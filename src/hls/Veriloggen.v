(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *               2021 Michalis Pardalos <mpardalos@gmail.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

Require Import compcert.common.AST.
Require Import compcert.common.Errors.

Require Import vericert.common.Maps.
Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.HTL.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Import ListNotations.

Section TRANSLATE.
  Local Open Scope error_monad_scope.

  Definition transl_states : list (HTL.node * HTL.datapath_stmnt) -> list (Verilog.expr * Verilog.stmnt) :=
    map (fun '(n, s) => (Verilog.Vlit (posToValue n), s)).

  Definition scl_to_Vdecls :=
    map (fun '(r, (io, Verilog.VScalar sz)) => Vdeclaration (Vdecl io r sz)).

  Definition arr_to_Vdeclarrs :=
    map (fun '(r, (io, Verilog.VArray sz l)) => Vdeclaration (Vdeclarr io r sz l)).

  (** Clean up declarations for an inlined module. Make IO decls into reg, and remove the clk declaration *)
  Definition clean_up_decl (clk : reg) (it : Verilog.module_item) :=
    match it with
    | Vdeclaration (Vdecl _ reg sz) =>
      if Pos.eqb reg clk
      then None
      else Some (Vdeclaration (Vdecl None reg sz))
    | Vdeclaration (Vdeclarr (Some _) reg sz len) =>
      Some (Vdeclaration (Vdeclarr None reg sz len))
    | _ => Some it
    end.

  Definition inst_ram clk ram :=
    Valways (Vnegedge clk)
            (Vcond (Vbinop Vne (Vvar (ram_u_en ram)) (Vvar (ram_en ram)))
                   (Vseq (Vcond (Vvar (ram_wr_en ram))
                                (Vnonblock (Vvari (ram_mem ram) (Vvar (ram_addr ram)))
                                           (Vvar (ram_d_in ram)))
                                (Vnonblock (Vvar (ram_d_out ram))
                                           (Vvari (ram_mem ram) (Vvar (ram_addr ram)))))
                         (Vnonblock (Vvar (ram_en ram)) (Vvar (ram_u_en ram))))
                   Vskip).

  Definition transl_module (externclk : option reg) (m : HTL.module) : Verilog.module :=
    let clk := match externclk with
               | None => HTL.mod_clk m
               | Some c => c
               end in

    let case_el_ctrl := list_to_stmnt (transl_states (PTree.elements (HTL.mod_controllogic m))) in
    let case_el_data := list_to_stmnt (transl_states (PTree.elements (HTL.mod_datapath m))) in

    let externctrl := HTL.mod_externctrl m in

    let local_arrdecls := PTree.filter (fun r _ => negb (PTree.contains r externctrl)) (HTL.mod_arrdecls m) in
    let arr_decls := arr_to_Vdeclarrs (AssocMap.elements local_arrdecls) in

    let local_scldecls := PTree.filter (fun r _ => negb (PTree.contains r externctrl)) (HTL.mod_scldecls m) in
    let scl_decls := scl_to_Vdecls (AssocMap.elements local_scldecls) in

    let body : list Verilog.module_item :=
        match (HTL.mod_ram m) with
        | Some ram =>
            Valways (Vposedge clk) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                          (Vnonblock (Vvar (HTL.mod_st m)) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                          (Vcase (Vvar (HTL.mod_st m)) case_el_ctrl (Some Vskip)))
                    :: Valways (Vposedge clk) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                                     (Vnonblock (Vvar (HTL.mod_finish m)) (Vlit (ZToValue 0)))
                                                     (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip)))
                    :: inst_ram clk ram
                    :: arr_decls
                    ++ scl_decls
        | Nothing =>
            Valways (Vposedge clk) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                          (Vnonblock (Vvar (HTL.mod_st m)) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                          (Vcase (Vvar (HTL.mod_st m)) case_el_ctrl (Some Vskip)))
                    :: Valways (Vposedge clk) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                                     (Vnonblock (Vvar (HTL.mod_finish m)) (Vlit (ZToValue 0)))
                                                     (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip)))
                    :: arr_decls
                    ++ scl_decls
        end
    in

    Verilog.mkmodule
      (HTL.mod_start m)
      (HTL.mod_reset m)
      clk
      (HTL.mod_finish m)
      (HTL.mod_return m)
      (HTL.mod_st m)
      (HTL.mod_stk m)
      (HTL.mod_stk_len m)
      (HTL.mod_params m)
      body
      (HTL.mod_entrypoint m).

    (*   let htl_modules := PTree.filter *)
    (*                    (fun m _ => List.existsb (Pos.eqb m) inline_names) *)
    (*                    modmap in *)
    (*   do translated_modules <- PTree.traverse (fun _ => transl_module fuel' prog (Some clk)) htl_modules; *)
    (*   let cleaned_modules := PTree.map1 (map_body (Option.map_option (clean_up_decl clk))) *)
    (*                                     translated_modules in *)

    (*                 ++ List.flat_map Verilog.mod_body (List.map snd (PTree.elements cleaned_modules)) *)

  (* FIXME Remove the fuel parameter (recursion limit)*)
  Fixpoint referenced_module_names (fuel : nat) (prog : HTL.program) (m : HTL.module) : res (list ident) :=
    match fuel with
    | O => Error (msg "Veriloggen: recursion too deep")
    | S fuel' =>
      let modmap := prog_modmap prog in
      let directly_referenced_names : list ident :=
                     (* Take just the module name *)
                     (List.map (fun '(_, (othermod_name, _)) => othermod_name)
                               (PTree.elements (HTL.mod_externctrl m))) in
      do indirectly_referenced_namess <-
         mmap (fun '(_, m) => referenced_module_names fuel' prog m)
                  (List.filter (fun '(n, m) => in_dec Pos.eq_dec n directly_referenced_names)
                               (PTree.elements modmap));

      let indirectly_referenced_names := List.concat indirectly_referenced_namess in
      OK (List.nodup Pos.eq_dec (directly_referenced_names ++ indirectly_referenced_names))
    end.

  Definition transl_top_module (prog : HTL.program) (m : HTL.module) : res Verilog.module :=
    let tm := transl_module None m in

    let modmap := prog_modmap prog in
    do referenced_names <- referenced_module_names 100 prog m;
    do referenced_modules <- mmap (fun n => match modmap!n with
                                         | Some m => OK m
                                         | None => Error (msg "Veriloggen: Could not find module")
                                         end) referenced_names;
    let translated_modules := List.map (transl_module (Some (mod_clk tm))) referenced_modules in
    let cleaned_modules := List.map (map_body (Option.map_option (clean_up_decl (mod_clk tm)))) translated_modules in
    let referenced_module_bodies := List.flat_map Verilog.mod_body cleaned_modules in

    OK (map_body (app referenced_module_bodies) tm).

  Definition transl_fundef (prog : HTL.program) := transf_partial_fundef (transl_top_module prog).
  Definition transl_program (prog : HTL.program) := transform_partial_program (transl_fundef prog) prog.

End TRANSLATE.
