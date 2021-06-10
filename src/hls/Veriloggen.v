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

  Definition called_functions (main_name : ident) (m : HTL.module) : list ident :=
    (* remove duplicates *)
    List.nodup Pos.eq_dec
               (* Take just the module name *)
               (List.map (Basics.compose fst snd)
                         (* Remove the main module if it's referenced *)
                         (List.filter (fun it => negb (Pos.eqb (fst (snd it)) main_name))
                                      (PTree.elements (HTL.mod_externctrl m)))).

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

  (* FIXME Remove the fuel parameter (recursion limit)*)
  Fixpoint transl_module (fuel : nat) (prog : HTL.program) (externclk : option reg) (m : HTL.module) : res Verilog.module :=
    match fuel with
    | O => Error (msg "Veriloggen: transl_module recursion too deep")
    | S fuel' =>
      let clk := match externclk with
                 | None => HTL.mod_clk m
                 | Some c => c
                 end in

      let inline_names := called_functions (AST.prog_main prog) m in
      let modmap := prog_modmap prog in
      let htl_modules := PTree.filter
                       (fun m _ => List.existsb (Pos.eqb m) inline_names)
                       modmap in
      do translated_modules <- PTree.traverse (fun _ => transl_module fuel' prog (Some clk)) htl_modules;
      let cleaned_modules := PTree.map1 (map_body (Option.map_option (clean_up_decl clk)))
                                        translated_modules in


      let case_el_ctrl := transl_states (PTree.elements (HTL.mod_controllogic m)) in
      let case_el_data := transl_states (PTree.elements (HTL.mod_datapath m)) in

      let externctrl := HTL.mod_externctrl m in

      (* Only declare the clock if this is the top-level module, i.e. there is no inherited clock *)
      let maybe_clk_decl := match externclk with
                            | None => scl_to_Vdecls [(clk, (Some Vinput, VScalar 1))]
                            | Some _ => []
                            end in

      let local_arrdecls := PTree.filter (fun r _ => negb (PTree.contains r externctrl)) (HTL.mod_arrdecls m) in
      let arr_decls := arr_to_Vdeclarrs (AssocMap.elements local_arrdecls) in

      let local_scldecls := PTree.filter (fun r _ => negb (PTree.contains r externctrl)) (HTL.mod_scldecls m) in
      let scl_decls := scl_to_Vdecls (AssocMap.elements local_scldecls) in

      let body : list Verilog.module_item:=
          Valways (Vposedge clk) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                                    (Vseq
                                                      (Vnonblock (Vvar (HTL.mod_st m)) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                                      (Vnonblock (Vvar (HTL.mod_finish m)) (Vlit (ZToValue 0))))
                                                    (Vcase (Vvar (HTL.mod_st m)) case_el_ctrl (Some Vskip)))
                  :: Valways (Vposedge clk) (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip))
                  :: arr_decls
                  ++ scl_decls
                  ++ maybe_clk_decl
                  ++ List.flat_map Verilog.mod_body (List.map snd (PTree.elements cleaned_modules)) in

      OK (Verilog.mkmodule
               (HTL.mod_start m)
               (HTL.mod_reset m)
               (HTL.mod_clk m)
               (HTL.mod_finish m)
               (HTL.mod_return m)
               (HTL.mod_st m)
               (HTL.mod_stk m)
               (HTL.mod_stk_len m)
               (HTL.mod_params m)
               body
               (HTL.mod_entrypoint m))
    end.

  Definition transl_fundef (prog : HTL.program) := transf_partial_fundef (transl_module 10 prog None).
  Definition transl_program (prog : HTL.program) := transform_partial_program (transl_fundef prog) prog.

End TRANSLATE.
