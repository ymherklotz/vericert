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

Local Open Scope error_monad_scope.


Section TRANSLATE.
  Local Open Scope error_monad_scope.

  Definition transl_datapath_fun (a : Verilog.node * HTL.datapath_stmnt) :=
    let (n, s) := a in
    let node := Verilog.Vlit (posToValue n) in
    OK (node, s).

  Definition transl_datapath st := Errors.mmap transl_datapath_fun st.

  Definition transl_ctrl_fun (a : Verilog.node * HTL.control_stmnt) : Errors.res (Verilog.expr * Verilog.stmnt):=
    let (n, s) := a in
    let node := Verilog.Vlit (posToValue n) in
    Errors.OK (node, s).

  Definition transl_ctrl st := Errors.mmap transl_ctrl_fun st.

  Definition scl_to_Vdecl_fun (a : reg * (option Verilog.io * Verilog.scl_decl)) :=
    match a with (r, (io, Verilog.VScalar sz)) => (Verilog.Vdecl io r sz) end.

  Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

  Definition arr_to_Vdeclarr_fun (a : reg * (option Verilog.io * Verilog.arr_decl)) :=
    match a with (r, (io, Verilog.VArray sz l)) => (Verilog.Vdeclarr io r sz l) end.

  Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

  Definition called_functions (m : HTL.module) : list ident :=
    List.nodup Pos.eq_dec (List.map (Basics.compose fst snd) (PTree.elements (HTL.mod_externctrl m))).

  Definition find_module (program : HTL.program) (name : ident) : Errors.res HTL.module :=
    match option_map snd (find (fun named_module => Pos.eqb (fst named_module) name) program.(prog_defs)) with
    | Some (Gfun (Internal f)) => OK f
    | _ => Error (msg "Veriloggen: Could not find definition for called module")
    end.

  Definition max_reg_module (m : HTL.module) : positive :=
    fold_left Pos.max (
    [ HTL.mod_st m
    ; HTL.mod_stk m
    ; HTL.mod_finish m
    ; HTL.mod_return m
    ; HTL.mod_start m
    ; HTL.mod_reset m
    ; HTL.mod_clk m
    ] ++ HTL.mod_params m ++ map fst (PTree.elements (mod_scldecls m)) ++ map fst (PTree.elements (mod_arrdecls m))) 1%positive.

  Definition prog_modmap (p : HTL.program) :=
    PTree_Properties.of_list (Option.map_option
                            (fun a => match a with
                                   | (ident, (Gfun (Internal f))) => Some (ident, f)
                                   | _ => None
                                   end)
                            p.(prog_defs)).

  (** Clean up declarations for an inlined module. Make IO decls into reg, and remove the clk declaration *)
  Definition clean_up_decl (clk : reg) (it : Verilog.module_item) :=
    match it with
    | Vdeclaration (Vdecl (Some _) reg sz) =>
      if Pos.eqb reg clk
      then None
      else Some (Vdeclaration (Vdecl None reg sz))
    | Vdeclaration (Vdeclarr (Some _) reg sz len) =>
      Some (Vdeclaration (Vdeclarr None reg sz len))
    | _ => Some it
    end.

  (* FIXME Remove the fuel parameter (recursion limit)*)
  Fixpoint transf_module (fuel : nat) (program : HTL.program) (m : HTL.module) : res Verilog.module :=
    match fuel with
    | O => Error (msg "Veriloggen: transf_module recursion too deep")
    | S fuel' =>

      let inline_start_reg := max_reg_module m in
      let inline_names := called_functions m in
      let htl_modules := PTree.filter
                       (fun m _ => List.existsb (Pos.eqb m) inline_names)
                       (prog_modmap program) in
      do translated_modules <- PTree.traverse (fun _ => transf_module fuel' program) htl_modules;
      let cleaned_modules := PTree.map1 (map_body (Option.map_option (clean_up_decl (HTL.mod_clk m))))
                                        translated_modules in

      do case_el_ctrl <- transl_ctrl (PTree.elements (HTL.mod_controllogic m));
      do case_el_data <- transl_datapath (PTree.elements (HTL.mod_datapath m));

      let body : list Verilog.module_item:=
          Valways (Vposedge (HTL.mod_clk m)) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                                    (Vseq
                                                      (Vnonblock (Vvar (HTL.mod_st m)) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                                      (Vnonblock (Vvar (HTL.mod_finish m)) (Vlit (ZToValue 0))))
                                                    (Vcase (Vvar (HTL.mod_st m)) case_el_ctrl (Some Vskip)))
                  :: Valways (Vposedge (HTL.mod_clk m)) (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip))
                  :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements (HTL.mod_arrdecls m))
                                                           ++ scl_to_Vdecl (AssocMap.elements (HTL.mod_scldecls m)))
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
               (HTL.mod_entrypoint m)
                )
    end.

  Definition transl_fundef (prog : HTL.program) := transf_partial_fundef (transf_module 10 prog).
  Definition transl_program (prog : HTL.program) := transform_partial_program (transl_fundef prog) prog.

End TRANSLATE.
