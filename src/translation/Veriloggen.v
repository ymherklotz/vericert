(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
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

From compcert Require Import Maps.
From compcert Require Errors.
From compcert Require Import AST.
From vericert Require Import Verilog HTL Vericertlib AssocMap ValueInt.

Definition transl_datapath_fun (a : node * HTL.datapath_stmnt) :=
  let (n, s) := a in
  (Vlit (posToValue n),
   match s with
   | HTLcall m args dst => Vskip
   | HTLVstmnt s => s
   end).


Definition transl_datapath st := map transl_datapath_fun st.

Definition transl_ctrl_fun (a : node * Verilog.stmnt) :=
  let (n, stmnt) := a
  in (Vlit (posToValue n), stmnt).

Definition transl_ctrl st := map transl_ctrl_fun st.

Definition scl_to_Vdecl_fun (a : reg * (option io * scl_decl)) :=
  match a with (r, (io, VScalar sz)) => (Vdecl io r sz) end.

Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

Definition arr_to_Vdeclarr_fun (a : reg * (option io * arr_decl)) :=
  match a with (r, (io, VArray sz l)) => (Vdeclarr io r sz l) end.

Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

Definition transl_module (m : HTL.module) : Verilog.module :=
  let case_el_ctrl := transl_ctrl (PTree.elements m.(mod_controllogic)) in
  let case_el_data := transl_datapath (PTree.elements m.(mod_datapath)) in
  let body :=
      Valways (Vposedge m.(mod_clk)) (Vcond (Vbinop Veq (Vvar m.(mod_reset)) (Vlit (ZToValue 1)))
                                               (Vnonblock (Vvar m.(mod_st)) (Vlit (posToValue m.(mod_entrypoint))))
                                               (Vcase (Vvar m.(mod_st)) case_el_ctrl (Some Vskip)))
      :: Valways (Vposedge m.(mod_clk)) (Vcase (Vvar m.(mod_st)) case_el_data (Some Vskip))
      :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements m.(mod_arrdecls))
                          ++ scl_to_Vdecl (AssocMap.elements m.(mod_scldecls))) in
  Verilog.mkmodule m.(mod_start)
                   m.(mod_reset)
                   m.(mod_clk)
                   m.(mod_finish)
                   m.(mod_return)
                   m.(mod_st)
                   m.(mod_stk)
                   m.(mod_stk_len)
                   m.(mod_params)
                   body
                   m.(mod_entrypoint).

Definition transl_fundef := transf_fundef transl_module.

Definition transl_program (p: HTL.program) : Verilog.program :=
  transform_program transl_fundef p.
