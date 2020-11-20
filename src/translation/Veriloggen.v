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

Require Import List.
Import ListNotations.

From compcert Require Import Maps.
From compcert Require Errors.
From compcert Require Import AST.
From vericert Require Import Verilog HTL Vericertlib AssocMap ValueInt.

Definition transl_list_fun (a : node * Verilog.stmnt) :=
  let (n, stmnt) := a in
  (Vlit (posToValue n), stmnt).

Definition transl_list st := map transl_list_fun st.

Definition scl_to_Vdecl_fun (a : reg * scl_decl) :=
  match a with
  | (r, (VScalar io sz)) => (Vdecl io r sz)
  | (r, VWire sz) => (Vdeclwire r sz)
  end.

Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

Definition arr_to_Vdeclarr_fun (a : reg * (option io * arr_decl)) :=
  match a with (r, (io, VArray sz l)) => (Vdeclarr io r sz l) end.

Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

Definition inst_to_Vdecl_fun (m: HTL.module) (a: positive * HTL.instantiation) :=
  match a with (_, HTLinstantiation mod_name inst_name args fin dst) =>
               (Vinstancedecl mod_name inst_name ([mod_start m; mod_reset m; mod_clk m] ++ args ++ [dst;fin])) end.

Definition inst_to_Vdecl (m: HTL.module) := map (inst_to_Vdecl_fun m).

Definition transl_module (m : HTL.module) : Verilog.module :=
  let case_el_ctrl := transl_list (PTree.elements m.(mod_controllogic)) in
  let case_el_data := transl_list (PTree.elements m.(mod_datapath)) in
  let body :=
      Valways (Vposedge m.(mod_clk)) (Vcond (Vbinop Veq (Vvar m.(mod_reset)) (Vlit (ZToValue 1)))
                                               (Vnonblock (Vvar m.(mod_st)) (Vlit (posToValue m.(mod_entrypoint))))
                                               (Vcase (Vvar m.(mod_st)) case_el_ctrl (Some Vskip)))
      :: Valways (Vposedge m.(mod_clk)) (Vcase (Vvar m.(mod_st)) case_el_data (Some Vskip))
      :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements m.(mod_arrdecls))
                                               ++ scl_to_Vdecl (AssocMap.elements m.(mod_scldecls))
                                               ++ inst_to_Vdecl m (AssocMap.elements m.(mod_insts))) in
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
