(*
 * CoqUp: Verified high-level synthesis.
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
From coqup Require Import Verilog HTL Coquplib AssocMap Value.

Fixpoint transl_list (st : list (node * Verilog.stmnt)) {struct st} : list (expr * Verilog.stmnt) :=
  match st with
  | (n, stmt) :: ls => (Vlit (posToValue 32 n), stmt) :: transl_list ls
  | nil => nil
  end.

Fixpoint scl_to_Vdecl (scldecl : list (reg * (option io * scl_decl))) {struct scldecl} : list module_item :=
  match scldecl with
  | (r, (io, Scalar sz))::scldecl' => Vdeclaration (Vdecl io r sz) :: scl_to_Vdecl scldecl'
  | nil => nil
  end.

Fixpoint arr_to_Vdeclarr (arrdecl : list (reg * (option io * arr_decl))) {struct arrdecl} : list module_item :=
  match arrdecl with
  | (r, (io, Array sz l))::arrdecl' => Vdeclaration (Vdeclarr io r sz l) :: arr_to_Vdeclarr arrdecl'
  | nil => nil
  end.

Definition transl_module (m : HTL.module) : Verilog.module :=
  let case_el_ctrl := transl_list (PTree.elements m.(mod_controllogic)) in
  let case_el_data := transl_list (PTree.elements m.(mod_datapath)) in
  let body :=
      Valways (Vposedge m.(mod_clk)) (Vcase (Vvar m.(mod_st)) case_el_data (Some Vskip))
      :: Valways (Vposedge m.(mod_clk)) (Vcond (Vbinop Veq (Vvar m.(mod_reset)) (ZToValue 1 1))
                                               (Vnonblock (Vvar m.(mod_st)) (posToValue 32 m.(mod_entrypoint)))
                                               (Vcase (Vvar m.(mod_st)) case_el_ctrl (Some Vskip)))
      :: (arr_to_Vdeclarr (AssocMap.elements m.(mod_arrdecls))
                          ++ scl_to_Vdecl (AssocMap.elements m.(mod_scldecls))) in
  Verilog.mkmodule m.(mod_start)
                   m.(mod_reset)
                   m.(mod_clk)
                   m.(mod_finish)
                   m.(mod_return)
                   m.(mod_st)
                   m.(mod_stk)
                   m.(mod_params)
                   body
                   m.(mod_entrypoint).

Definition transl_fundef := transf_fundef transl_module.

Definition transl_program (p: HTL.program) : Verilog.program :=
  transform_program transl_fundef p.
