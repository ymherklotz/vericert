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

Require Import compcert.common.AST.
Require compcert.common.Errors.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.HTL.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.

Definition transl_list_fun (a : node * Verilog.stmnt) :=
  let (n, stmnt) := a in
  (Vlit (posToValue n), stmnt).

Definition transl_list st := map transl_list_fun st.

Definition scl_to_Vdecl_fun (a : reg * (option io * scl_decl)) :=
  match a with (r, (io, VScalar sz)) => (Vdecl io r sz) end.

Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

Definition arr_to_Vdeclarr_fun (a : reg * (option io * arr_decl)) :=
  match a with (r, (io, VArray sz l)) => (Vdeclarr io r sz l) end.

Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

Definition inst_ram clk ram :=
  Valways (Vnegedge clk)
          (Vcond (Vvar (ram_en ram))
                 (Vcond (Vvar (ram_wr_en ram))
                        (Vnonblock (Vvari (ram_mem ram) (Vvar (ram_addr ram)))
                                   (Vvar (ram_d_in ram)))
                        (Vnonblock (Vvar (ram_d_out ram))
                                   (Vvari (ram_mem ram) (Vvar (ram_addr ram)))))
                 Vskip).

Definition transl_module (m : HTL.module) : Verilog.module :=
  let case_el_ctrl := list_to_stmnt (transl_list (PTree.elements m.(mod_controllogic))) in
  let case_el_data := list_to_stmnt (transl_list (PTree.elements m.(mod_datapath))) in
  match m.(HTL.mod_ram) with
  | Some ram =>
    let body :=
        Valways (Vposedge m.(HTL.mod_clk)) (Vcond (Vbinop Veq (Vvar m.(HTL.mod_reset)) (Vlit (ZToValue 1)))
                                                  (Vnonblock (Vvar m.(HTL.mod_st)) (Vlit (posToValue m.(HTL.mod_entrypoint))))
                                                  (Vcase (Vvar m.(HTL.mod_st)) case_el_ctrl (Some Vskip)))
                :: Valways (Vposedge m.(HTL.mod_clk)) (Vcase (Vvar m.(HTL.mod_st)) case_el_data (Some Vskip))
                :: inst_ram m.(HTL.mod_clk) ram
                :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements m.(mod_arrdecls))
                                                          ++ scl_to_Vdecl (AssocMap.elements m.(mod_scldecls))) in
    Verilog.mkmodule m.(HTL.mod_start)
                     m.(HTL.mod_reset)
                     m.(HTL.mod_clk)
                     m.(HTL.mod_finish)
                     m.(HTL.mod_return)
                     m.(HTL.mod_st)
                     m.(HTL.mod_stk)
                     m.(HTL.mod_stk_len)
                     m.(HTL.mod_params)
                     body
                     m.(HTL.mod_entrypoint)
  | None =>
    let body :=
        Valways (Vposedge m.(HTL.mod_clk)) (Vcond (Vbinop Veq (Vvar m.(HTL.mod_reset)) (Vlit (ZToValue 1)))
                                                  (Vnonblock (Vvar m.(HTL.mod_st)) (Vlit (posToValue m.(HTL.mod_entrypoint))))
                                                  (Vcase (Vvar m.(HTL.mod_st)) case_el_ctrl (Some Vskip)))
                :: Valways (Vposedge m.(HTL.mod_clk)) (Vcase (Vvar m.(HTL.mod_st)) case_el_data (Some Vskip))
                :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements m.(mod_arrdecls))
                                                          ++ scl_to_Vdecl (AssocMap.elements m.(mod_scldecls))) in
    Verilog.mkmodule m.(HTL.mod_start)
                     m.(HTL.mod_reset)
                     m.(HTL.mod_clk)
                     m.(HTL.mod_finish)
                     m.(HTL.mod_return)
                     m.(HTL.mod_st)
                     m.(HTL.mod_stk)
                     m.(HTL.mod_stk_len)
                     m.(HTL.mod_params)
                     body
                     m.(HTL.mod_entrypoint)
  end.

Definition transl_fundef := transf_fundef transl_module.

Definition transl_program (p: HTL.program) : Verilog.program :=
  transform_program transl_fundef p.
