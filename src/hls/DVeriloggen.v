(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <yann@yannherklotz.com>
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
Require Import vericert.hls.DHTL.
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

Definition declare_all (start reset clk finish ret st stk: reg) (stk_len: nat) (body: list module_item) :=
  Vdeclaration (Vdecl (Some Vinput) start 1)
  :: Vdeclaration (Vdecl (Some Vinput) reset 1)
  :: Vdeclaration (Vdecl (Some Vinput) clk 1)
  :: Vdeclaration (Vdecl (Some Voutput) finish 1)
  :: Vdeclaration (Vdecl (Some Voutput) ret 32)
  :: Vdeclaration (Vdecl None st 32)
  :: Vdeclaration (Vdeclarr None stk 32 stk_len)
  :: (all_reg_declarations (start::reset::clk::finish::ret::st::stk::nil) body).

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

Definition transl_module (m : DHTL.module) : Verilog.module :=
  let case_el_data := list_to_stmnt (transl_list (PTree.elements m.(mod_datapath))) in
  (* let nstate := (max_reg_module m + 1)%positive in *)
  match m.(DHTL.mod_ram) with
  | Some ram =>
    let body :=
       Valways (Vposedge m.(DHTL.mod_clk)) (Vcond (Vbinop Veq (Vvar m.(DHTL.mod_reset)) (Vlit (ZToValue 1)))
                                                  (Vnonblock (Vvar m.(DHTL.mod_st)) (Vlit (posToValue m.(DHTL.mod_entrypoint))))
(Vcase (Vvar (DHTL.mod_st m)) case_el_data (Some Vskip)))
        (*         :: Valways (Vposedge m.(DHTL.mod_clk)) (Vcond (Vbinop Veq (Vvar m.(DHTL.mod_reset)) (Vlit (ZToValue 1))) *)
        (* (Vnonblock (Vvar (DHTL.mod_st m)) (Vlit (posToValue m.(DHTL.mod_entrypoint)))) (Vnonblock (Vvar (DHTL.mod_st m)) (Vvar m.(DHTL.mod_st)))) *)
                :: inst_ram m.(DHTL.mod_clk) ram
                :: nil in
    Verilog.mkmodule m.(DHTL.mod_start)
                     m.(DHTL.mod_reset)
                     m.(DHTL.mod_clk)
                     m.(DHTL.mod_finish)
                     m.(DHTL.mod_return)
                     m.(DHTL.mod_st)
                     m.(DHTL.mod_stk)
                     m.(DHTL.mod_stk_len)
                     m.(DHTL.mod_params)
                     (body ++ declare_all m.(DHTL.mod_start)
                     m.(DHTL.mod_reset)
                     m.(DHTL.mod_clk)
                     m.(DHTL.mod_finish)
                     m.(DHTL.mod_return)
                     m.(DHTL.mod_st)
                     m.(DHTL.mod_stk)
                     m.(DHTL.mod_stk_len) body)
                     m.(DHTL.mod_entrypoint)
  | None =>
    let body :=
        Valways (Vposedge m.(DHTL.mod_clk)) (Vcond (Vbinop Veq (Vvar m.(DHTL.mod_reset)) (Vlit (ZToValue 1)))
                                                  (Vnonblock (Vvar m.(DHTL.mod_st)) (Vlit (posToValue m.(DHTL.mod_entrypoint))))
(Vcase (Vvar (DHTL.mod_st m)) case_el_data (Some Vskip)))
                (* :: Valways (Vposedge m.(DHTL.mod_clk)) (Vcond (Vbinop Veq (Vvar m.(DHTL.mod_reset)) (Vlit (ZToValue 1))) *)
        (* (Vnonblock (Vvar (DHTL.mod_st m)) (Vlit (posToValue m.(DHTL.mod_entrypoint)))) *)
        (* (Vnonblock (Vvar (DHTL.mod_st m)) (Vvar m.(DHTL.mod_st)))) *)
        :: nil in
    Verilog.mkmodule m.(DHTL.mod_start)
                     m.(DHTL.mod_reset)
                     m.(DHTL.mod_clk)
                     m.(DHTL.mod_finish)
                     m.(DHTL.mod_return)
                     m.(DHTL.mod_st)
                     m.(DHTL.mod_stk)
                     m.(DHTL.mod_stk_len)
                     m.(DHTL.mod_params)
                     (body ++ declare_all m.(DHTL.mod_start)
                     m.(DHTL.mod_reset)
                     m.(DHTL.mod_clk)
                     m.(DHTL.mod_finish)
                     m.(DHTL.mod_return)
                     m.(DHTL.mod_st)
                     m.(DHTL.mod_stk)
                     m.(DHTL.mod_stk_len) body)
                     m.(DHTL.mod_entrypoint)
  end.

Definition transl_fundef := transf_fundef transl_module.

Definition transl_program (p: DHTL.program) : Verilog.program :=
  transform_program transl_fundef p.
