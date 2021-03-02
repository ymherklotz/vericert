(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.HTL.
Require Import vericert.hls.AssocMap.

Local Open Scope positive.

Inductive load_store :=
| LSload : expr -> load_store
| LSstore : load_store.

Definition transf_stmnt_store (addr d_in d_out wr: reg) s :=
  match s with
  | Vnonblock (Vvari r e1) e2 =>
    ((Vseq
        (Vnonblock (Vvar wr) (Vlit (ZToValue 1)))
        (Vseq (Vnonblock (Vvar d_in) e2)
              (Vnonblock (Vvar addr) e1))), Some LSstore)
  | Vnonblock e1 (Vvari r e2) =>
    ((Vseq
        (Vnonblock (Vvar wr) (Vlit (ZToValue 0)))
        (Vnonblock (Vvar addr) e2)), Some (LSload e1))
  | s => (s, None)
  end.

Definition max_pc_function (m: module) :=
  List.fold_left Pos.max (List.map fst (PTree.elements m.(mod_controllogic))) 1.

Definition transf_maps (st addr d_in d_out wr: reg)
           (dc: node * PTree.t stmnt * PTree.t stmnt) i :=
  match dc with
  | (n, d, c) =>
    match PTree.get i d, PTree.get i c with
    | Some d_s, Some c_s =>
      match transf_stmnt_store addr d_in d_out wr d_s with
      | (ns, Some LSstore) =>
        (n, PTree.set i ns d, c)
      | (ns, Some (LSload e)) =>
        (n+1, PTree.set i ns
                   (PTree.set n (Vnonblock e (Vvar d_out)) d),
         PTree.set i (Vnonblock (Vvar st) (Vlit (posToValue n)))
                   (PTree.set n c_s c))
      | (_, _) => dc
      end
    | _, _ => dc
    end
  end.

Lemma is_wf:
  forall A nc nd,
  @map_well_formed A nc /\ @map_well_formed A nd.
Admitted.

Definition transf_module (m: module): module :=
  let addr := m.(mod_clk)+1 in
  let d_in := m.(mod_clk)+2 in
  let d_out := m.(mod_clk)+3 in
  let wr_en := m.(mod_clk)+4 in
  match fold_left (transf_maps m.(mod_st) addr d_in d_out wr_en)
                  (map fst (PTree.elements m.(mod_datapath)))
                  (max_pc_function m + 1, m.(mod_datapath), m.(mod_controllogic))
  with
  | (_, nd, nc) =>
    mkmodule m.(mod_params)
             nd
             nc
             m.(mod_entrypoint)
             m.(mod_st)
             m.(mod_stk)
             (2 ^ Nat.log2_up m.(mod_stk_len))%nat
             m.(mod_finish)
             m.(mod_return)
             m.(mod_start)
             m.(mod_reset)
             m.(mod_clk)
             (AssocMap.set wr_en (None, VScalar 32)
              (AssocMap.set d_out (None, VScalar 32)
               (AssocMap.set d_in (None, VScalar 32)
                (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))
             (AssocMap.set m.(mod_stk) (None, VArray 32 (2 ^ Nat.log2_up m.(mod_stk_len)))%nat m.(mod_arrdecls))
             (Some (addr, d_in, d_out, wr_en))
             (is_wf _ nc nd)
  end.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : program) :=
  transform_program transf_fundef p.
