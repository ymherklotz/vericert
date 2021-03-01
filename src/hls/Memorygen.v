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
        (Vnonblock (Vvar addr) e1)), Some (LSload e1))
  | s => (s, None)
  end.

Definition transf_maps (st addr d_in d_out wr: reg)
           (dc: PTree.t stmnt * PTree.t stmnt) i :=
  let (d, c) := dc in
  match PTree.get i d, PTree.get i c with
  | Some d_s, Some c_s =>
    match transf_stmnt_store addr d_in d_out wr d_s with
    | (ns, Some LSstore) =>
      (PTree.set i ns d, c)
    | (ns, Some (LSload e)) =>
      (PTree.set i ns
                 (PTree.set 1000 (Vnonblock e (Vvar d_out)) d),
       PTree.set i (Vnonblock (Vvar st) (Vlit (ZToValue 1000%Z)))
                 (PTree.set 1000 c_s c))
    | (_, _) => (d, c)
    end
  | _, _ => (d, c)
  end.

Lemma is_wf:
  forall A nc nd,
  @map_well_formed A nc /\ @map_well_formed A nd.
Admitted.

Definition transf_module (m: module): module :=
  let (nd, nc) := fold_left (transf_maps m.(mod_st) 1 2 3 4)
                            (map fst (PTree.elements m.(mod_datapath)))
                            (m.(mod_datapath), m.(mod_controllogic))
  in
  mkmodule m.(mod_params)
           nd
           nc
           m.(mod_entrypoint)
           m.(mod_st)
           m.(mod_stk)
           m.(mod_stk_len)
           m.(mod_finish)
           m.(mod_return)
           m.(mod_start)
           m.(mod_reset)
           m.(mod_clk)
           m.(mod_scldecls)
           m.(mod_arrdecls)
           (is_wf _ nc nd).

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : program) :=
  transform_program transf_fundef p.
