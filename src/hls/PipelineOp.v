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

Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.FunctionalUnits.

Definition state : Type := code * funct_units.

Definition div_pos (il: nat * list nat) x :=
  let (i, l) := il in
  match x with
  | RBop _ Odiv _ _ => (S i, i :: l)
  | RBop _ Odivu _ _ => (S i, i :: l)
  | RBop _ Omod _ _ => (S i, i :: l)
  | RBop _ Omodu _ _ => (S i, i :: l)
  | _ => (S i, l)
  end.

Definition find_divs (bb: bblock) : list nat :=
  snd (List.fold_left div_pos bb.(bb_body) (1%nat, nil)).

Definition transf_code (i: state) (bbn: node * bblock) : state :=
  let (c, fu) := i in
  let (n, bb) := bbn in
  (PTree.set n bb c, fu).

Definition transf_function (f: function) : function :=
  let (c, fu) := List.fold_left transf_code
                                (PTree.elements f.(fn_code))
                                (PTree.empty bblock, f.(fn_funct_units)) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    c
    fu
    f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
