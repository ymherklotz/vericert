(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
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

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.Predicate.

(*|
=====================
Reverse If-Conversion
=====================

This transformation takes a scheduling RTLPar block and removes any predicates
from it.  It can then be trivially transformed into linear code again.  It works
by iteratively selecting a predicate, then creating a branch based on it and
placing subsequent instructions in one branch or the other.
|*)

Fixpoint existsb_val {A B} (f: A -> option B) (l : list A) : option B :=
  match l with
  | nil => None
  | a :: l0 =>
      match f a, existsb_val f l0 with
      | _, Some v => Some v
      | Some v, _ => Some v
      | _, _ => None
      end
  end.

Definition includes_setpred (bb: list (list instr)) :=
  existsb_val (existsb_val (fun x => match x with RBsetpred a _ _ _ => Some a | _ => None end)) bb.

Definition add_bb (should_split: bool) (i: list (list instr))
           (bbc: list (list (list instr)) * list (list (list instr))) :=
  match bbc with
  | (a, b) => if should_split then (a, i::b) else (i::a, b)
  end.

Fixpoint first_split (saw_pred: bool) (bb: bb) :=
  match bb with
  | a :: b =>
      match includes_setpred a with
      | Some v =>
          let (_, res) := first_split true b in
          (Some v, add_bb saw_pred a res)
      | _ =>
          let (v, res) := first_split saw_pred b in
          (v, add_bb saw_pred a res)
      end
  | nil => (None, (nil, nil))
  end.

Definition split_bb (fresh: node) (b: bb) : bb * bb * bb :=
  match first_split false b with
  | (Some p, (bb1, bb2)) => (bb1 ++ bb2, nil, nil)
  | (None, (bb1, bb2)) => (bb1 ++ bb2, nil, nil)
  end.

Definition transf_function (f: function) : function := f.

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
