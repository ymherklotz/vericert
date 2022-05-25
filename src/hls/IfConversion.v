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

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.Predicate.
Require Import vericert.bourdoncle.Bourdoncle.

Parameter build_bourdoncle : function -> (bourdoncle * PMap.t N).

(*|
=============
If-Conversion
=============

This conversion is a verified conversion from RTLBlock back to itself, which
performs if-conversion on basic blocks to make basic blocks larger.
|*)

Definition combine_pred (p: pred_op) (optp: option pred_op) :=
  match optp with
  | Some p' => Pand p p'
  | None => p
  end.

Definition map_if_convert (p: pred_op) (i: instr) :=
  match i with
  | RBop p' op args dst => RBop (Some (combine_pred p p')) op args dst
  | RBload p' chunk addr args dst =>
    RBload (Some (combine_pred p p')) chunk addr args dst
  | RBstore p' chunk addr args src =>
    RBstore (Some (combine_pred p p')) chunk addr args src
  | _ => i
  end.

Definition if_convert_block (c: code) (p: predicate) (bb: bblock) : bblock :=
  let cfi := bb_exit bb in
  match cfi with
  | RBcond cond args n1 n2 =>
    match PTree.get n1 c, PTree.get n2 c with
    | Some bb1, Some bb2 =>
      let bb1' := List.map (map_if_convert (Plit (true, p))) bb1.(bb_body) in
      let bb2' := List.map (map_if_convert (Plit (false, p))) bb2.(bb_body) in
      mk_bblock (List.concat (bb.(bb_body) :: ((RBsetpred None cond args p) :: bb1') :: bb2' :: nil))
                (RBpred_cf (Plit (true, p)) bb1.(bb_exit) bb2.(bb_exit))
    | _, _ => bb
    end
  | _ => bb
  end.

Definition is_cond_cfi (cfi: cf_instr) :=
  match cfi with
  | RBcond _ _ _ _ => true
  | _ => false
  end.

Fixpoint any {A: Type} (f: A -> bool) (a: list A) :=
  match a with
  | x :: xs => f x || any f xs
  | nil => false
  end.

Fixpoint all {A: Type} (f: A -> bool) (a: list A) :=
  match a with
  | x :: xs => f x && all f xs
  | nil => true
  end.

Definition find_backedge (nb: node * bblock) :=
  let (n, b) := nb in
  let succs := successors_instr b.(bb_exit) in
  filter (fun x => Pos.ltb n x) succs.

Definition find_all_backedges (c: code) : list node :=
  List.concat (List.map find_backedge (PTree.elements c)).

Definition has_backedge (entry: node) (be: list node) :=
  any (fun x => Pos.eqb entry x) be.

Fixpoint get_loops (b: bourdoncle): list node :=
  match b with
  | L h b' => h::(fold_right (fun a b => get_loops a ++ b) nil b')
  | I h => nil
  end.

Definition is_loop (b: list node) (n: node) :=
  any (Pos.eqb n) b.

Definition is_flat_cfi (n: cf_instr) :=
  match n with
  | RBcond _ _ _ _ => false
  | RBjumptable _ _ => false
  | RBpred_cf _ _ _ => false
  | _ => true
  end.

Definition is_flat (c: code) (succ: node) :=
  match c ! succ with
  | Some bblock => is_flat_cfi bblock.(bb_exit)
  | None => false
  end.

Definition find_blocks_with_cond ep (b: list node) (c: code) : list (node * bblock) :=
  let backedges := find_all_backedges c in
  List.filter (fun x => is_cond_cfi (snd x).(bb_exit) &&
                        (negb (is_loop b (fst x)) || Pos.eqb (fst x) ep) &&
                        all (fun x' => is_flat c x')
                            (successors_instr (snd x).(bb_exit))
              ) (PTree.elements c).

Definition if_convert_code (p: nat * code) (nb: node * bblock) :=
  let nbb := if_convert_block (snd p) (Pos.of_nat (fst p)) (snd nb) in
  (S (fst p), PTree.set (fst nb) nbb (snd p)).

Definition transf_function (f: function) : function :=
  let (b, _) := build_bourdoncle f in
  let b' := get_loops b in
  let (_, c) := List.fold_left if_convert_code
                               (find_blocks_with_cond f.(fn_entrypoint) b' f.(fn_code))
                               (1%nat, f.(fn_code)) in
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize) c f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
