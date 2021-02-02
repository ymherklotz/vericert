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

(*|
=============
If conversion
=============

This conversion is a verified conversion from RTLBlock back to itself, which performs if-conversion
on basic blocks to make basic blocks larger.
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

Definition if_convert_block (c: code) (p: pred_op) (bb: bblock) : bblock :=
  let cfi := bb_exit bb in
  match cfi with
  | RBcond cond args n1 n2 =>
    match PTree.get n1 c, PTree.get n2 c with
    | Some bb1, Some bb2 =>
      let bb1' := List.map (map_if_convert p) bb1.(bb_body) in
      let bb2' := List.map (map_if_convert (Pnot p)) bb2.(bb_body) in
      mk_bblock (List.concat (bb.(bb_body) :: bb1' :: bb2' :: nil))
                (RBpred_cf p bb1.(bb_exit) bb2.(bb_exit))
    | _, _ => bb
    end
  | _ => bb
  end.

Definition is_cond_cfi (cfi: cf_instr) :=
  match cfi with
  | RBcond _ _ _ _ => true
  | _ => false
  end.

Definition find_block_with_cond (c: code) : option (node * bblock) :=
  match List.filter (fun x => is_cond_cfi (snd x).(bb_exit)) (PTree.elements c) with
  | (a :: b)%list => Some a
  | nil => None
  end.

Definition transf_function (f: function) : function :=
  match find_block_with_cond f.(fn_code) with
  | Some (n, bb) =>
    let nbb := if_convert_block f.(fn_code) (Pvar 1%positive) bb in
    mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
               (PTree.set n nbb f.(fn_code)) f.(fn_entrypoint)
  | None => f
  end.

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
