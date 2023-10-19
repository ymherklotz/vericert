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

Require Import Coq.micromega.Lia.

Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.
Require compcert.common.Globalenvs.
Require compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSubPar.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Predicate.
Require Import vericert.common.Errormonad.
Import ErrorMonad.
Import ErrorMonadExtra.
Import MonadNotation.

#[local] Open Scope monad_scope.

Definition transl_block' (icode: positive * (positive * GibleSubPar.code)) (bb: SubParBB.t): 
  res (positive * (positive * GibleSubPar.code)) :=
  let '(curr, (next, code)) := icode in
  match code ! curr with
  | None => OK (next, (Pos.succ next, PTree.set curr (bb ++ (((RBexit None (RBgoto next))::nil)::nil)) code))
  | _ => Error (msg "GibleSubPargen: Overlapping blocks in translation")
  end.

Definition transl_block (freshcode: positive * GibleSubPar.code) (ibb: positive * ParBB.t): res (positive * GibleSubPar.code) :=
  let (i, bb) := ibb in
  let (fresh, code) := freshcode in
  map snd (mfold_left transl_block' bb (OK (i, (fresh, code)))).

Definition transl_function (f: GiblePar.function) : res GibleSubPar.function :=
  do new_code <- mfold_left transl_block (PTree.elements f.(fn_code)) (OK (Pos.succ (max_pc_function f), PTree.empty _));
  OK (GibleSubPar.mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize) (snd new_code) f.(fn_entrypoint)).

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : GiblePar.program) : Errors.res GibleSubPar.program :=
  transform_partial_program transl_fundef p.
