(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <git@yannherklotz.com>
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
Require Import compcert.common.Errors.
Require Import compcert.common.Linking.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePargenproofEquiv.
Require Import vericert.hls.GiblePargen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.
Require Import vericert.common.Monad.

Module Import OptionExtra := MonadExtra(Option).

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

#[local] Opaque simplify.
#[local] Opaque deep_simplify.

#[local] Ltac destr := destruct_match; try discriminate; [].

Definition state_lessdef := GiblePargenproofEquiv.match_states.

(*|
===================================
GiblePar to Abstr Translation Proof
===================================

This proof is for the correctness of the translation from the parallel Gible
program into the Abstr language, which is the symbolic execution language.  The
main characteristic of this proof is that it has to be performed backwards, as
the translation goes from GiblePar to Abstr, whereas the correctness proof is
needed from Abstr to GiblePar to get the proper direction of the proof.
|*)

Section CORRECTNESS.

Context (prog: GibleSeq.program) (tprog : GiblePar.program).

Let ge : GibleSeq.genv := Globalenvs.Genv.globalenv prog.
Let tge : GiblePar.genv := Globalenvs.Genv.globalenv tprog.

Lemma sem_equiv_execution :
  forall sp x i i' ti cf x' ti',
    abstract_sequence x = Some x' ->
    sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
    SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf) ->
    state_lessdef i ti ->
    state_lessdef i' ti'.
Proof. Admitted.

Lemma sem_exists_execution :
  forall sp x i i' ti cf x',
    abstract_sequence x = Some x' ->
    sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
    exists ti', SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf).
Proof. Admitted.

Lemma abstr_seq_reverse_correct :
  forall sp x i i' ti cf x',
    abstract_sequence x = Some x' ->
    sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
    state_lessdef i ti ->
   exists ti', SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf)
           /\ state_lessdef i' ti'.
Proof.
  intros. exploit sem_exists_execution; eauto; simplify.
  eauto using sem_equiv_execution.
Qed.

(*|
Proof Sketch:

We do an induction over the list of instructions ``x``.  This is trivial for the
empty case and then for the inductive case we know that there exists an
execution that matches the abstract execution, so we need to know that adding
another instructions to it will still mean that the execution will result in the
same value.

Arithmetic operations will be a problem because we will have to show that these
can be executed.  However, this should mostly be a problem in the abstract state
comparison, because there two abstract states can be equal without one being
evaluable.
|*)

End CORRECTNESS.
