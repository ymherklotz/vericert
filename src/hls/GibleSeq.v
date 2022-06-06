(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Gible.

(*|
========
GibleSeq
========
|*)

Module SeqBB <: BlockType.

  Definition t := list instr.

  Definition foldl {A: Type}: (A -> instr -> A) -> t -> A -> A := @fold_left A instr.

  Definition length : t -> nat := @length instr.

(*|
Instruction list step
---------------------

The ``step_instr_list`` definition describes the execution of a list of
instructions in one big step, inductively traversing the list of instructions
and applying the ``step_instr``.

This is simply using the high-level function ``step_list``, which is a general
function that can execute lists of things, given their execution rule.
|*)

  Definition step {A B: Type} (ge: Genv.t A B) := step_list (step_instr ge).

End SeqBB.

Module GibleSeq := Gible(SeqBB).
Export GibleSeq.

Fixpoint replace_section {A: Type} (f: A -> instr -> (A * SeqBB.t)) (s: A) (b: SeqBB.t): A * SeqBB.t :=
  match b with
  | i :: b' =>
      let (s', b'') := replace_section f s b' in
      let (s'', i') := f s' i in
      (s'', i' ++ b'')
  | nil => (s, nil)
  end.

Lemma forbidden_term_trans :
  forall A B ge sp i c b i' c',
    ~ @SeqBB.step A B ge sp (Iterm i c) b (Iterm i' c').
Proof. induction b; unfold not; intros; inv H. Qed.

Lemma step_instr_false :
  forall A B ge sp i c a i0,
    ~ @step_instr A B ge sp (Iterm i c) a (Iexec i0).
Proof. destruct a; unfold not; intros; inv H. Qed.

Lemma step_list2_false :
  forall A B ge l0 sp i c i0',
    ~ step_list2 (@step_instr A B ge) sp (Iterm i c) l0 (Iexec i0').
Proof.
  induction l0; unfold not; intros.
  inv H. inv H. destruct i1. eapply step_instr_false in H4. auto.
  eapply IHl0; eauto.
Qed.

Lemma append' :
  forall A B l0 cf i0 i1 l1 sp ge i0',
    step_list2 (@step_instr A B ge) sp (Iexec i0) l0 (Iexec i0') ->
    @SeqBB.step A B ge sp (Iexec i0') l1 (Iterm i1 cf) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof.
  induction l0; crush. inv H. eauto. inv H. destruct i3.
  econstructor; eauto. eapply IHl0; eauto.
  eapply step_list2_false in H7. exfalso; auto.
Qed.

Lemma append :
  forall A B cf i0 i1 l0 l1 sp ge,
      (exists i0', step_list2 (@step_instr A B ge) sp (Iexec i0) l0 (Iexec i0') /\
                    @SeqBB.step A B ge sp (Iexec i0') l1 (Iterm i1 cf)) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof. intros. simplify. eapply append'; eauto. Qed.

Lemma append2 :
  forall A B l0 cf i0 i1 l1 sp ge,
    @SeqBB.step A B ge sp (Iexec i0) l0 (Iterm i1 cf) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof.
  induction l0; crush.
  inv H.
  inv H. econstructor; eauto. eapply IHl0; eauto.
  constructor; auto.
Qed.

#[local] Open Scope positive.

Lemma max_pred_function_use :
  forall f pc bb i p,
    f.(fn_code) ! pc = Some bb ->
    In i bb ->
    In p (pred_uses i) ->
    p <= max_pred_function f.
Proof. Admitted.
