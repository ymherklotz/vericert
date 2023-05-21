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
Require Import vericert.hls.Predicate.

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

Lemma step_list_false :
  forall A B ge sp a i0 s,
    ~ step_list (@step_instr A B ge) sp s a (Iexec i0).
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

#[local] Notation "'mki'" := (mk_instr_state) (at level 1).

Lemma exec_rbexit_truthy :
  forall A B bb ge sp rs pr m rs' pr' m' cf,
    @SeqBB.step A B ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf) ->
    exists p b1 b2,
      truthy pr' p
      /\ bb = b1 ++ (RBexit p cf) :: b2
      /\ step_list2 (Gible.step_instr ge) sp (Iexec (mki rs pr m)) b1 (Iexec (mki rs' pr' m')).
Proof.
  induction bb; crush.
  inv H. inv H.
  - destruct state'. exploit IHbb; eauto; simplify.
    exists x. exists (a :: x0). exists x1. simplify; auto.
    econstructor; eauto.
  -  inv H3.
     exists p. exists (@nil instr). exists bb. crush.
     constructor.
Qed.

#[local] Open Scope positive.

Lemma max_pred_function_use :
  forall f pc bb i p,
    f.(fn_code) ! pc = Some bb ->
    In i bb ->
    In p (pred_uses i) ->
    p <= max_pred_function f.
Proof. Admitted.

Ltac truthy_falsy :=
  match goal with
  | H: instr_falsy ?ps (RBop ?p _ _ _), H2: truthy ?ps ?p |- _ =>
      solve [inv H2; inv H; crush]
  | H: instr_falsy ?ps (RBload ?p _ _ _ _), H2: truthy ?ps ?p |- _ =>
      solve [inv H2; inv H; crush]
  | H: instr_falsy ?ps (RBstore ?p _ _ _ _), H2: truthy ?ps ?p |- _ =>
      solve [inv H2; inv H; crush]
  | H: instr_falsy ?ps (RBexit ?p _), H2: truthy ?ps ?p |- _ =>
      solve [inv H2; inv H; crush]
  | H: instr_falsy ?ps (RBsetpred ?p _ _ _), H2: truthy ?ps ?p |- _ =>
      solve [inv H2; inv H; crush]
  end.

Lemma exec_determ :
  forall A B ge sp s1 a s2 s2',
    @step_instr A B ge sp s1 a s2 ->
    step_instr ge sp s1 a s2' ->
    s2 = s2'.
Proof.
  inversion 1; subst; crush.
  - inv H0; auto.
  - inv H2; crush; truthy_falsy.
  - inv H3; crush. truthy_falsy.
  - inv H3; crush. truthy_falsy.
  - inv H2; crush. truthy_falsy.
  - inv H1; crush. truthy_falsy.
  - destruct st; simplify. inv H1; crush; truthy_falsy.
Qed.

Lemma append3 :
  forall A B l0 l1 sp ge s1 s2 s3,
    step_list2 (step_instr ge) sp s1 l0 (Iexec s2) ->
    @SeqBB.step A B ge sp s1 (l0 ++ l1) s3 ->
    @SeqBB.step A B ge sp (Iexec s2) l1 s3.
Proof.
  induction l0; crush. inv H. auto.
  inv H0. inv H. assert (i1 = (Iexec state')) by (eapply exec_determ; eauto). subst. eauto.
  inv H. assert (i1 = (Iterm state' cf)) by (eapply exec_determ; eauto). subst.
  exfalso; eapply step_list2_false; eauto.
Qed.

Lemma step_cf_in :
  forall A B (ge: Genv.t A B) sp bb i1 i2 cf,
    SeqBB.step ge sp (Iexec i1) bb (Iterm i2 cf) ->
    exists p, In (RBexit p cf) bb.
Proof.
  induction bb; crush; inv H; eauto.
  exploit IHbb; eauto; simplify; eauto.
  inv H3; eauto.
Qed.

Lemma SeqBB_foldl_In :
  forall bb l pc,
    In pc l ->
    In pc (fold_left (fun (ns : list node) (i : instr) => match i with
                                                       | RBexit _ cf0 => successors_instr cf0 ++ ns
                                                       | _ => ns
                                                       end) bb l).
Proof.
  induction bb; crush. eapply IHbb; eauto.
  destruct a; auto.
  apply in_or_app; auto.
Qed.

Lemma in_cf_all_successors' :
  forall bb pc cf p l,
    In pc (successors_instr cf) ->
    In (RBexit p cf) bb ->
    In pc (fold_left (fun (ns : list node) (i : instr) => match i with
                                                       | RBexit _ cf0 => successors_instr cf0 ++ ns
                                                       | _ => ns
                                                       end) bb l).
Proof.
  induction bb; crush.
  inv H0. simplify.
  eapply SeqBB_foldl_In.
  apply in_or_app; auto.
  eapply IHbb; eauto.
Qed.

Lemma in_cf_all_successors :
  forall bb pc cf p,
    In pc (successors_instr cf) ->
    In (RBexit p cf) bb ->
    In pc (all_successors bb).
Proof.
  unfold all_successors, SeqBB.foldl; intros.
  eapply in_cf_all_successors'; eauto.
Qed.

Lemma eq_stepBB :
  forall A B (ge: Genv.t A B) sp l i1 i2 i2',
    SeqBB.step ge sp i1 l i2 ->
    SeqBB.step ge sp i1 l i2' ->
    i2 = i2'.
Proof.
  induction l; crush.  inv H.
  inv H; inv H0.
  assert (Iexec state' = Iexec state'0).
  { eapply exec_determ; eauto. }
  inv H. eauto.
  assert (Iexec state' = Iterm state'0 cf0).
  { eapply exec_determ; eauto. }
  discriminate.
  assert (Iterm state' cf = Iexec state'0).
  { eapply exec_determ; eauto. }
  discriminate.
  eapply exec_determ; eauto.
Qed.

Lemma step_options :
  forall A B (ge: Genv.t A B) a b i1 i2 cf sp,
    SeqBB.step ge sp (Iexec i1) (a ++ b) (Iterm i2 cf) ->
    (SeqBB.step ge sp (Iexec i1) a (Iterm i2 cf) \/
       exists i1', step_list2 (step_instr ge) sp (Iexec i1) a (Iexec i1')
              /\ SeqBB.step ge sp (Iexec i1') b (Iterm i2 cf)).
Proof.
  induction a; crush. right; eexists; split; [constructor|auto].
  inv H. exploit IHa; eauto; intros. inv H.
  left; econstructor; eauto.
  simplify.
  right. eexists; split; eauto. econstructor; eauto.
  left. constructor; eauto.
Qed.

Lemma step_options2' :
  forall A B (ge: Genv.t A B) a b i1 i2 sp,
    step_list2 (step_instr ge) sp (Iexec i1) (a ++ b) (Iexec i2) ->
    (step_list2 (step_instr ge) sp (Iexec i1) a (Iexec i2) \/
       exists i1', step_list2 (step_instr ge) sp (Iexec i1) a (Iexec i1')
              /\ step_list2 (step_instr ge) sp (Iexec i1') b (Iexec i2)).
Proof.
  induction a; crush. right; eexists; split; [constructor|auto].
  inv H. destruct i3; [|exfalso; eapply step_list2_false; eauto]. exploit IHa; eauto; intros. inv H.
  left; econstructor; eauto.
  simplify.
  right. eexists; split; eauto. econstructor; eauto.
Qed.

Lemma step_options2 :
  forall A B (ge: Genv.t A B) a b i1 i2 sp,
    step_list2 (step_instr ge) sp (Iexec i1) (a ++ b) (Iexec i2) ->
    exists i', step_list2 (step_instr ge) sp (Iexec i1) a (Iexec i')
          /\ step_list2 (step_instr ge) sp (Iexec i') b (Iexec i2).
Proof.
  induction a; crush. eexists; split; eauto.
  constructor.
  inv H. destruct i3; [|exfalso; eapply step_list2_false; eauto].
  exploit IHa; eauto; simplify.
  eexists; split; eauto. econstructor; eauto.
Qed.

Lemma step_instr_unchanged_state :
  forall A (ge: Genv.t A unit) sp r st st' cf,
    step_instr ge sp (Iexec st) r (Iterm st' cf) -> st = st'.
Proof. intros. inv H; auto. Qed.

Lemma step_exists:
  forall A (ge: Genv.t A unit) sp instrs i i' ti cf,
    SeqBB.step ge sp (Iexec i) instrs (Iterm i' cf) ->
    state_equiv i ti ->
    exists ti',
      SeqBB.step ge sp (Iexec ti) instrs (Iterm ti' cf)
      /\ state_equiv i' ti'.
Proof.
  induction instrs.
  - intros. inv H.
  - intros. inv H.
    + exploit (@step_exists A); eauto; simplify.
      exploit IHinstrs; eauto; simplify.
      eexists; split. econstructor; eauto. auto.
    + inversion H4; subst. eexists. constructor.
      constructor. eapply step_exists_Iterm; eauto. auto.
Qed.
