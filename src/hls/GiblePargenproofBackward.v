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

Require Import Optionmonad.
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

(*Lemma sem_equiv_execution :
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
Proof. Admitted. *)

Definition update' (s: pred_op * forest * list pred_expr) (i: instr): option (pred_op * forest * list pred_expr) :=
  let '(p, f, l) := s in
  Option.bind2 (fun p' f' => Option.ret (p', f', remember_expr f l i)) (update (p, f) i).

Definition abstract_sequence' (b : list instr) : option (forest * list pred_expr) :=
  Option.map (fun x => let '(_, y, z) := x in (y, z))
    (mfold_left update' b (Some (Ptrue, empty, nil))).

Definition i_state (s: istate): instr_state :=
  match s with
  | Iexec t => t
  | Iterm t _ => t
  end.

Definition cf_state (s: istate): option cf_instr :=
  match s with
  | Iexec _ => None
  | Iterm _ cf => Some cf
  end.

Definition evaluable_pred_expr {G} (ctx: @Abstr.ctx G) pr p :=
  exists r,
      sem_pred_expr pr sem_value ctx p r.

Definition evaluable_pred_list {G} ctx pr l :=
  forall p,
    In p l ->
    @evaluable_pred_expr G ctx pr p.

Lemma evaluable_pred_expr_exists :
  forall sp pr f i0 exit_p exit_p' f' cf i ti p op args dst,
    update (exit_p, f) (RBop p op args dst) = Some (exit_p', f') ->
    sem (mk_ctx i0 sp ge) f (i, cf) ->
    evaluable_pred_expr (mk_ctx i0 sp ge) pr (f' #r (Reg dst)) ->
    state_lessdef i ti ->
    exists ti', step_instr ge sp (Iexec ti) (RBop p op args dst) (Iexec ti').
Proof.
  intros. cbn in H. unfold Option.bind in H. destr. inv H.
  destruct ti. econstructor. econstructor.
  unfold evaluable_pred_expr in H1. Admitted.

Lemma remember_expr_in :
  forall x l f a,
    In x l -> In x (remember_expr f l a).
Proof.
  unfold remember_expr; destruct a; eauto using in_cons.
Qed.

Lemma in_mfold_left_abstr :
  forall instrs p f l p' f' l' x,
    mfold_left update' instrs (Some (p, f, l)) = Some (p', f', l') ->
    In x l -> In x l'.
Proof.
  induction instrs; intros.
  - cbn in *; now inv H.
  - cbn -[update] in *.
    pose proof H as Y.
    apply OptionExtra.mfold_left_Some in Y. inv Y.
    rewrite H1 in H. destruct x0 as ((p_int & f_int) & l_int).
    exploit IHinstrs; eauto.
    unfold Option.bind2, Option.ret in H1; repeat destr. inv H1.
    auto using remember_expr_in.
Qed.

Lemma abstr_seq_reverse_correct_fold :
  forall sp instrs i0 i i' ti cf f' l p p' l' f,
    sem (mk_ctx i0 sp ge) f (i, None) ->
    mfold_left update' instrs (Some (p, f, l)) = Some (p', f', l') ->
    evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) l' ->
    sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
    state_lessdef i ti ->
    exists ti',
      SeqBB.step ge sp (Iexec ti) instrs (Iterm ti' cf)
      /\ state_lessdef i' ti'.
Proof.
  induction instrs; intros * Y3 Y Y0 Y1 Y2.
  - cbn in *. inv Y.
    assert (similar {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |}
                    {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |})
      by auto using similar_refl.
    now eapply sem_det in H; [| eapply Y1 | eapply Y3 ].
  - cbn -[update] in Y.
    pose proof Y as YX.
    apply OptionExtra.mfold_left_Some in YX. inv YX.
    rewrite H in Y.
    destruct x as ((p_mid & f_mid) & l_mid).
    unfold Option.bind2, Option.ret in H. repeat destr.
    inv H.

    (* Assume we are in RBop for now*)
    assert (exists pred op args dst, a = RBop pred op args dst)
      by admit; destruct H as (pred & op & args & dst & EQ); subst a.

    exploit evaluable_pred_expr_exists; eauto.
    unfold evaluable_pred_list in Y0.
    instantiate (1 := forest_preds f').
    apply Y0 in YI. auto.
    (* provable using evaluability in list *) intros [t step].

    assert (exists ti_mid, sem {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |}
                             f_mid (ti_mid, None)) by admit.

    destruct H as (ti_mid & Hsem2).
    exploit IHinstrs. 2: { eapply Y. }  eauto. auto. eauto. reflexivity.
    intros (ti_mid' & Hseq & Hstate).
    assert (state_lessdef ti_mid t) by admit.
    exists ti_mid'; split; auto.
    econstructor; eauto.
Admitted.

Lemma sem_empty :
  forall G (ctx: @Abstr.ctx G),
    sem ctx empty (ctx_is ctx, None).
Proof.
  intros. destruct ctx. cbn. destruct ctx_is.
  constructor.
  constructor. cbn. intros. rewrite get_empty.
  constructor. cbn. constructor. constructor. constructor. intros.
  rewrite get_empty_p. constructor. constructor.
  rewrite get_empty. constructor. cbn. constructor.
  constructor. constructor. cbn. constructor. constructor.
Qed.

Lemma abstr_seq_reverse_correct:
  forall sp x i i' ti cf x' l,
    abstract_sequence' x = Some (x', l) ->
    (forall p, In p l -> exists r, sem_pred_expr x'.(forest_preds) sem_value (mk_ctx i sp ge) p r) ->
    sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
    state_lessdef i ti ->
   exists ti', SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf)
           /\ state_lessdef i' ti'.
Proof.
(*  intros. exploit sem_exists_execution; eauto; simplify.
  eauto using sem_equiv_execution.
Qed. *)
  intros. unfold abstract_sequence' in H.
  unfold Option.map in H. repeat destr. inv H.
  eapply  abstr_seq_reverse_correct_fold.
  2: {  eauto. }
  all: eauto.
  apply sem_empty.
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
