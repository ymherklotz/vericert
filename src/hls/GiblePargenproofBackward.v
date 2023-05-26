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
Require Import vericert.hls.GiblePargenproofCommon.
Require Import vericert.hls.GiblePargenproofForward.
Require Import vericert.hls.GiblePargen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.
Require Import vericert.hls.AbstrSemIdent.
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

(* Set Nested Proofs Allowed. *)

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

Definition remember_expr (f : forest) (lst: list pred_expr) (i : instr): list pred_expr :=
  match i with
  | RBnop => lst
  | RBop p op rl r => (f #r (Reg r)) :: lst
  | RBload  p chunk addr rl r => (f #r (Reg r)) :: lst
  | RBstore p chunk addr rl r => lst
  | RBsetpred p' c args p => lst
  | RBexit p c => lst
  end.

Definition remember_expr_m (f : forest) (lst: list pred_expr) (i : instr): list pred_expr :=
  match i with
  | RBnop => lst
  | RBop p op rl r => lst
  | RBload  p chunk addr rl r => lst
  | RBstore p chunk addr rl r => (f #r Mem) :: lst
  | RBsetpred p' c args p => lst
  | RBexit p c => lst
  end.

Definition update' (s: pred_op * forest * list pred_expr * list pred_expr) (i: instr): option (pred_op * forest * list pred_expr * list pred_expr) :=
  let '(p, f, l, lm) := s in
  Option.bind2 (fun p' f' => Option.ret (p', f', remember_expr f l i, remember_expr_m f lm i)) (update (p, f) i).

Lemma equiv_update:
  forall i p f l lm p' f' l' lm',
    mfold_left update' i (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left update i (Some (p, f)) = Some (p', f').
Proof.
  induction i; cbn -[update] in *; intros.
  - inv H; auto.
  - exploit OptionExtra.mfold_left_Some; eauto;
      intros [[[[p_mid f_mid] l_mid] lm_mid] HB].
    unfold Option.bind2, Option.ret in HB; repeat destr. inv Heqp1.
    eapply IHi; eauto.
Qed.

Definition gather_predicates (preds : PTree.t unit) (i : instr): option (PTree.t unit) :=
  match i with
  | RBop (Some p) _ _ _
  | RBload (Some p) _ _ _ _
  | RBstore (Some p) _ _ _ _
  | RBexit (Some p) _ =>
    Some (fold_right (fun x => PTree.set x tt) preds (predicate_use p))
  | RBsetpred p' c args p =>
    let preds' := match p' with
                  | Some p'' => fold_right (fun x => PTree.set x tt) preds (predicate_use p'')
                  | None => preds
                  end
    in
    match preds' ! p with
    | Some _ => None
    | None => Some (PTree.set p tt preds')
    end
  | _ => Some preds
  end.

Definition abstract_sequence' (b : list instr) : option (forest * list pred_expr * list pred_expr) :=
  Option.bind (fun x => Option.bind (fun _ => Some x)
    (mfold_left gather_predicates b (Some (PTree.empty _))))
      (Option.map (fun x => let '(_, y, z, zm) := x in (y, z, zm))
        (mfold_left update' b (Some (Ptrue, empty, nil, nil)))).

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
  exists r, sem_pred_expr pr sem_value ctx p r.

Definition evaluable_pred_expr_m {G} (ctx: @Abstr.ctx G) pr p :=
  exists r, sem_pred_expr pr sem_mem ctx p r.

Definition evaluable_pred_list {G} ctx pr l :=
  forall p,
    In p l ->
    @evaluable_pred_expr G ctx pr p.

Definition evaluable_pred_list_m {G} ctx pr l :=
  forall p,
    In p l ->
    @evaluable_pred_expr_m G ctx pr p.

(* Lemma evaluable_pred_expr_exists : *)
(*   forall sp pr f i0 exit_p exit_p' f' cf i ti p op args dst, *)
(*     update (exit_p, f) (RBop p op args dst) = Some (exit_p', f') -> *)
(*     sem (mk_ctx i0 sp ge) f (i, cf) -> *)
(*     evaluable_pred_expr (mk_ctx i0 sp ge) pr (f' #r (Reg dst)) -> *)
(*     state_lessdef i ti -> *)
(*     exists i', sem (mk_ctx i0 sp ge) f' (i', cf). *)
(* Proof. *)
(*   intros. cbn in H. unfold Option.bind in H. destr. inv H. *)
(*   destruct ti. econstructor. econstructor. *)
(*   unfold evaluable_pred_expr in H1. Admitted. *)

Lemma evaluable_pred_expr_exists_RBop :
  forall sp f i0 exit_p exit_p' f' i ti p op args dst,
    eval_predf (is_ps i) exit_p = true ->
    valid_mem (is_mem i0) (is_mem i) ->
    update (exit_p, f) (RBop p op args dst) = Some (exit_p', f') ->
    sem (mk_ctx i0 sp ge) f (i, None) ->
    evaluable_pred_expr (mk_ctx i0 sp ge) f'.(forest_preds) (f' #r (Reg dst)) ->
    state_lessdef i ti ->
    exists ti',
      step_instr ge sp (Iexec ti) (RBop p op args dst) (Iexec ti').
Proof.
  intros * HEVAL VALID_MEM **. cbn -[seq_app] in H. unfold Option.bind in H. destr. inv H.
  assert (HPRED': sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
    by now inv H0.
  inversion_clear HPRED' as [? ? ? HPRED].
  destruct ti as [is_trs is_tps is_tm].
  unfold evaluable_pred_expr in H1. destruct H1 as (r & Heval).
  rewrite forest_reg_gss in Heval.
  exploit sem_pred_expr_prune_predicated2; eauto; intros.
  pose proof (truthy_dec (is_ps i) p) as YH. inversion_clear YH as [YH'|YH'].
  - assert (eval_predf (is_ps i) (dfltp p ∧ exit_p') = true).
    { pose proof (truthy_dflt _ _ YH'). rewrite eval_predf_Pand.
      rewrite H1. now rewrite HEVAL. }
    exploit sem_pred_expr_app_predicated2; eauto; intros.
    exploit sem_pred_expr_seq_app_val2; eauto; simplify.
    unfold pred_ret in *. inv H4. inv H12.
    destruct i as [is_rs_1 is_ps_1 is_m_1]. exploit sem_merge_list; eauto; intros.
    instantiate (1 := args) in H4.
    eapply sem_pred_expr_ident2 in H4. simplify.
    exploit sem_pred_expr_ident_det. eapply H5. eapply H4.
    intros. subst. inv H7.
    eapply sem_val_list_det in H8; eauto; [|reflexivity]. subst.
    inv H2.
    econstructor. constructor.
    + cbn in *. eapply eval_operation_valid_pointer. symmetry; eauto.
      unfold ctx_mem in H14. cbn in H14. erewrite <- match_states_list; eauto.
    + inv H0.
      assert (sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps_1))
        by (now constructor).
      pose proof (sem_predset_det _ _ ltac:(reflexivity) _ _ _ H0 H17).
      assert (truthy is_ps_1 p).
      { eapply truthy_match_state; eassumption. }
      eapply truthy_match_state; eassumption.
  - inv YH'. cbn -[seq_app] in H.
    assert (eval_predf (is_ps i) (p0 ∧ exit_p') = false).
    { rewrite eval_predf_Pand. now rewrite H1. }
    eapply sem_pred_expr_app_predicated_false2 in H; eauto.
    eexists. eapply exec_RB_falsy. constructor. auto. cbn.
    assert (sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
        by (now constructor).
    inv H0. pose proof (sem_predset_det _ _ ltac:(reflexivity) _ _ _ H4 H8).
    inv H2.
    erewrite <- eval_predf_pr_equiv by exact H16.
    now erewrite <- eval_predf_pr_equiv by exact H0.
Qed.

Lemma evaluable_pred_expr_exists_RBload :
  forall sp f i0 exit_p exit_p' f' i ti p chunk addr args dst,
    eval_predf (is_ps i) exit_p = true ->
    valid_mem (is_mem i0) (is_mem i) ->
    update (exit_p, f) (RBload p chunk addr args dst) = Some (exit_p', f') ->
    sem (mk_ctx i0 sp ge) f (i, None) ->
    evaluable_pred_expr (mk_ctx i0 sp ge) f'.(forest_preds) (f' #r (Reg dst)) ->
    state_lessdef i ti ->
    exists ti',
      step_instr ge sp (Iexec ti) (RBload p chunk addr args dst) (Iexec ti').
Proof.
  intros * HEVAL VALID_MEM **. cbn -[seq_app] in H. unfold Option.bind in H. destr. inv H.
  assert (HPRED': sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
    by now inv H0.
  inversion_clear HPRED' as [? ? ? HPRED].
  destruct ti as [is_trs is_tps is_tm].
  unfold evaluable_pred_expr in H1. destruct H1 as (r & Heval).
  rewrite forest_reg_gss in Heval.
  exploit sem_pred_expr_prune_predicated2; eauto; intros.
  pose proof (truthy_dec (is_ps i) p) as YH. inversion_clear YH as [YH'|YH'].
  - assert (eval_predf (is_ps i) (dfltp p ∧ exit_p') = true).
    { pose proof (truthy_dflt _ _ YH'). rewrite eval_predf_Pand.
      rewrite H1. now rewrite HEVAL. }
    exploit sem_pred_expr_app_predicated2; eauto; intros.
    exploit sem_pred_expr_seq_app_val2; eauto; simplify.
    exploit sem_pred_expr_seq_app_val2; eauto; simplify.
    unfold pred_ret in *. inv H6. inv H15. clear H13. inv H10.
    destruct i as [is_rs_1 is_ps_1 is_m_1]. exploit sem_merge_list; eauto; intros.
    instantiate (1 := args) in H6.
    eapply sem_pred_expr_ident2 in H6. simplify.
    exploit sem_pred_expr_ident_det. eapply H8. eapply H6.
    intros. subst. inv H7.
    eapply sem_val_list_det in H10; eauto; [|reflexivity]. subst.
    cbn in *. inv H2.
    econstructor. econstructor; eauto.
    + erewrite <- match_states_list; eauto.
    + inv H0. exploit sem_pred_expr_ident. eapply H5. eapply H15. intros.
      eapply sem_pred_expr_det in H0. rewrite H0. eassumption.
      reflexivity. eapply sem_mem_det. reflexivity. auto.
    + inv H0.
      assert (sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps_1))
        by (now constructor).
      pose proof (sem_predset_det _ _ ltac:(reflexivity) _ _ _ H0 H20).
      assert (truthy is_ps_1 p).
      { eapply truthy_match_state; eassumption. }
      eapply truthy_match_state; eassumption.
  - inv YH'. cbn -[seq_app] in H.
    assert (eval_predf (is_ps i) (p0 ∧ exit_p') = false).
    { rewrite eval_predf_Pand. now rewrite H1. }
    eapply sem_pred_expr_app_predicated_false2 in H; eauto.
    eexists. eapply exec_RB_falsy. constructor. auto. cbn.
    assert (sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
        by (now constructor).
    inv H0. pose proof (sem_predset_det _ _ ltac:(reflexivity) _ _ _ H4 H8).
    inv H2.
    erewrite <- eval_predf_pr_equiv by exact H16.
    now erewrite <- eval_predf_pr_equiv by exact H0.
Qed.

Lemma evaluable_pred_expr_exists_RBstore :
  forall sp f i0 exit_p exit_p' f' i ti p chunk addr args src,
    eval_predf (is_ps i) exit_p = true ->
    valid_mem (is_mem i0) (is_mem i) ->
    update (exit_p, f) (RBstore p chunk addr args src) = Some (exit_p', f') ->
    sem (mk_ctx i0 sp ge) f (i, None) ->
    evaluable_pred_expr_m (mk_ctx i0 sp ge) f'.(forest_preds) (f' #r Mem) ->
    state_lessdef i ti ->
    exists ti',
      step_instr ge sp (Iexec ti) (RBstore p chunk addr args src) (Iexec ti').
Proof.
  intros * HEVAL VALID_MEM **. cbn -[seq_app] in H. unfold Option.bind in H. destr. inv H.
  assert (HPRED': sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
    by now inv H0.
  inversion_clear HPRED' as [? ? ? HPRED].
  destruct ti as [is_trs is_tps is_tm].
  unfold evaluable_pred_expr in H1. destruct H1 as (r & Heval).
  rewrite forest_reg_gss in Heval.
  exploit sem_pred_expr_prune_predicated2; eauto; intros.
  pose proof (truthy_dec (is_ps i) p) as YH. inversion_clear YH as [YH'|YH'].
  - assert (eval_predf (is_ps i) (dfltp p ∧ exit_p') = true).
    { pose proof (truthy_dflt _ _ YH'). rewrite eval_predf_Pand.
      rewrite H1. now rewrite HEVAL. }
    exploit sem_pred_expr_app_predicated2; eauto; intros.
    exploit sem_pred_expr_seq_app_val2; eauto; simplify.
    exploit sem_pred_expr_seq_app_val2; eauto; simplify.
    exploit sem_pred_expr_flap2_2; eauto; simplify.
    exploit sem_pred_expr_seq_app_val2; eauto; simplify.
    unfold pred_ret in *. inv H14. inv H11. inv H18. clear H16. inv H10. inv H7.
    destruct i as [is_rs_1 is_ps_1 is_m_1]. exploit sem_merge_list; eauto; intros.
    instantiate (1 := args) in H7.
    eapply sem_pred_expr_ident2 in H7. simplify.
    exploit sem_pred_expr_ident_det. eapply H8. eapply H7.
    intros. subst.
    eapply sem_val_list_det in H20; eauto; [|reflexivity]. subst.
    cbn in *. inv H2. inv H0. inv H20. pose proof H0 as YH0. specialize (YH0 src).
    exploit sem_pred_expr_ident. eapply H5. eauto. intros.
    exploit sem_pred_expr_ident. eapply H12. eauto. intros.
    eapply sem_pred_expr_det in H25; eauto; [|reflexivity|eapply sem_mem_det; reflexivity].
    eapply sem_pred_expr_det in YH0; eauto; [|reflexivity|eapply sem_value_det; reflexivity].
    subst.
    econstructor. econstructor; eauto.
    + erewrite <- match_states_list; eauto.
    + rewrite <- H16. eassumption.
    + assert (sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps_1))
        by (now constructor).
      pose proof (sem_predset_det _ _ ltac:(reflexivity) _ _ _ H24 H13).
      assert (truthy is_ps_1 p).
      { eapply truthy_match_state; eassumption. }
      eapply truthy_match_state; eassumption.
  - inv YH'. cbn -[seq_app] in H.
    assert (eval_predf (is_ps i) (p0 ∧ exit_p') = false).
    { rewrite eval_predf_Pand. now rewrite H1. }
    eapply sem_pred_expr_app_predicated_false2 in H; eauto.
    eexists. eapply exec_RB_falsy. constructor. auto. cbn.
    assert (sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
        by (now constructor).
    inv H0. pose proof (sem_predset_det _ _ ltac:(reflexivity) _ _ _ H4 H8).
    inv H2.
    erewrite <- eval_predf_pr_equiv by exact H16.
    now erewrite <- eval_predf_pr_equiv by exact H0.
Qed.

Lemma evaluable_pred_expr_exists_RBsetpred :
  forall sp f i0 exit_p exit_p' f' i ti p c args src ps',
    eval_predf (is_ps i) exit_p = true ->
    valid_mem (is_mem i0) (is_mem i) ->
    update (exit_p, f) (RBsetpred p c args src) = Some (exit_p', f') ->
    sem (mk_ctx i0 sp ge) f (i, None) ->
    sem_predset (mk_ctx i0 sp ge) f' ps' ->
    state_lessdef i ti ->
    exists ti',
      step_instr ge sp (Iexec ti) (RBsetpred p c args src) (Iexec ti').
Proof.
  intros * HEVAL VALID_MEM **. cbn -[seq_app] in H. unfold Option.bind in H. destr. inv H.
  assert (HPRED': sem_predset {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |} f (is_ps i))
    by now inv H0.
  inversion_clear HPRED' as [? ? ? HPRED].
  destruct ti as [is_trs is_tps is_tm]. destr. inv H4. inv H1.
  pose proof H as YH. specialize (YH src). rewrite forest_pred_gss in YH.
  inv YH; try inv H3.
  + inv H1. inv H6. replace false with (negb true) in H4 by auto.
    replace false with (negb true) in H8 by auto.
    eapply sem_pexpr_negate2 in H4. eapply sem_pexpr_negate2 in H8.
    destruct i.
    exploit from_predicated_sem_pred_expr2; eauto; intros.
    exploit sem_pred_expr_seq_app_val2. eapply HPRED. eauto. simplify.
    inv H3. inv H15. clear H13.
    exploit sem_merge_list; eauto; intros. instantiate (1:=args) in H3.
    eapply sem_pred_expr_ident2 in H3; simplify. exploit sem_pred_expr_ident_det.
    eapply H6. eauto. intros. subst.
    intros. inv H10. eapply sem_val_list_det in H11; eauto. subst.
    inv H2.
    econstructor. econstructor. erewrite <- match_states_list; eauto.
    erewrite <- storev_eval_condition; eauto.
    assert (truthy is_ps p).
    { destruct p. cbn in H4. constructor.
      eapply sem_pexpr_forward_eval; eauto. constructor.
    }
    eapply truthy_match_state; eassumption.
    reflexivity.
  + inv H1. inv H6. inv H3.
    * replace false with (negb true) in H1 by auto. eapply sem_pexpr_negate2 in H1.
      eapply sem_pexpr_forward_eval in H1; eauto. rewrite eval_predf_negate in H1.
      assert ((eval_predf (is_ps i) (dfltp p)) = false).
      { replace false with (negb true) by auto. rewrite <- H1. now rewrite negb_involutive. }
      econstructor. apply exec_RB_falsy. cbn. destruct p. constructor; auto. inv H2.
      erewrite <- eval_predf_pr_equiv; eauto. now cbn in H3.
    * replace false with (negb true) in H1 by auto. eapply sem_pexpr_negate2 in H1.
      eapply sem_pexpr_forward_eval in H1; eauto. rewrite eval_predf_negate in H1.
      now rewrite HEVAL in H1.
  + inv H5. inv H3.
    * inv H1. inv H5.
      -- replace true with (negb false) in H1 by auto. eapply sem_pexpr_negate2 in H1.
         eapply sem_pexpr_forward_eval in H1; eauto.
         econstructor. apply exec_RB_falsy. cbn. destruct p. constructor; auto. inv H2.
         erewrite <- eval_predf_pr_equiv; eauto. now cbn in H1.
      -- replace true with (negb false) in H1 by auto. eapply sem_pexpr_negate2 in H1.
         eapply sem_pexpr_forward_eval in H1; eauto. now rewrite HEVAL in H1.
    * case_eq (eval_predf (is_ps i) (dfltp p)); intros.
      -- eapply sem_pexpr_eval in H3; eauto.
         destruct i.
         exploit from_predicated_sem_pred_expr2; eauto; intros.
         exploit sem_pred_expr_seq_app_val2. eapply HPRED. eauto. simplify.
         inv H7. inv H15. clear H13.
         exploit sem_merge_list; eauto; intros. instantiate (1:=args) in H7.
         eapply sem_pred_expr_ident2 in H7; simplify. exploit sem_pred_expr_ident_det.
         eapply H8. eauto. intros. subst.
         inv H10. clear H8. eapply sem_val_list_det in H11; eauto. subst.
         inv H2.
         econstructor. econstructor. erewrite <- match_states_list; eauto.
         erewrite <- storev_eval_condition; eauto.
         assert (truthy is_ps p).
         { destruct p. cbn in H4. constructor.
           eapply sem_pexpr_forward_eval; eauto.
           constructor.
         }
         eapply truthy_match_state; eassumption.
         reflexivity.
      -- econstructor. apply exec_RB_falsy.
         destruct p. constructor. inv H2. erewrite <- eval_predf_pr_equiv; eauto.
         easy.
Qed.

Lemma evaluable_pred_expr_exists_RBexit :
  forall sp i ti p cf,
    eval_predf (is_ps i) (dfltp p) = false ->
    state_lessdef i ti ->
    step_instr ge sp (Iexec ti) (RBexit p cf) (Iexec ti).
Proof.
  intros. constructor. destruct p; [|now cbn in *].
  inv H0. constructor. erewrite <- eval_predf_pr_equiv; eauto.
Qed.

Lemma evaluable_pred_expr_exists_RBexit2 :
  forall sp i ti p cf,
    eval_predf (is_ps i) (dfltp p) = true ->
    state_lessdef i ti ->
    step_instr ge sp (Iexec ti) (RBexit p cf) (Iterm ti cf).
Proof.
  intros. econstructor.
  inv H0. cbn. destruct p; try constructor.
  erewrite <- eval_predf_pr_equiv; eauto.
Qed.

Lemma evaluable_pred_expr_exists_RBexit3 :
  forall i p cf f p_exit p_exit' f',
    eval_predf (is_ps i) (dfltp p) = true ->
    update (p_exit, f) (RBexit p cf) = Some (p_exit', f') ->
    eval_predf (is_ps i) p_exit' = false.
Proof.
  intros. cbn in *. unfold Option.bind in *. destr. inv H0.
  rewrite eval_predf_simplify. rewrite eval_predf_Pand.
  rewrite eval_predf_negate. rewrite H. auto.
Qed.

Lemma remember_expr_in :
  forall x l f a,
    In x l -> In x (remember_expr f l a).
Proof.
  unfold remember_expr; destruct a; eauto using in_cons.
Qed.

Lemma remember_expr_in_m :
  forall x l f a,
    In x l -> In x (remember_expr_m f l a).
Proof.
  unfold remember_expr; destruct a; eauto using in_cons.
Qed.

Lemma in_mfold_left_abstr :
  forall instrs p f l p' f' l' x lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    In x l -> In x l'.
Proof.
  induction instrs; intros.
  - cbn in *; now inv H.
  - cbn -[update] in *.
    pose proof H as Y.
    apply OptionExtra.mfold_left_Some in Y. inv Y.
    rewrite H1 in H. destruct x0 as (((p_int & f_int) & l_int) & lm_int).
    exploit IHinstrs; eauto.
    unfold Option.bind2, Option.ret in H1; repeat destr. inv H1.
    auto using remember_expr_in.
Qed.

Lemma in_mfold_left_abstr_m :
  forall instrs p f l p' f' l' x lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    In x lm -> In x lm'.
Proof.
  induction instrs; intros.
  - cbn in *; now inv H.
  - cbn -[update] in *.
    pose proof H as Y.
    apply OptionExtra.mfold_left_Some in Y. inv Y.
    rewrite H1 in H. destruct x0 as (((p_int & f_int) & l_int) & lm_int).
    exploit IHinstrs; eauto.
    unfold Option.bind2, Option.ret in H1; repeat destr. inv H1.
    auto using remember_expr_in_m.
Qed.

Lemma not_remembered_in_forest :
  forall a p f p_mid f_mid l x,
    update (p, f) a = Some (p_mid, f_mid) ->
    ~ In f #r (Reg x) (remember_expr f l a) ->
    f #r (Reg x) = f_mid #r (Reg x).
Proof.
  intros; destruct a; cbn in *;
    unfold Option.bind in H; repeat destr; inv H; try easy.
  - assert (~ (f #r (Reg r) = f #r (Reg x)) /\ ~ (In f #r (Reg x) l)) by tauto.
    inv H. destruct (resource_eq (Reg r) (Reg x));
      try (rewrite e in *; contradiction).
    now rewrite forest_reg_gso by auto.
  - assert (~ (f #r (Reg r) = f #r (Reg x)) /\ ~ (In f #r (Reg x) l)) by tauto.
    inv H. destruct (resource_eq (Reg r) (Reg x));
      try (rewrite e in *; contradiction).
    now rewrite forest_reg_gso by auto.
  - destruct (resource_eq Mem (Reg x)); try discriminate.
    now rewrite forest_reg_gso by auto.
Qed.

Lemma not_remembered_in_forest_m :
  forall a p f p_mid f_mid l,
    update (p, f) a = Some (p_mid, f_mid) ->
    ~ In f #r Mem (remember_expr_m f l a) ->
    f #r Mem = f_mid #r Mem.
Proof.
  intros; destruct a; cbn in *;
    unfold Option.bind in H; repeat destr; inv H; try easy.
  - rewrite forest_reg_gso; auto. easy.
  - rewrite forest_reg_gso; auto. easy.
  - assert (~ (f #r Mem = f #r Mem) /\ ~ (In f #r Mem l)) by tauto. inv H.
    contradiction.
Qed.

Lemma in_forest_or_remembered :
  forall instrs p f l p' f' l' lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    forall x, In (f #r (Reg x)) l' \/ f #r (Reg x) = f' #r (Reg x).
Proof.
  induction instrs; try solve [crush]; []; intros.
  cbn -[update] in H.
  pose proof H as YX.
  apply OptionExtra.mfold_left_Some in YX. inv YX.
  rewrite H0 in H.
  destruct x0 as (((p_mid & f_mid) & l_mid) & lm_mid).
  pose proof (IHinstrs _ _ _ _ _ _ _ _ H).
  unfold Option.bind2, Option.ret in H0; cbn -[update] in H0; repeat destr.
  inv H0. specialize (H1 x).
  pose proof H as Y.
  destruct (in_dec pred_expr_eqb (f #r (Reg x)) (remember_expr f l a));
    eauto using in_mfold_left_abstr.
  inv H1; eapply not_remembered_in_forest with (f_mid := f_mid) in n; eauto;
    rewrite n in *; tauto.
Qed.

Lemma in_forest_or_remembered_m :
  forall instrs p f l p' f' l' lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    In (f #r Mem) lm' \/ f #r Mem = f' #r Mem.
Proof.
  induction instrs; try solve [crush]; []; intros.
  cbn -[update] in H.
  pose proof H as YX.
  apply OptionExtra.mfold_left_Some in YX. inv YX.
  rewrite H0 in H.
  destruct x as (((p_mid & f_mid) & l_mid) & lm_mid).
  pose proof (IHinstrs _ _ _ _ _ _ _ _ H).
  unfold Option.bind2, Option.ret in H0; cbn -[update] in H0; repeat destr.
  inv H0.
  pose proof H as Y.
  destruct (in_dec pred_expr_eqb (f #r Mem) (remember_expr_m f lm a));
    eauto using in_mfold_left_abstr_m.
  inv H1; eapply not_remembered_in_forest_m with (f_mid := f_mid) in n; eauto;
    rewrite n in *; tauto.
Qed.

Lemma in_forest_evaluable :
  forall G sp ge i' cf instrs p f l p' f' l' x i0 lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    sem (mk_ctx i0 sp ge) f' (i', cf) ->
    @evaluable_pred_list G (mk_ctx i0 sp ge) f'.(forest_preds) l' ->
    evaluable_pred_expr (mk_ctx i0 sp ge) f'.(forest_preds) (f #r (Reg x)).
Proof.
  intros.
  pose proof H as Y. apply in_forest_or_remembered with (x := x) in Y.
  inv Y; eauto.
  inv H0. inv H5. rewrite H2.
  unfold evaluable_pred_expr. eauto.
Qed.

Lemma in_forest_evaluable_m :
  forall G sp ge i' cf instrs p f l p' f' l' i0 lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    sem (mk_ctx i0 sp ge) f' (i', cf) ->
    @evaluable_pred_list_m G (mk_ctx i0 sp ge) f'.(forest_preds) lm' ->
    evaluable_pred_expr_m (mk_ctx i0 sp ge) f'.(forest_preds) (f #r Mem).
Proof.
  intros.
  pose proof H as Y. apply in_forest_or_remembered_m in Y.
  inv Y; eauto.
  inv H0. inv H5. rewrite H2.
  unfold evaluable_pred_expr_m. eauto.
Qed.

Definition pe_preds_in {A} (x: predicated A) preds :=
  NE.Forall (fun x => forall pred, PredIn pred (fst x)
               -> PTree.get pred preds = Some tt) x.

Definition all_preds_in f preds :=
  forall x, NE.Forall (fun x => forall pred, PredIn pred (fst x)
                       -> PTree.get pred preds = Some tt) (f #r x).

Lemma gather_predicates_fold:
  forall l preds x,
    preds ! x = Some tt ->
    (fold_right (fun x0 : positive => PTree.set x0 tt) preds l) ! x = Some tt.
Proof.
  induction l; crush.
  destruct (peq x a); subst.
  { rewrite PTree.gss; auto. }
  rewrite PTree.gso; eauto.
Qed.

Lemma gather_predicates_fold2:
  forall l preds x,
    In x l ->
    (fold_right (fun x0 : positive => PTree.set x0 tt) preds l) ! x = Some tt.
Proof.
  induction l; crush.
  destruct (peq x a); subst.
  { rewrite PTree.gss; auto. }
  rewrite PTree.gso; eauto.
  eapply IHl. now inv H.
Qed.

Lemma gather_predicates_fold3:
  forall l preds x,
    (fold_right (fun x0 : positive => PTree.set x0 tt) preds l) ! x = None ->
    preds ! x = None.
Proof.
  induction l; crush.
  destruct (peq x a); subst.
  { rewrite PTree.gss in H; discriminate. }
  rewrite PTree.gso in H; eauto.
Qed.

Lemma gather_predicates_fold4:
  forall l preds x,
    (fold_right (fun x0 : positive => PTree.set x0 tt) preds l) ! x = None ->
    ~ In x l.
Proof.
  induction l; crush.
  destruct (peq x a); subst.
  { rewrite PTree.gss in H; discriminate. }
  rewrite PTree.gso in H; eauto. intuition. eapply IHl; eauto.
Qed.

Lemma gather_predicates_in :
  forall i preds preds' x,
    gather_predicates preds i = Some preds' ->
    preds ! x = Some tt ->
    preds' ! x = Some tt.
Proof.
  destruct i; crush; try (destruct_match; inv H; auto);
    try (apply gather_predicates_fold; auto).
  destruct o; auto.
  destruct (peq x p); subst; [rewrite PTree.gss | rewrite PTree.gso by auto]; auto.
  apply gather_predicates_fold; auto.
  destruct (peq x p); subst; [rewrite PTree.gss | rewrite PTree.gso by auto]; auto.
Qed.

Lemma filter_predicated_in_pred :
  forall A (x y: predicated A) f preds,
    NE.filter f x = Some y ->
    pe_preds_in x preds ->
    pe_preds_in y preds.
Proof.
  induction x; intros.
  - cbn in *. destr. inv H. auto.
  - cbn in *. destruct_match; cbn in *. destruct_match.
    + inv H. inv H0. constructor; auto. eapply IHx; eauto.
    + inv H. inv H0; constructor; auto.
    + inv H0. eauto.
Qed.

#[local] Transparent deep_simplify.
Lemma deep_simplify_in :
  forall pop pred,
    PredIn pred (deep_simplify peq pop) ->
    PredIn pred pop.
Proof.
  induction pop; intros; cbn in *; auto.
  - constructor.
    destruct (PredIn_decidable _ pred (deep_simplify peq pop1) peq); [intuition|].
    destruct (PredIn_decidable _ pred (deep_simplify peq pop2) peq); [intuition|].
    repeat destruct_match; try solve [contradiction | inv H; inv H1; contradiction].
  - constructor.
    destruct (PredIn_decidable _ pred (deep_simplify peq pop1) peq); [intuition|].
    destruct (PredIn_decidable _ pred (deep_simplify peq pop2) peq); [intuition|].
    repeat destruct_match; try solve [contradiction | inv H; inv H1; contradiction].
Qed.
Opaque deep_simplify.

#[local] Transparent simplify.
Lemma simplify_in :
  forall pop (pred: positive),
    PredIn pred (simplify pop) ->
    PredIn pred pop.
Proof.
  induction pop; intros; cbn in *; auto.
  - constructor.
    destruct (PredIn_decidable _ pred (simplify pop1) peq); [intuition|].
    destruct (PredIn_decidable _ pred (simplify pop2) peq); [intuition|].
    repeat destruct_match; try solve [contradiction | inv H; inv H1; contradiction].
  - constructor.
    destruct (PredIn_decidable _ pred (simplify pop1) peq); [intuition|].
    destruct (PredIn_decidable _ pred (simplify pop2) peq); [intuition|].
    repeat destruct_match; try solve [contradiction | inv H; inv H1; contradiction].
Qed.
Opaque simplify.

Lemma map_in_pred :
  forall A B (x: predicated A) f preds (g: A -> B),
    pe_preds_in x preds ->
    (forall pop pred, PredIn pred (f pop) -> PredIn pred pop) ->
    pe_preds_in (NE.map (fun x0 => (f (fst x0), g (snd x0))) x) preds.
Proof.
  induction x.
  - inversion 1; subst. constructor; intros. specialize (H1 pred). apply H1. eauto.
  - intros. inv H. constructor; eauto. eapply IHx; eauto.
Qed.

Lemma map_in_pred2 :
  forall A B (x: predicated A) f preds (g: A -> B),
    pe_preds_in x preds ->
    (forall pop pred, PredIn pred (f pop) -> preds ! pred = Some tt) ->
    pe_preds_in (NE.map (fun x0 => (f (fst x0), g (snd x0))) x) preds.
Proof.
  induction x.
  - intros. inv H. cbn. constructor. intros. cbn in *. eapply H0; eauto.
  - intros. inv H. constructor; eauto. eapply IHx; eauto.
Qed.

Lemma map_in_pred3 :
  forall A B (x: predicated A) f preds (g: A -> B),
    pe_preds_in x preds ->
    (forall pop pred, PredIn pred (f pop) -> PredIn pred pop \/ preds ! pred = Some tt) ->
    pe_preds_in (NE.map (fun x0 => (f (fst x0), g (snd x0))) x) preds.
Proof.
  induction x.
  - intros. inv H. cbn. constructor; intros. cbn in *. eapply H0 in H. inv H; eauto.
  - intros. inv H. constructor; eauto. intros. cbn in H. eapply H0 in H. inv H; eauto.
    eapply IHx; eauto.
Qed.

Lemma map_in_pred4 :
  forall A B (x: predicated A) (f: (pred_op * A) -> (pred_op * B)) preds,
    pe_preds_in x preds ->
    (forall a pop pred, PredIn pred (fst (f (pop, a))) -> PredIn pred pop
      \/ preds ! pred = Some tt) ->
    pe_preds_in (NE.map f x) preds.
Proof.
  induction x.
  - intros. inv H. cbn. constructor; intros. destruct a. apply H0 in H. inv H; auto.
  - intros. inv H. cbn. constructor; intros. destruct a. apply H0 in H. inv H; auto.
    eapply IHx; eauto.
Qed.

Lemma app_in_pred :
  forall A (a b: predicated A) preds,
    pe_preds_in a preds ->
    pe_preds_in b preds ->
    pe_preds_in (NE.app a b) preds.
Proof.
  intros. unfold pe_preds_in in *.
  apply NE.Forall_forall; intros. eapply NE.in_NEapp5 in H1. inv H1.
  - eapply NE.Forall_forall in H; eauto.
  - eapply NE.Forall_forall in H0; eauto.
Qed.

Lemma prune_predicated_in_pred :
  forall A (x y: predicated A) preds,
    prune_predicated x = Some y ->
    pe_preds_in x preds ->
    pe_preds_in y preds.
Proof.
  intros. unfold prune_predicated in *.
  eapply filter_predicated_in_pred in H. eauto.
  eapply map_in_pred with (f := deep_simplify peq) (g := fun x => x); auto.
  apply deep_simplify_in.
Qed.

Lemma predin_negate :
  forall A preds (pred: A),
    PredIn pred preds ->
    PredIn pred (negate preds).
Proof.
  induction preds.
  - cbn. repeat destr. inv Heqp0; intros. inv H. constructor.
  - inversion 1.
  - inversion 1.
  - inversion 1; subst. clear H. inv H1. cbn.
    constructor. eauto. cbn. constructor. eauto.
  - inversion 1; subst. clear H. inv H1. cbn.
    constructor. eauto. cbn. constructor. eauto.
Qed.

Lemma predin_negate2 :
  forall A preds (pred: A),
    PredIn pred (negate preds) ->
    PredIn pred preds.
Proof.
  induction preds.
  - cbn. repeat destr. inv Heqp0; intros. inv H. constructor.
  - inversion 1.
  - inversion 1.
  - inversion 1; subst. clear H. inv H1. cbn.
    constructor. eauto. cbn. constructor. eauto.
  - inversion 1; subst. clear H. inv H1. cbn.
    constructor. eauto. cbn. constructor. eauto.
Qed.

Lemma app_predicated_in_pred :
  forall A (a: predicated A) b p preds,
    pe_preds_in a preds ->
    pe_preds_in b preds ->
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    pe_preds_in (app_predicated p a b) preds.
Proof.
  unfold app_predicated. unfold app_predicated; intros.
  eapply app_in_pred.
  apply map_in_pred3 with (f := (fun x => Pand (negate p) x)) (g := (fun x => x)); auto.
  intros. inv H2. inv H4; auto. right. eapply H1. apply predin_negate2; auto.
  apply map_in_pred3 with (f := (fun x => Pand p x)) (g := (fun x => x)); auto.
  intros. inv H2. inv H4; auto.
Qed.

Lemma predicated_map_in_pred :
  forall A B (a: predicated A) preds (f: A -> B),
    pe_preds_in a preds ->
    pe_preds_in (predicated_map f a) preds.
Proof.
  unfold predicated_map; intros.
  apply map_in_pred with (f := fun x => x) (g := f); auto.
Qed.

(* Lemma non_empty_prod_cons : *)
(*   forall A (a: A) r b, *)
(*     NE.non_empty_prod (NE.cons a r) b = . *)

Lemma map_in_pred5:
  forall A B p preds,
    pe_preds_in (NE.map fst p) preds ->
    pe_preds_in (NE.map snd p) preds ->
    pe_preds_in (NE.map (fun x : Predicate.pred_op * A * (Predicate.pred_op * B) =>
      let (y, y0) := x in let (a, b1) := y in let (c, d) := y0 in (a ∧ c, (b1, d))) p) preds.
Proof.
  induction p; crush; repeat destr.
  - inv H. inv H0. constructor; intros. inv H. inv H3; auto.
  - inv Heqp0. inv H. inv H0. constructor. intros. inv H. inv H1; auto.
    eapply IHp; eauto.
Qed.

Lemma predicated_prod_in_pred :
  forall A B (a: predicated A) (b: predicated B) preds,
    pe_preds_in a preds ->
    pe_preds_in b preds ->
    pe_preds_in (predicated_prod a b) preds.
Proof.
  unfold predicated_prod; induction a; induction b; crush; repeat destr.
  - constructor. cbn. inversion 1; subst. inv H3. inv H. eauto. inv H0; eauto.
  - inv Heqp0. constructor; cbn; intros. inv H1. inv H3. inv H; auto. inv H0; auto.
    inv H0; eauto. eapply IHb; eauto.
  - inv Heqp0. inv H0. inv H. constructor; eauto. cbn; intros. inv H. inv H1; eauto.
    eapply IHa; eauto. constructor. eauto.
  - inv H. inv H0. constructor; cbn; intros. inv H. inv H1; eauto.
    rewrite NE.app_NEmap. apply app_in_pred.
    eapply map_in_pred5.
    { clear IHb. clear IHa. clear H4. clear H2. generalize dependent b.
      induction b; crush.
      - constructor; auto.
      - inv H5. constructor; auto. eapply IHb; eauto.
    }
    { clear IHb. clear IHa. clear H4. clear H2. generalize dependent b.
      induction b; crush.
      inv H5. constructor; auto. eapply IHb; eauto.
    }
    eapply IHa; eauto. constructor; eauto.
Qed.

Lemma seq_app_prod_in_pred :
  forall A B (a: predicated (A -> B)) (b: predicated A) preds,
    pe_preds_in a preds ->
    pe_preds_in b preds ->
    pe_preds_in (seq_app a b) preds.
Proof.
  intros. unfold seq_app. eapply predicated_map_in_pred.
  eapply predicated_prod_in_pred; auto.
Qed.

Lemma cons_pred_expr_in :
  forall a b preds,
    pe_preds_in a preds ->
    pe_preds_in b preds ->
    pe_preds_in (cons_pred_expr a b) preds.
Proof.
  intros. unfold cons_pred_expr. eapply predicated_map_in_pred.
  eapply predicated_prod_in_pred; auto.
Qed.

Lemma cons_fold_in:
  forall n s preds,
    pe_preds_in s preds ->
    NE.Forall (fun n' => pe_preds_in n' preds) n ->
    pe_preds_in (GiblePargenproofEquiv.NE.fold_right cons_pred_expr s n) preds.
Proof.
  induction n; crush.
  - inv H0. eapply cons_pred_expr_in; auto.
  - inv H0. eapply cons_pred_expr_in; auto.
Qed.

Lemma to_list_in :
  forall A l n (x: A),
    NE.of_list l = Some n -> In x l -> NE.In x n.
Proof.
  induction l; crush.
  inv H0. destruct l. inv H. constructor. destr. inv H. constructor; tauto.
  destruct l. inv H1. destr. inv H. inv H1. econstructor. right.
  eapply IHl; auto. constructor. auto. constructor. right. eapply IHl; auto.
  apply in_cons; auto.
Qed.

Lemma to_list_in2 :
  forall A l n (x: A),
    NE.of_list l = Some n -> NE.In x n -> In x l.
Proof.
  induction l; crush.
  inv H0. destruct l. inv H. destr. inv H.
  inv H1; try tauto. right. eapply IHl; eauto.
  destruct l. inv H. tauto.
  destruct_match. inv H. inv H.
Qed.

Lemma merge_preds_in :
  forall a preds,
    Forall (fun x => pe_preds_in x preds) a ->
    pe_preds_in (merge a) preds.
Proof.
  unfold merge; intros. destruct_match; cbn.
  - eapply cons_fold_in; auto. constructor. inversion 1.
    apply NE.Forall_forall; intros. eapply Forall_forall in H.
    2: { eapply to_list_in2; eauto. } auto.
  - constructor; inversion 1.
Qed.

Lemma list_translation_in :
  forall f preds,
    all_preds_in f preds ->
    forall args, Forall (fun x : predicated expression => pe_preds_in x preds) (list_translation args f).
Proof.
  induction args.
  - cbn. constructor.
  - cbn. constructor; auto. unfold all_preds_in in H. eapply H.
Qed.

Lemma pe_preds_in_fold:
  forall A l preds x,
    pe_preds_in x preds ->
    @pe_preds_in A x (fold_right (fun x0 : positive => PTree.set x0 tt) preds l).
Proof.
  unfold pe_preds_in; intros. apply NE.Forall_forall; intros.
  eapply NE.Forall_forall in H; eauto. apply gather_predicates_fold; eauto.
Qed.

Lemma pe_preds_in_fold2:
  forall A l preds x y,
    pe_preds_in x preds ->
    @pe_preds_in A x (PTree.set y tt (fold_right (fun x0 : positive => PTree.set x0 tt) preds l)).
Proof.
  unfold pe_preds_in; intros. apply NE.Forall_forall; intros.
  eapply NE.Forall_forall in H; eauto.
  destruct (peq pred y); subst; [rewrite PTree.gss; auto | rewrite PTree.gso by auto].
  apply gather_predicates_fold; eauto.
Qed.

Lemma pe_preds_in3:
  forall A preds x y,
    pe_preds_in x preds ->
    @pe_preds_in A x (PTree.set y tt preds).
Proof.
  unfold pe_preds_in; intros. apply NE.Forall_forall; intros.
  destruct (peq pred y); subst; [rewrite PTree.gss; auto | rewrite PTree.gso by auto].
  eapply NE.Forall_forall in H; eauto.
Qed.

Lemma pred_in_pred_uses:
  forall A (p: A) pop,
    PredIn p pop ->
    In p (predicate_use pop).
Proof.
  induction pop; crush.
  - destr. inv Heqp1. inv H. now constructor.
  - inv H.
  - inv H.
  - apply in_or_app. inv H. inv H1; intuition.
  - apply in_or_app. inv H. inv H1; intuition.
Qed.

Lemma pe_preds_in_flap2:
  forall A B C f a b preds,
    pe_preds_in f preds ->
    pe_preds_in (@flap2 A B C f a b) preds.
Proof.
  unfold flap2; intros.
  eapply map_in_pred4; auto.
Qed.

Definition option_predicate_use (p: option pred_op) :=
  match p with
  | Some p' => predicate_use p'
  | None => nil
  end.

#[local] Opaque seq_app.
Lemma gather_predicates_RBop :
  forall p f pred op args dst p' f' preds preds',
    update (p, f) (RBop pred op args dst) = Some (p', f') ->
    gather_predicates preds (RBop pred op args dst) = Some preds' ->
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    all_preds_in f preds ->
    all_preds_in f' preds'.
Proof.
  intros. cbn in *. unfold Option.bind in *; generalize dependent H;
  repeat destr; intros H. inv H.
  inv H0. unfold all_preds_in in *; intros.
  apply NE.Forall_forall; intros.
  assert (YX: (fold_right (fun x : positive => PTree.set x tt) preds (option_predicate_use pred)) = preds').
  { destruct pred. cbn. inv H3; auto. cbn. inv H3. auto. } subst.
  clear H3.
  destruct (resource_eq (Reg dst) x).
  { subst. rewrite forest_reg_gss in H.
    eapply prune_predicated_in_pred in Heqo.
    instantiate (1:=(fold_right (fun x : positive => PTree.set x tt) preds (option_predicate_use pred))) in Heqo.
    unfold pe_preds_in in Heqo. eapply NE.Forall_forall in Heqo; eauto.
    eapply app_predicated_in_pred.
    eapply pe_preds_in_fold.
    specialize (H2 (Reg dst)). unfold pe_preds_in.
    apply NE.Forall_forall; intros. eapply NE.Forall_forall in H2; eauto.
    eapply seq_app_prod_in_pred. unfold pred_ret. constructor; inversion 1.
    eapply pe_preds_in_fold.
    eapply merge_preds_in.
    apply list_translation_in.
    eauto.
    intros. inv H3. inv H5.
    eapply gather_predicates_fold2; eauto.
    destruct pred; cbn in *. apply pred_in_pred_uses; auto. inv H3.
    eapply gather_predicates_fold; eauto.
  }
  rewrite forest_reg_gso in H by auto.
  apply gather_predicates_fold; auto.
  specialize (H2 x). eapply NE.Forall_forall in H2; eauto.
Qed.

Lemma gather_predicates_RBload :
  forall p f pred chunk addr args dst p' f' preds preds',
    update (p, f) (RBload pred chunk addr args dst) = Some (p', f') ->
    gather_predicates preds (RBload pred chunk addr args dst) = Some preds' ->
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    all_preds_in f preds ->
    all_preds_in f' preds'.
Proof.
  intros. cbn in *. unfold Option.bind in *; generalize dependent H;
  repeat destr; intros H. inv H.
  inv H0. unfold all_preds_in in *; intros.
  apply NE.Forall_forall; intros.
  assert (YX: (fold_right (fun x : positive => PTree.set x tt) preds (option_predicate_use pred)) = preds').
  { destruct pred. cbn. inv H3; auto. cbn. inv H3. auto. } subst.
  clear H3.
  destruct (resource_eq (Reg dst) x).
  { subst. rewrite forest_reg_gss in H.
    eapply prune_predicated_in_pred in Heqo.
    instantiate (1:=(fold_right (fun x : positive => PTree.set x tt) preds (option_predicate_use pred))) in Heqo.
    unfold pe_preds_in in Heqo. eapply NE.Forall_forall in Heqo; eauto.
    eapply app_predicated_in_pred.
    eapply pe_preds_in_fold.
    specialize (H2 (Reg dst)). unfold pe_preds_in.
    apply NE.Forall_forall; intros. eapply NE.Forall_forall in H2; eauto.
    eapply seq_app_prod_in_pred.
    eapply seq_app_prod_in_pred.
    unfold pred_ret. constructor; inversion 1.
    eapply pe_preds_in_fold.
    eapply merge_preds_in.
    apply list_translation_in. eauto.
    unfold pe_preds_in; intros. eapply NE.Forall_forall; intros.
    specialize (H2 Mem). eapply NE.Forall_forall in H2; eauto.
    eapply gather_predicates_fold; eauto.
    intros. inv H3. inv H5.
    eapply gather_predicates_fold2; eauto.
    destruct pred; cbn in *; [apply pred_in_pred_uses; auto | inversion H3].
    eapply gather_predicates_fold; eauto.
  }
  rewrite forest_reg_gso in H by auto.
  apply gather_predicates_fold; auto.
  specialize (H2 x). eapply NE.Forall_forall in H2; eauto.
Qed.

Lemma gather_predicates_RBstore :
  forall p f pred chunk addr args src p' f' preds preds',
    update (p, f) (RBstore pred chunk addr args src) = Some (p', f') ->
    gather_predicates preds (RBstore pred chunk addr args src) = Some preds' ->
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    all_preds_in f preds ->
    all_preds_in f' preds'.
Proof.
  intros. cbn in *. unfold Option.bind in *; generalize dependent H;
  repeat destr; intros H. inv H.
  inv H0. unfold all_preds_in in *; intros.
  apply NE.Forall_forall; intros.
  assert (YX: (fold_right (fun x : positive => PTree.set x tt) preds (option_predicate_use pred)) = preds').
  { destruct pred. cbn. inv H3; auto. cbn. inv H3. auto. } subst.
  clear H3.
  destruct (resource_eq Mem x).
  { subst. rewrite forest_reg_gss in H.
    eapply prune_predicated_in_pred in Heqo.
    instantiate (1:=(fold_right (fun x : positive => PTree.set x tt) preds (option_predicate_use pred))) in Heqo.
    unfold pe_preds_in in Heqo. eapply NE.Forall_forall in Heqo; eauto.
    eapply app_predicated_in_pred.
    eapply pe_preds_in_fold.
    specialize (H2 Mem). unfold pe_preds_in.
    apply NE.Forall_forall; intros. eapply NE.Forall_forall in H2; eauto.
    eapply seq_app_prod_in_pred.
    eapply seq_app_prod_in_pred.
    apply pe_preds_in_flap2.
    eapply seq_app_prod_in_pred.
    unfold pred_ret. constructor; inversion 1.
    eapply pe_preds_in_fold. eapply H2.
    eapply pe_preds_in_fold.
    eapply merge_preds_in.
    apply list_translation_in. eauto.
    eapply pe_preds_in_fold. eapply H2.
    intros. inv H3. inv H5.
    eapply gather_predicates_fold2; eauto.
    destruct pred; cbn in *; [apply pred_in_pred_uses; auto | inversion H3].
    eapply gather_predicates_fold; eauto.
  }
  rewrite forest_reg_gso in H by auto.
  apply gather_predicates_fold; auto.
  specialize (H2 x). eapply NE.Forall_forall in H2; eauto.
Qed.

Lemma gather_predicates_RBsetpred :
  forall p f pred args cond pset p' f' preds preds',
    update (p, f) (RBsetpred pred cond args pset) = Some (p', f') ->
    gather_predicates preds (RBsetpred pred cond args pset) = Some preds' ->
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    all_preds_in f preds ->
    all_preds_in f' preds'.
Proof.
  intros. cbn in *. unfold Option.bind in *; generalize dependent H;
  repeat destr; inversion 1; subst; clear H.
  inv H0. unfold all_preds_in in *; intros. destruct pred; cbn in *;
  rewrite forest_pred_reg; auto.
  eapply pe_preds_in_fold2. eapply H2.
  eapply pe_preds_in3. eapply H2.
Qed.

Lemma forest_exit_regs :
  forall f n r,
    (f <-e n) #r r = f #r r.
Proof.
  unfold "<-e", "#r"; intros.
  repeat destruct_match; crush.
Qed.

Lemma gather_predicates_RBexit :
  forall p f pred cf p' f' preds preds',
    update (p, f) (RBexit pred cf) = Some (p', f') ->
    gather_predicates preds (RBexit pred cf) = Some preds' ->
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    all_preds_in f preds ->
    all_preds_in f' preds'.
Proof.
  intros. cbn in *. unfold Option.bind in *; generalize dependent H;
  repeat destr; inversion 1; subst; clear H.
  inv H0. unfold all_preds_in in *; intros. destruct pred; cbn in *. inv H3.
  rewrite forest_exit_regs; auto.
  eapply pe_preds_in_fold. eapply H2.
  inv H3. rewrite forest_exit_regs. auto.
Qed.

Transparent seq_app.

Lemma gather_predicates_in_forest :
  forall p i f p' f' preds preds',
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    update (p, f) i = Some (p', f') ->
    gather_predicates preds i = Some preds' ->
    all_preds_in f preds ->
    all_preds_in f' preds'.
Proof.
  intros. destruct i.
  - inv H0; inv H1; auto.
  - eapply gather_predicates_RBop; eauto.
  - eapply gather_predicates_RBload; eauto.
  - eapply gather_predicates_RBstore; eauto.
  - eapply gather_predicates_RBsetpred; eauto.
  - eapply gather_predicates_RBexit; eauto.
Qed.

Lemma gather_predicates_update_constant :
  forall p f i p' f' preds preds',
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    gather_predicates preds i = Some preds' ->
    update (p, f) i = Some (p', f') ->
    (forall in_pred, PredIn in_pred p' -> preds' ! in_pred = Some tt).
Proof.
  intros. destruct i; try solve [exploit gather_predicates_in; eauto; cbn in *;
  unfold Option.bind in *; repeat destr; inv H0; inv H1; try (eapply H; eauto)].
  cbn in *; unfold Option.bind in *; repeat destr. inv H1. apply simplify_in in H2.
  inv H2. inv H3.
  - destruct o; cbn in *; [|inv H1]. inv H0. apply predin_negate2 in H1.
    eapply gather_predicates_fold2. now apply pred_in_pred_uses.
  - exploit gather_predicates_in; eauto. instantiate (1:=RBexit o c); auto.
Qed.

Lemma sem_pexpr_eval_predin:
  forall G pr ps ps' (ctx: @Abstr.ctx G) b,
    (forall pred, PredIn pred pr -> ps' ! pred = ps ! pred) ->
    sem_pexpr ctx (from_pred_op ps' pr) b ->
    sem_pexpr ctx (from_pred_op ps pr) b.
Proof.
  induction pr; intros.
  - cbn in *; repeat destr. inv Heqp0.
    destruct (ps' ! p0) eqn:HPS'.
    + assert (HPS: ps ! p0 = Some p).
      { erewrite <- H; auto. constructor. }
      unfold get_forest_p' in *. rewrite HPS' in *. rewrite HPS in *. assumption.
    + assert (HPS: ps ! p0 = None).
      { erewrite <- H; auto. constructor. }
      unfold get_forest_p' in *. rewrite HPS' in *. rewrite HPS in *. assumption.
  - inversion H0. constructor.
  - inversion H0. constructor.
  - inversion_clear H0; subst; [inversion_clear H1; subst|].
    + assert (sem_pexpr ctx (from_pred_op ps pr1) false).
      eapply IHpr1; [|eassumption]. intros. eapply H. constructor; tauto.
      constructor; tauto.
    + assert (sem_pexpr ctx (from_pred_op ps pr2) false).
      eapply IHpr2; [|eassumption]. intros. eapply H. constructor; tauto.
      constructor; tauto.
    + apply IHpr1 with (ps:=ps) in H1.
      apply IHpr2 with (ps:=ps) in H2.
      constructor; auto.
      intros. apply H. constructor; auto.
      intros. apply H. constructor; auto.
  - inversion_clear H0; subst; [inversion_clear H1; subst|].
    + assert (sem_pexpr ctx (from_pred_op ps pr1) true).
      eapply IHpr1; [|eassumption]. intros. eapply H. constructor; tauto.
      constructor; tauto.
    + assert (sem_pexpr ctx (from_pred_op ps pr2) true).
      eapply IHpr2; [|eassumption]. intros. eapply H. constructor; tauto.
      constructor; tauto.
    + apply IHpr1 with (ps:=ps) in H1.
      apply IHpr2 with (ps:=ps) in H2.
      constructor; auto.
      intros. apply H. constructor; auto.
      intros. apply H. constructor; auto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval_sem :
  forall A B G a_sem pe ps i0 sp ge pe_val ps',
    @sem_pred_expr G A B ps' a_sem (mk_ctx i0 sp ge) pe pe_val ->
    NE.Forall (fun x => forall pred, PredIn pred (fst x) -> ps' ! pred = ps ! pred) pe ->
    sem_pred_expr ps a_sem (mk_ctx i0 sp ge) pe pe_val.
Proof.
  induction pe as [a | a pe Hpe ]; intros * HSEM HFORALL.
  - inv HSEM. constructor; auto. inversion_clear HFORALL.
    eapply sem_pexpr_eval_predin; eassumption.
  - inv HFORALL. destruct a. cbn [fst snd] in *. inversion_clear HSEM; subst.
    + econstructor; auto. eapply sem_pexpr_eval_predin; eassumption.
    + apply sem_pred_expr_cons_false; auto. eapply sem_pexpr_eval_predin; eassumption.
      eauto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_sem2 :
  forall x p f i p' f' preds preds',
    update (p, f) i = Some (p', f') ->
    gather_predicates preds i = Some preds' ->
    preds ! x = Some tt ->
    f.(forest_preds) ! x = f'.(forest_preds) ! x.
Proof.
  intros.
  exploit gather_predicates_in. eauto. eauto. intros HIN.
  destruct i; intros; cbn in *;
    unfold Option.bind, Option.ret, Option.bind2 in *; generalize H;
    repeat destr; cbn in *; inversion_clear 1; subst; cbn in *; auto.
  inversion_clear H; destruct o; auto.
  - destruct (peq p0 x); subst.
    + inv H0. eapply gather_predicates_fold in H1. rewrite H1 in Heqo2. discriminate.
    + rewrite PTree.gso by auto; auto.
  - destruct (peq p0 x); subst.
    { rewrite H1 in Heqo2. inversion Heqo2. }
    rewrite PTree.gso by auto; auto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval3'' :
  forall A B G a_sem instrs p f p' f' i0 sp ge preds preds' pe pe_val,
    update (p, f) instrs = Some (p', f') ->
    gather_predicates preds instrs = Some preds' ->
    @sem_pred_expr G A B f'.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val ->
    NE.Forall (fun x => forall pred, PredIn pred (fst x) -> preds ! pred = Some tt) pe ->
    sem_pred_expr f.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val.
Proof.
  intros * YFUP YFGATH YSEM YFRL.
  eapply abstr_seq_revers_correct_fold_sem_pexpr_eval_sem. { eassumption. }
  apply NE.Forall_forall. intros [pe_op a] YIN pred_tmp YPREDIN.
  apply NE.Forall_forall with (x:=(pe_op, a)) in YFRL; auto.
  specialize (YFRL pred_tmp YPREDIN).
  cbn [fst snd] in *.
  symmetry. eapply abstr_seq_revers_correct_fold_sem_pexpr_sem2; eauto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval3' :
  forall A B G a_sem instrs p f p' f' i0 sp ge preds preds' pe pe_val l l' lm lm',
    update' (p, f, l, lm) instrs = Some (p', f', l', lm') ->
    gather_predicates preds instrs = Some preds' ->
    @sem_pred_expr G A B f'.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val ->
    NE.Forall (fun x => forall pred, PredIn pred (fst x) -> preds ! pred = Some tt) pe ->
    sem_pred_expr f.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val.
Proof.
  intros.
  unfold update', Option.bind2, Option.ret in H; repeat destr.
  inversion H; subst.
  eapply abstr_seq_revers_correct_fold_sem_pexpr_eval3''; eauto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval3 :
  forall A B G a_sem instrs p f l p' f' l' i0 sp ge preds preds' pe pe_val lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left gather_predicates instrs (Some preds) = Some preds' ->
    @sem_pred_expr G A B f'.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val ->
    NE.Forall (fun x => forall pred, PredIn pred (fst x) -> preds ! pred = Some tt) pe ->
    sem_pred_expr f.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val.
Proof.
  induction instrs; [crush|].
  intros. cbn -[update] in H,H0.
  exploit OptionExtra.mfold_left_Some. eapply H. intros [[[[p_mid f_mid] l_mid] lm_mid] HBind].
  rewrite HBind in H.
  exploit OptionExtra.mfold_left_Some. eapply H0. intros [preds_mid HGATHER].
  rewrite HGATHER in H0.
  exploit IHinstrs; eauto.
  apply NE.Forall_forall. intros [p_op aval] YIN ypred YPREDIN.
  apply NE.Forall_forall with (x:=(p_op, aval)) in H2; auto. cbn [fst snd] in *.
  specialize (H2 ypred YPREDIN).
  eapply gather_predicates_in; eassumption.
  intros HSEM.
  eapply abstr_seq_revers_correct_fold_sem_pexpr_eval3'; eauto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval2 :
  forall G instrs p f l p' f' l' i0 sp ge preds preds' pe lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left gather_predicates instrs (Some preds) = Some preds' ->
    @evaluable_pred_expr G (mk_ctx i0 sp ge) f'.(forest_preds) pe ->
    NE.Forall (fun x => forall pred, PredIn pred (fst x)
                 -> PTree.get pred preds = Some tt) pe ->
    evaluable_pred_expr (mk_ctx i0 sp ge) f.(forest_preds) pe.
Proof.
  unfold evaluable_pred_expr in *.
  intros. inv H1. exists x.
  eapply abstr_seq_revers_correct_fold_sem_pexpr_eval3; eauto.
Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval4 :
  forall G instrs p f l p' f' l' i0 sp ge preds preds' pe lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left gather_predicates instrs (Some preds) = Some preds' ->
    @evaluable_pred_expr_m G (mk_ctx i0 sp ge) f'.(forest_preds) pe ->
    NE.Forall (fun x => forall pred, PredIn pred (fst x)
                 -> PTree.get pred preds = Some tt) pe ->
    evaluable_pred_expr_m (mk_ctx i0 sp ge) f.(forest_preds) pe.
Proof.
  unfold evaluable_pred_expr in *.
  intros. inv H1. exists x.
  eapply abstr_seq_revers_correct_fold_sem_pexpr_eval3; eauto.
Qed.

Lemma state_lessdef_state_equiv :
  forall x y, state_lessdef x y <-> state_equiv x y.
Proof. split; intros; inv H; constructor; auto. Qed.

Lemma abstr_seq_revers_correct_fold_sem_pexpr :
  forall instrs p f l p' f' l' preds preds' lm lm',
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left gather_predicates instrs (Some preds) = Some preds' ->
    forall pred, preds ! pred = Some tt ->
      f #p pred = f' #p pred.
Proof.
  induction instrs; try solve [crush].
  intros. cbn -[update] in *.
  exploit OptionExtra.mfold_left_Some. apply H. intros [[[[p_mid f_mid] l_mid] lm_mid] HBIND].
  exploit OptionExtra.mfold_left_Some. apply H0. intros [ptree_mid HGATHER].
  rewrite HBIND in H. rewrite HGATHER in H0.
  exploit IHinstrs; eauto. eapply gather_predicates_in; eauto.
  intros. rewrite <- H2.
  unfold "#p". unfold get_forest_p'. erewrite abstr_seq_revers_correct_fold_sem_pexpr_sem2; eauto.
  unfold Option.bind2, Option.ret in *. repeat destr. inv Heqp1. inv HBIND. eauto.
Qed.

(*|
This lemma states that predicates are always evaluable, given that the output
forest is also evaluable.  This is true because gather_predicates ensures that
all predicates are encountered are never assigned again.  Therefore, throughout
the evaluation of the forest, one knows that syntactically the predicate will
stay the same.  This further means that the symbol representation stays the
same, and that the evaluation therefore has to be the same.
|*)

Lemma update_rev_gather_constant:
  forall G i preds i0 sp ge f p l lm p' f' l' lm' preds' ps,
    (forall p, preds ! p = None -> @sem_pexpr G (mk_ctx i0 sp ge) (f #p p) (ps !! p)) ->
    update' (p, f, l, lm) i = Some (p', f', l', lm') ->
    gather_predicates preds i = Some preds' ->
    (forall p, preds' ! p = None -> sem_pexpr (mk_ctx i0 sp ge) (f' #p p) (ps !! p)).
Proof.
  unfold update', gather_predicates; destruct i; intros; unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr.
  - inv H0. inv H1. inv Heqo. eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. destruct o. inv H1. eapply gather_predicates_fold3 in H2. eauto. inv H1; eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. inv Heqo0. destruct o. inv H1. eapply gather_predicates_fold3 in H2.
    eauto. inv H1; eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. inv Heqo0. destruct o. inv H1. eapply gather_predicates_fold3 in H2.
    eauto. inv H1; eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *. repeat destr. inv Heqo1. inv H4.
    destruct (peq p1 p); subst. inv H1. rewrite PTree.gss in H2. discriminate.
    rewrite forest_pred_gso by auto. inv H1. rewrite PTree.gso in H2 by auto.
    destruct o. eapply gather_predicates_fold3 in H2. eauto. eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. inv Heqo0. destruct o. inv H1. eapply gather_predicates_fold3 in H2.
    eauto. inv H1; eauto.
Qed.

Lemma update_rev_gather_constant2:
  forall G i preds i0 sp ge f p l lm p' f' l' lm' preds' ps,
    (forall p, preds ! p = None -> @sem_pexpr G (mk_ctx i0 sp ge) (f #p p) ps) ->
    update' (p, f, l, lm) i = Some (p', f', l', lm') ->
    gather_predicates preds i = Some preds' ->
    (forall p, preds' ! p = None -> sem_pexpr (mk_ctx i0 sp ge) (f' #p p) ps).
Proof.
  unfold update', gather_predicates; destruct i; intros; unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr.
  - inv H0. inv H1. inv Heqo. eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. destruct o. inv H1. eapply gather_predicates_fold3 in H2. eauto. inv H1; eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. inv Heqo0. destruct o. inv H1. eapply gather_predicates_fold3 in H2.
    eauto. inv H1; eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. inv Heqo0. destruct o. inv H1. eapply gather_predicates_fold3 in H2.
    eauto. inv H1; eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *. repeat destr. inv Heqo1. inv H4.
    destruct (peq p1 p); subst. inv H1. rewrite PTree.gss in H2. discriminate.
    rewrite forest_pred_gso by auto. inv H1. rewrite PTree.gso in H2 by auto.
    destruct o. eapply gather_predicates_fold3 in H2. eauto. eauto.
  - inv H0. cbn in *. unfold Option.bind, Option.bind2, Option.ret in *;
    repeat destr; inv Heqo1; inv H4. inv Heqo0. destruct o. inv H1. eapply gather_predicates_fold3 in H2.
    eauto. inv H1; eauto.
Qed.

Definition PMapmap {A} (f: positive -> A -> A) (m: PMap.t A): PMap.t A :=
  (fst m, PTree.map f (snd m)).

Definition mask_pred_map (preds: PTree.t unit) (initial_map after_map: PMap.t bool): PMap.t bool :=
  PMapmap (fun i a =>
    match preds ! i with
    | Some _ => a
    | None => initial_map !! i
    end) after_map.

Lemma abstr_seq_revers_correct_fold_sem_pexpr_eval :
  forall G instrs p f l p' f' l' i0 sp ge preds preds' ps' lm lm',
    (forall p, preds ! p = None -> sem_pexpr (mk_ctx i0 sp ge) (f #p p) ((is_ps i0) !! p)) ->
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left gather_predicates instrs (Some preds) = Some preds' ->
    sem_predset (@mk_ctx G i0 sp ge) f' ps' ->
    exists ps, sem_predset (mk_ctx i0 sp ge) f ps.
Proof.
  induction instrs.
  - intros * YH **. cbn in *. inv H. inv H0. eauto.
  - intros * YH **. cbn -[update] in *.
    exploit OptionExtra.mfold_left_Some. apply H. intros [[[[p_mid f_mid] l_mid] lm_mid] HBIND].
    exploit OptionExtra.mfold_left_Some. apply H0. intros [ptree_mid HGATHER].
    rewrite HBIND in H. rewrite HGATHER in H0.
    exploit IHinstrs. 2: { eauto. } 2: { eauto. } eapply update_rev_gather_constant; eauto.
    eauto.
    intros [ps_mid HSEM_MID].
    (* destruct (preds ! p0) eqn:?. destruct u. eapply gather_predicates_in in HGATHER; eauto. *)
    (* rewrite HGATHER in H2. discriminate. *)
    unfold Option.bind2, Option.bind, Option.ret in *; repeat destr. inv HBIND.
    destruct a; cbn in *.
    + inv Heqo. inv HGATHER. eauto.
    + unfold Option.bind2, Option.bind, Option.ret in *; repeat destr.
      generalize dependent Heqo; repeat destr; intros Heqo; inv Heqo.
      inv HSEM_MID.
      econstructor. constructor; eauto.
    + unfold Option.bind2, Option.bind, Option.ret in *; repeat destr.
      generalize dependent Heqo; repeat destr; intros Heqo; inv Heqo.
      inv HSEM_MID.
      econstructor. constructor; eauto.
    + unfold Option.bind2, Option.bind, Option.ret in *; repeat destr.
      generalize dependent Heqo; repeat destr; intros Heqo; inv Heqo.
      inv HSEM_MID.
      econstructor. constructor; eauto.
    + unfold Option.bind2, Option.bind, Option.ret in *; repeat destr. inv HGATHER.
      generalize dependent Heqo; repeat destr; intros Heqo; inv Heqo.
      exists (mask_pred_map preds (is_ps i0) ps_mid).
      econstructor; intros.
      destruct (peq x p0); subst.
      * admit.
      * inv HSEM_MID. specialize (H2 x). rewrite forest_pred_gso in H2 by auto.
    + unfold Option.bind2, Option.bind, Option.ret in *; repeat destr.
      generalize dependent Heqo; repeat destr; intros Heqo; inv Heqo.
      inv HSEM_MID.
      econstructor. constructor; eauto.
Qed.

(* [[id:5e6486bb-fda2-4558-aed8-243a9698de85]] *)
Lemma abstr_seq_reverse_correct_fold :
  forall sp instrs i0 i i' ti cf f' l p p' l' f preds preds' lm lm' ps',
    (forall in_pred, PredIn in_pred p -> preds ! in_pred = Some tt) ->
    valid_mem (is_mem i0) (is_mem i) ->
    all_preds_in f preds ->
    eval_predf (is_ps i) p = true ->
    sem (mk_ctx i0 sp ge) f (i, None) ->
    mfold_left update' instrs (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left gather_predicates instrs (Some preds) = Some preds' ->
    evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) l' ->
    evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) lm' ->
    sem_predset (mk_ctx i0 sp ge) f' ps' ->
    sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
    state_lessdef i ti ->
    exists ti',
      SeqBB.step ge sp (Iexec ti) instrs (Iterm ti' cf)
      /\ state_lessdef i' ti'.
Proof.
  induction instrs; intros * YPREDSIN YVALID YALL YEVAL Y3 Y YGATHER Y0 YEVALUABLE YSEM_FINAL Y1 Y2.
  - cbn in *. inv Y.
    assert (X: similar {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |}
                       {| ctx_is := i0; ctx_sp := sp; ctx_ge := ge |})
      by reflexivity.
    now eapply sem_det in X; [| exact Y1 | exact Y3 ].
  - cbn -[update] in Y.
    pose proof Y as YX.
    apply OptionExtra.mfold_left_Some in YX. inv YX.
    cbn in YGATHER.
    pose proof YGATHER as YX.
    apply OptionExtra.mfold_left_Some in YX. inv YX. rewrite H0 in YGATHER.
    pose proof H0 as YGATHER_SINGLE. clear H0.
    rewrite H in Y.
    destruct x as ((p_mid & f_mid) & l_mid).
    unfold Option.bind2, Option.ret in H. repeat destr.
    inv H.

    destruct a.
    + cbn in Heqo. inv Heqo. cbn in YGATHER_SINGLE. inv YGATHER_SINGLE.
      exploit IHinstrs; eauto; simplify.
      exists x; split; auto. econstructor. constructor. auto.
    + exploit evaluable_pred_expr_exists_RBop; eauto.
      eapply abstr_seq_revers_correct_fold_sem_pexpr_eval2; eauto.
      unfold evaluable_pred_list in Y0. eapply in_forest_evaluable; eauto.
      eapply gather_predicates_in_forest in YALL; eauto.
      unfold all_preds_in in YALL. eauto.
      intros [ti_mid HSTEP].

      pose proof Y3 as YH.
      pose proof HSTEP as YHSTEP.
      pose proof Y2 as Y2SPLIT; inv Y2SPLIT.
      eapply step_exists in YHSTEP.
      2: { symmetry. econstructor; try eassumption; auto. }
      inv YHSTEP. inv H1.
      exploit sem_update_instr. auto. eauto. eauto. eauto. eauto. auto. intros.
      exploit IHinstrs. 5: { eauto. } eapply gather_predicates_update_constant; eauto.
      cbn in YVALID. transitivity m'; auto.
      replace m' with (is_mem {| is_rs := rs; Gible.is_ps := ps; Gible.is_mem := m' |}) by auto.
      eapply sem_update_valid_mem; eauto.
      eapply gather_predicates_in_forest; eauto.
      eapply eval_predf_update_true; eauto.
      eauto. eauto. eauto. eauto. eauto. eauto. symmetry.
      eapply state_lessdef_state_equiv; eauto.
      intros [ti' [YHH HLD]].
      exists ti'; split; eauto. econstructor; eauto.
    + exploit evaluable_pred_expr_exists_RBload; eauto.
      eapply abstr_seq_revers_correct_fold_sem_pexpr_eval2; eauto.
      unfold evaluable_pred_list in Y0. eapply in_forest_evaluable; eauto.
      eapply gather_predicates_in_forest in YALL; eauto.
      unfold all_preds_in in YALL. eauto.
      intros [ti_mid HSTEP].

      pose proof Y3 as YH.
      pose proof HSTEP as YHSTEP.
      pose proof Y2 as Y2SPLIT; inv Y2SPLIT.
      eapply step_exists in YHSTEP.
      2: { symmetry. econstructor; try eassumption; auto. }
      inv YHSTEP. inv H1.
      exploit sem_update_instr. auto. eauto. eauto. eauto. eauto. auto. intros.
      exploit IHinstrs. 5: { eauto. } eapply gather_predicates_update_constant; eauto.
      cbn in YVALID. transitivity m'; auto.
      replace m' with (is_mem {| is_rs := rs; Gible.is_ps := ps; Gible.is_mem := m' |}) by auto.
      eapply sem_update_valid_mem; eauto.
      eapply gather_predicates_in_forest; eauto.
      eapply eval_predf_update_true; eauto.
      eauto. eauto. eauto. eauto. eauto. eauto. symmetry.
      eapply state_lessdef_state_equiv; eauto.
      intros [ti' [YHH HLD]].
      exists ti'; split; eauto. econstructor; eauto.
    + exploit evaluable_pred_expr_exists_RBstore; eauto.
      eapply abstr_seq_revers_correct_fold_sem_pexpr_eval4; eauto.
      unfold evaluable_pred_list in Y0. eapply in_forest_evaluable_m; eauto.
      eapply gather_predicates_in_forest in YALL; eauto.
      unfold all_preds_in in YALL. eauto.
      intros [ti_mid HSTEP].

      pose proof Y3 as YH.
      pose proof HSTEP as YHSTEP.
      pose proof Y2 as Y2SPLIT; inv Y2SPLIT.
      eapply step_exists in YHSTEP.
      2: { symmetry. econstructor; try eassumption; auto. }
      inv YHSTEP. inv H1.
      exploit sem_update_instr. auto. eauto. eauto. eauto. eauto. auto. intros.
      exploit IHinstrs. 5: { eauto. } eapply gather_predicates_update_constant; eauto.
      cbn in YVALID. transitivity m'; auto.
      replace m' with (is_mem {| is_rs := rs; Gible.is_ps := ps; Gible.is_mem := m' |}) by auto.
      eapply sem_update_valid_mem; eauto.
      eapply gather_predicates_in_forest; eauto.
      eapply eval_predf_update_true; eauto.
      eauto. eauto. eauto. eauto. eauto. eauto. symmetry.
      eapply state_lessdef_state_equiv; eauto.
      intros [ti' [YHH HLD]].
      exists ti'; split; eauto. econstructor; eauto.
    + exploit abstr_seq_revers_correct_fold_sem_pexpr_eval; eauto. admit. intros [ps_mid HPRED2].
      exploit evaluable_pred_expr_exists_RBsetpred; eauto.
      intros [ti_mid HSTEP].

      pose proof Y3 as YH.
      pose proof HSTEP as YHSTEP.
      pose proof Y2 as Y2SPLIT; inv Y2SPLIT.
      eapply step_exists in YHSTEP.
      2: { symmetry. econstructor; try eassumption; auto. }
      inv YHSTEP. inv H1.
      exploit sem_update_instr. auto. eauto. eauto. eauto. eauto. auto. intros.
      exploit IHinstrs. 5: { eauto. } eapply gather_predicates_update_constant; eauto.
      cbn in YVALID. transitivity m'; auto.
      replace m' with (is_mem {| is_rs := rs; Gible.is_ps := ps; Gible.is_mem := m' |}) by auto.
      eapply sem_update_valid_mem; eauto.
      eapply gather_predicates_in_forest; eauto.
      eapply eval_predf_update_true; eauto.
      eauto. eauto. eauto. eauto. eauto. eauto. symmetry.
      eapply state_lessdef_state_equiv; eauto.
      intros [ti' [YHH HLD]].
      exists ti'; split; eauto. econstructor; eauto.
    + case_eq (eval_predf (is_ps i) (dfltp o)); intros.
      * exploit evaluable_pred_expr_exists_RBexit2; eauto; intros HSTEP.
        instantiate (1:=c) in HSTEP.
        instantiate (1:=sp) in HSTEP.
        exploit evaluable_pred_expr_exists_RBexit3. eauto. eauto. intros.
        pose proof (state_lessdef_state_equiv i ti). inv H1.
        specialize (H2 Y2).
        pose proof (step_exists_Iterm ge sp ti _ i _ HSTEP
                      ltac:(symmetry; assumption)).
        exploit sem_update_instr_term; eauto; intros. inv H4.
        exploit abstr_fold_falsy; auto. eauto. eapply equiv_update; eauto. cbn. auto.
        intros. eapply sem_det in Y1; eauto. inv Y1. inv H7.
        eexists. split. constructor. eauto. transitivity i.
        symmetry; auto. auto. reflexivity.
      * exploit evaluable_pred_expr_exists_RBexit; eauto; intros HSTEP.
        instantiate (1:=c) in HSTEP. instantiate (1:=sp) in HSTEP.
        pose proof Y3 as YH.
        pose proof HSTEP as YHSTEP.
        pose proof Y2 as Y2SPLIT; inv Y2SPLIT.
        eapply step_exists in YHSTEP.
        2: { symmetry. econstructor; try eassumption; auto. }
        inv YHSTEP. inv H2.
        exploit sem_update_instr. auto. eauto. eauto. eauto. eapply Heqo. eauto. auto. intros.
        exploit IHinstrs. 5: { eauto. } eapply gather_predicates_update_constant; eauto.
        cbn in YVALID. transitivity m'; auto.
        replace m' with (is_mem {| is_rs := rs; Gible.is_ps := ps; Gible.is_mem := m' |}) by auto.
        cbn. inv H4.
        reflexivity.
        eapply gather_predicates_in_forest; eauto.
        eapply eval_predf_update_true; eauto.
        eauto. eauto. eauto. eauto. eauto. eauto. symmetry.
        eapply state_lessdef_state_equiv; eauto.
        intros [ti' [YHH HLD]].
        exists ti'; split; eauto. econstructor; eauto.
Qed.

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

Lemma all_preds_in_empty:
  all_preds_in empty (PTree.empty unit).
Proof.
  unfold all_preds_in; intros; apply NE.Forall_forall; intros.
  - rewrite get_empty in H. inv H. inv H0.
Qed.

Lemma abstr_seq_reverse_correct:
  forall sp x i i' ti cf x' l lm ps',
    abstract_sequence' x = Some (x', l, lm) ->
    evaluable_pred_list (mk_ctx i sp ge) x'.(forest_preds) l ->
    evaluable_pred_list_m (mk_ctx i sp ge) x'.(forest_preds) lm ->
    sem_predset {| ctx_is := i; ctx_sp := sp; ctx_ge := ge |} x' ps' ->
    sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
    state_lessdef i ti ->
   exists ti', SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf)
           /\ state_lessdef i' ti'.
Proof.
  intros. unfold abstract_sequence' in H.
  unfold Option.map, Option.bind in H. repeat destr. inv H. inv Heqo.
  eapply abstr_seq_reverse_correct_fold;
    try eassumption; try reflexivity; auto using sem_empty, all_preds_in_empty.
  inversion 1.
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
