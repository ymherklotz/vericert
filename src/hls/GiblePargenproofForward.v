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
Require Import vericert.hls.GiblePargen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.
Require Import vericert.hls.AbstrSemIdent.
Require Import vericert.common.Monad.

Module Import OptionExtra := MonadExtra(Option).

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

#[local] Opaque simplify.
#[local] Opaque deep_simplify.

#[local] Ltac destr := destruct_match; try discriminate; [].

Definition state_lessdef := GiblePargenproofEquiv.match_states.

Definition is_regs i := match i with mk_instr_state rs _ _ => rs end.
Definition is_mem i := match i with mk_instr_state _ _ m => m end.
Definition is_ps i := match i with mk_instr_state _ p _ => p end.

Definition check_dest i r' :=
  match i with
  | RBop p op rl r => (r =? r')%positive
  | RBload p chunk addr rl r => (r =? r')%positive
  | _ => false
  end.

Lemma check_dest_dec i r :
  {check_dest i r = true} + {check_dest i r = false}.
Proof. destruct (check_dest i r); tauto. Qed.

Fixpoint check_dest_l l r :=
  match l with
  | nil => false
  | a :: b => check_dest a r || check_dest_l b r
  end.

Lemma check_dest_l_forall :
  forall l r,
  check_dest_l l r = false ->
  Forall (fun x => check_dest x r = false) l.
Proof. induction l; crush. Qed.

Lemma check_dest_l_dec i r :
  {check_dest_l i r = true} + {check_dest_l i r = false}.
Proof. destruct (check_dest_l i r); tauto. Qed.

Section CORRECTNESS.

  Context (prog: GibleSeq.program) (tprog : GiblePar.program).

  Let ge : GibleSeq.genv := Globalenvs.Genv.globalenv prog.
  Let tge : GiblePar.genv := Globalenvs.Genv.globalenv tprog.

(*|
Here we can finally assume that everything in the forest is evaluable, which
will allow us to prove that translating the list of register accesses will also
all be evaluable.
|*)

  Lemma sem_update_Iop :
    forall A op rs args m v f ps ctx,
      Op.eval_operation (ctx_ge ctx) (ctx_sp ctx) op rs ## args (is_mem (ctx_is ctx)) = Some v ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_value ctx
        (seq_app (pred_ret (Eop op)) (merge (list_translation args f))) v.
  Proof.
    intros * EVAL SEM.
    exploit sem_pred_expr_list_translation; try eassumption.
    intro H; inversion_clear H as [x [HS HV]].
    eapply sem_pred_expr_seq_app_val.
    - cbn in *; eapply sem_pred_expr_merge; eauto.
    - apply sem_pred_expr_pred_ret.
    - econstructor; [eauto|]; auto.
  Qed.

  Lemma sem_update_Iload :
    forall A rs args m v f ps ctx addr a0 chunk,
      Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr rs ## args = Some a0 ->
      Mem.loadv chunk m a0 = Some v ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_value ctx
        (seq_app (seq_app (pred_ret (Eload chunk addr)) (merge (list_translation args f))) (f #r Mem)) v.
  Proof.
    intros * EVAL MEM SEM.
    exploit sem_pred_expr_list_translation; try eassumption.
    intro H; inversion_clear H as [x [HS HV]].
    inversion SEM as [? ? ? ? ? ? REG PRED HMEM EXIT]; subst.
    exploit sem_pred_expr_ident2; [eapply HMEM|].
    intros H; inversion_clear H as [x' [HS' HV']].
    eapply sem_pred_expr_seq_app_val; eauto.
    { eapply sem_pred_expr_seq_app; eauto.
      - eapply sem_pred_expr_merge; eauto.
      - apply sem_pred_expr_pred_ret.
    }
    econstructor; eauto.
  Qed.

  Lemma sem_update_Istore :
    forall A rs args m v f ps ctx addr a0 chunk m' v',
      Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr rs ## args = Some a0 ->
      Mem.storev chunk m a0 v' = Some m' ->
      sem_value ctx v v' ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_mem ctx
        (seq_app (seq_app (pred_ret (Estore v chunk addr))
          (merge (list_translation args f))) (f #r Mem)) m'.
  Proof.
    intros * EVAL STOREV SEMVAL SEM.
    exploit sem_merge_list; try eassumption.
    intro MERGE. exploit sem_pred_expr_ident2; eauto.
    intro TMP; inversion_clear TMP as [x [HS HV]].
    inversion_clear SEM as [? ? ? ? ? ? REG PRED HMEM EXIT].
    exploit sem_pred_expr_ident2; [eapply HMEM|].
    intros TMP; inversion_clear TMP as [x' [HS' HV']].
    eapply sem_pred_expr_ident.
    eapply sem_pred_expr_seq_app; eauto.
    eapply sem_pred_expr_seq_app; eauto.
    eapply sem_pred_expr_pred_ret.
    econstructor; eauto.
  Qed.

  Lemma sem_update_Iop_top:
    forall A f p p' f' rs m pr op res args p0 v state,
      Op.eval_operation (ctx_ge state) (ctx_sp state) op rs ## args m = Some v ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBop p0 op args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state (rs # res <- v) pr m, None).
    Proof.
      intros * EVAL_OP TRUTHY VALID SEM UPD EVAL_PRED.
      pose proof SEM as SEM2.
      inversion UPD as [PRUNE]. unfold Option.bind in PRUNE.
      destr. inversion_clear PRUNE.
      rename Heqo into PRUNE.
      inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
      cbn [is_ps] in *. constructor.
      + constructor; intro x. inversion_clear REG as [? ? ? REG']. specialize (REG' x).
        destruct f as [fr fp fe]. cbn [forest_preds set_forest] in *.
        destruct (peq x res); subst.
        * rewrite forest_reg_gss in *. rewrite Regmap.gss in *.
          eapply sem_pred_expr_prune_predicated; eauto. inv PRED; eassumption.
          eapply sem_pred_expr_app_predicated; [| |eauto].
          replace fp with (forest_preds {| forest_regs := fr; forest_preds := fp; forest_exit := fe |}) by auto.
          eapply sem_update_Iop; eauto. cbn in *.
          eapply eval_operation_valid_pointer; eauto.
          inversion_clear SEM2 as [? ? ? ? ? ? REG2 PRED2 MEM2 EXIT2].
          inversion_clear PRED2; eauto.
          cbn -[eval_predf]. rewrite eval_predf_Pand.
          rewrite EVAL_PRED. rewrite truthy_dflt; auto.
        * rewrite forest_reg_gso. rewrite Regmap.gso; auto.
          unfold not in *; intros. apply n0. inv H; auto.
      + constructor; intros. inv PRED. rewrite forest_reg_pred. auto.
      + rewrite forest_reg_gso; auto; discriminate.
      + auto.
  Qed.

  Lemma sem_update_Iload_top:
    forall A f p p' f' rs m pr res args p0 v state addr a chunk,
      Op.eval_addressing (ctx_ge state) (ctx_sp state) addr rs ## args = Some a ->
      Mem.loadv chunk m a = Some v ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBload p0 chunk addr args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state (rs # res <- v) pr m, None).
    Proof.
      intros * EVAL_OP LOAD TRUTHY VALID SEM UPD EVAL_PRED.
      pose proof SEM as SEM2.
      inversion UPD as [PRUNE]. unfold Option.bind in PRUNE. destr.
      inversion_clear PRUNE.
      rename Heqo into PRUNE.
      inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
      cbn [is_ps] in *. constructor.
      + constructor; intro x. inversion_clear REG as [? ? ? REG']. specialize (REG' x).
        destruct f as [fr fp fe]. cbn [forest_preds set_forest] in *.
        destruct (peq x res); subst.
        * rewrite forest_reg_gss in *. rewrite Regmap.gss in *.
          eapply sem_pred_expr_prune_predicated; eauto. inv PRED; eassumption.
          eapply sem_pred_expr_app_predicated; [| |eauto].
          replace fp with (forest_preds {| forest_regs := fr; forest_preds := fp; forest_exit := fe |}) by auto.
          eapply sem_update_Iload; eauto.
          inversion_clear PRED; eauto.
          cbn -[eval_predf]. rewrite eval_predf_Pand.
          rewrite EVAL_PRED. rewrite truthy_dflt; auto.
        * rewrite forest_reg_gso. rewrite Regmap.gso; auto.
          unfold not in *; intros. apply n0. inv H; auto.
      + constructor; intros. inv PRED. rewrite forest_reg_pred. auto.
      + rewrite forest_reg_gso; auto; discriminate.
      + auto.
  Qed.

  Lemma sem_update_Istore_top:
    forall A f p p' f' rs m pr res args p0 state addr a chunk m',
      Op.eval_addressing (ctx_ge state) (ctx_sp state) addr rs ## args = Some a ->
      Mem.storev chunk m a rs !! res = Some m' ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBstore p0 chunk addr args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state rs pr m', None).
  Proof.
    intros * EVAL_OP STORE TRUTHY VALID SEM UPD EVAL_PRED.
    pose proof SEM as SEM2.
    inversion UPD as [PRUNE]. unfold Option.bind in PRUNE. destr.
    inversion_clear PRUNE.
    rename Heqo into PRUNE.
    inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
    cbn [is_ps] in *. constructor.
    + constructor; intros. inv REG. rewrite forest_reg_gso; eauto. discriminate.
    + constructor; intros. inv PRED. rewrite forest_reg_pred. auto.
    + destruct f as [fr fp fm]; cbn -[seq_app] in *.
      rewrite forest_reg_gss.
      exploit sem_pred_expr_ident2; [exact MEM|]; intro HSEM_;
        inversion_clear HSEM_ as [x [HSEM1 HSEM2]].
      inv REG. specialize (H res).
      pose proof H as HRES.
      eapply sem_pred_expr_ident2 in HRES.
      inversion_clear HRES as [r2 [HRES1 HRES2]].
      apply exists_sem_pred in H. inversion_clear H as [r' [HNE HVAL]].
      exploit sem_merge_list. eapply SEM2. instantiate (2 := args). intro HSPE. eapply sem_pred_expr_ident2 in HSPE.
      inversion_clear HSPE as [l_ [HSPE1 HSPE2]].
      eapply sem_pred_expr_prune_predicated; eauto. inv PRED; eassumption.
      eapply sem_pred_expr_app_predicated.
      eapply sem_pred_expr_seq_app_val; [solve [eauto]| |].
      eapply sem_pred_expr_seq_app; [solve [eauto]|].
      eapply sem_pred_expr_flap2.
      eapply sem_pred_expr_seq_app; [solve [eauto]|].
      eapply sem_pred_expr_pred_ret. econstructor. eauto. 3: { eauto. }
      eauto. auto. eauto. inv PRED. eauto.
      rewrite eval_predf_Pand. rewrite EVAL_PRED.
      rewrite truthy_dflt. auto. auto.
    + auto.
  Qed.

  Lemma sem_pexpr_not_in :
    forall G (ctx: @ctx G) p0 ps p e b,
      ~ PredIn p p0 ->
      sem_pexpr ctx (from_pred_op ps p0) b ->
      sem_pexpr ctx (from_pred_op (PTree.set p e ps) p0) b.
  Proof.
    induction p0; auto; intros.
    - cbn. destruct p. unfold get_forest_p'.
      assert (p0 <> p) by
        (unfold not; intros; apply H; subst; constructor).
      rewrite PTree.gso; auto.
    - cbn in *.
      assert (X: ~ PredIn p p0_1 /\ ~ PredIn p p0_2) by
        (split; unfold not; intros; apply H; constructor; tauto).
      inversion_clear X as [X1 X2].
      inv H0. inv H4.
      specialize (IHp0_1 _ p e _ X1 H0). constructor. tauto.
      specialize (IHp0_2 _ p e _ X2 H0). constructor. tauto.
      constructor; auto.
    - cbn in *.
      assert (X: ~ PredIn p p0_1 /\ ~ PredIn p p0_2) by
        (split; unfold not; intros; apply H; constructor; tauto).
      inversion_clear X as [X1 X2].
      inv H0. inv H4.
      specialize (IHp0_1 _ p e _ X1 H0). constructor. tauto.
      specialize (IHp0_2 _ p e _ X2 H0). constructor. tauto.
      constructor; auto.
  Qed.

  Lemma sem_pred_not_in :
    forall A B G (ctx: @ctx G) (s: @Abstr.ctx G -> A -> B -> Prop) l v p e ps,
      sem_pred_expr ps s ctx l v ->
      predicated_not_inP p l ->
      sem_pred_expr (PTree.set p e ps) s ctx l v.
  Proof.
    induction l.
    - intros. unfold predicated_not_inP in H0.
      destruct a. constructor. apply sem_pexpr_not_in.
      eapply H0. econstructor. inv H. auto. inv H. auto.
    - intros. inv H. constructor. unfold predicated_not_inP in H0.
      eapply sem_pexpr_not_in. eapply H0. constructor. left. eauto.
      auto. auto.
      apply sem_pred_expr_cons_false. apply sem_pexpr_not_in. eapply H0.
      constructor. tauto. auto. auto.
      eapply IHl. eauto. eapply predicated_not_inP_cons; eauto.
  Qed.

  Lemma pred_fold_true' :
    forall A l pred y,
      fold_left (fun a (p : positive * predicated A) => a && predicated_not_in pred (snd p)) l y = true ->
      y = true.
  Proof.
    induction l; crush.
    exploit IHl; try eassumption; intros.
    eapply andb_prop in H0; tauto.
  Qed.

  Lemma pred_fold_true :
    forall A pred l p y,
      fold_left (fun (a : bool) (p : positive * predicated A) => a && predicated_not_in pred (snd p)) l y = true ->
      y = true ->
      list_norepet (map fst l) ->
      In p l ->
      predicated_not_in pred (snd p) = true.
  Proof.
    induction l; crush.
    inv H1. inv H2.
    - cbn in *. now eapply pred_fold_true' in H.
    - cbn in *; eapply IHl; try eassumption.
      eapply pred_fold_true'; eauto.
  Qed.

  Lemma pred_not_in_forestP :
    forall pred f,
      predicated_not_in_forest pred f = true ->
      forall x, predicated_not_inP pred (f #r x).
  Proof.
    unfold predicated_not_in_forest, predicated_not_in_pred_expr; intros.
    destruct (RTree.get x (forest_regs f)) eqn:?.
    - eapply andb_prop in H. inv H. rewrite PTree.fold_spec in H0.
      unfold RTree.get in Heqo.
      exploit pred_fold_true. eauto. auto. apply PTree.elements_keys_norepet.
      apply PTree.elements_correct; eauto.
      intros. eapply predicated_not_inP_equiv. unfold "#r".
      unfold RTree.get. rewrite Heqo. auto.
    - unfold "#r". rewrite Heqo. unfold predicated_not_inP; intros.
    inv H0. inversion 1.
  Qed.

  Lemma pred_not_in_forest_exitP :
    forall pred f,
      predicated_not_in_forest pred f = true ->
      predicated_not_inP pred (forest_exit f).
  Proof.
    intros.
    eapply predicated_not_inP_equiv. unfold predicated_not_in_forest in H.
    eapply andb_prop in H; tauto.
  Qed.

  Lemma sem_update_Isetpred:
    forall A (ctx: @ctx A) f pr p0 c args b rs m,
      predicated_mutexcl (seq_app (pred_ret (PEsetpred c)) (merge (list_translation args f))) ->
      valid_mem (ctx_mem ctx) m ->
      sem ctx f (mk_instr_state rs pr m, None) ->
      Op.eval_condition c rs ## args m = Some b ->
      truthy pr p0 ->
      sem_pexpr ctx
      (from_predicated true (forest_preds f) (seq_app (pred_ret (PEsetpred c)) (merge (list_translation args f)))) b.
  Proof.
    intros * HPREDMUT **. eapply from_predicated_sem_pred_expr.
    { inv H0. inv H10. eassumption. }
    { auto. }
    pose proof (sem_merge_list _ ctx f rs pr m args H0).
    apply sem_pred_expr_ident2 in H3; simplify.
    eapply sem_pred_expr_seq_app_val; [eauto| |].
    constructor. constructor. constructor.
    econstructor; eauto.
    erewrite storev_eval_condition; eauto.
  Qed.

  Lemma sem_update_Isetpred_top:
    forall A f p p' f' rs m pr args p0 state c pred b,
      Op.eval_condition c rs ## args m = Some b ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBsetpred p0 c args pred) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state rs (pr # pred <- b) m, None).
  Proof.
    intros * EVAL_OP TRUTHY VALID SEM UPD EVAL_PRED.
    pose proof SEM as SEM2.
    inversion UPD as [PRUNE]. unfold Option.bind in PRUNE. repeat destr.
    inversion_clear PRUNE.
    rename Heqo into PRUNE.
    inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
    cbn [is_ps] in *. constructor.
    + constructor. intros. apply sem_pred_not_in. rewrite forest_pred_reg.
      inv REG. auto. rewrite forest_pred_reg. apply pred_not_in_forestP.
      unfold assert_ in *. repeat (destruct_match; try discriminate); auto.
    + constructor; intros. destruct (peq x pred); subst.
      * rewrite Regmap.gss.
        rewrite forest_pred_gss.
        cbn [update] in *. unfold Option.bind in *. repeat destr. inv UPD.
        replace b with (b && true) by eauto with bool.
        apply sem_pexpr_Pand.
        destruct b. constructor. right.
        eapply sem_update_Isetpred; eauto.
        { unfold assert_ in Heqo. destr. eauto using check_mutexcl_correct. }
        constructor. constructor. replace false with (negb true) by auto.
        apply sem_pexpr_negate. inv TRUTHY. constructor.
        cbn. eapply sem_pexpr_eval. inv PRED. eauto. auto.
        replace false with (negb true) by auto.
        apply sem_pexpr_negate.
        eapply sem_pexpr_eval. inv PRED. eauto. auto.
        eapply sem_update_Isetpred; eauto.
        { unfold assert_ in Heqo. destr. eauto using check_mutexcl_correct. }
        constructor. constructor. constructor.
        replace true with (negb false) by auto. apply sem_pexpr_negate.
        eapply sem_pexpr_eval. inv PRED. eauto. inv TRUTHY. auto. cbn -[eval_predf].
        rewrite eval_predf_negate. rewrite H; auto.
        replace true with (negb false) by auto. apply sem_pexpr_negate.
        eapply sem_pexpr_eval. inv PRED. eauto. rewrite eval_predf_negate.
        rewrite EVAL_PRED. auto.
      * rewrite Regmap.gso by auto. inv PRED. specialize (H x).
        rewrite forest_pred_gso by auto; auto.
    + rewrite forest_pred_reg. apply sem_pred_not_in. auto. apply pred_not_in_forestP.
      unfold assert_ in *. now repeat (destruct_match; try discriminate).
    + cbn -[from_predicated from_pred_op seq_app]. apply sem_pred_not_in; auto.
      apply pred_not_in_forest_exitP.
      unfold assert_ in *. now repeat (destruct_match; try discriminate).
  Qed.

  Lemma sem_pexpr_impl :
    forall A (state: @ctx A) a b res,
      sem_pexpr state b res ->
      sem_pexpr state a true ->
      sem_pexpr state (a → b) res.
  Proof.
    intros. destruct res.
    constructor; tauto.
    constructor; auto. replace false with (negb true) by auto.
    now apply sem_pexpr_negate.
  Qed.

  Lemma eval_predf_simplify :
    forall ps x,
      eval_predf ps (simplify x) = eval_predf ps x.
  Proof.
    unfold eval_predf; intros.
    rewrite simplify_correct. auto.
  Qed.

  Lemma sem_update_falsy:
    forall A state f f' rs ps m p a p',
      instr_falsy ps a ->
      update (p, f) a = Some (p', f') ->
      sem state f (mk_instr_state rs ps m, None) ->
      @sem A state f' (mk_instr_state rs ps m, None).
  Proof.
    inversion 1; cbn [update] in *; intros.
    - unfold Option.bind in *. destr. inv H2.
      constructor.
      * constructor. intros. destruct (peq x res); subst.
        rewrite forest_reg_gss. cbn.
        eapply sem_pred_expr_prune_predicated; eauto. inv H3; inv H9; eassumption.
        eapply sem_pred_expr_app_predicated_false. inv H3. inv H8. auto.
        inv H3. inv H9. eauto. rewrite eval_predf_Pand. cbn -[eval_predf].
        rewrite H0. auto. 
        rewrite forest_reg_gso. inv H3. inv H8. auto.
        unfold not; intros; apply n0. now inv H1.
      * constructor; intros. rewrite forest_reg_pred. inv H3. inv H9. auto.
      * rewrite forest_reg_gso. inv H3. auto. unfold not; intros. inversion H1.
      * inv H3. auto.
    - unfold Option.bind in *. destr. inv H2.
      constructor.
      * constructor. intros. destruct (peq x dst); subst.
        rewrite forest_reg_gss. cbn.
        eapply sem_pred_expr_prune_predicated; eauto. inv H3; inv H9; eassumption.
        eapply sem_pred_expr_app_predicated_false. inv H3. inv H8. auto.
        inv H3. inv H9. eauto. rewrite eval_predf_Pand. cbn -[eval_predf].
        rewrite H0. auto. 
        rewrite forest_reg_gso. inv H3. inv H8. auto.
        unfold not; intros; apply n0. now inv H1.
      * constructor; intros. rewrite forest_reg_pred. inv H3. inv H9. auto.
      * rewrite forest_reg_gso. inv H3. auto. unfold not; intros. inversion H1.
      * inv H3. auto.
    - unfold Option.bind in *. destr. inv H2.
      constructor.
      * constructor. intros. rewrite forest_reg_gso by discriminate. inv H3. inv H8. auto.
      * constructor; intros. rewrite forest_reg_pred. inv H3. inv H9. auto.
      * rewrite forest_reg_gss. cbn. eapply sem_pred_expr_prune_predicated; eauto. inv H3; inv H9; eassumption.
        eapply sem_pred_expr_app_predicated_false. inv H3. auto. inv H3. inv H9. eauto.
        rewrite eval_predf_Pand. cbn -[eval_predf]. rewrite H0. auto.
      * inv H3. auto.
    - unfold Option.bind in *. repeat destr. inv H2.
      constructor.
      * constructor; intros. rewrite forest_pred_reg. apply sem_pred_not_in.
        inv H3. inv H8. auto. apply pred_not_in_forestP. unfold assert_ in Heqo0. now destr.
      * constructor. intros. destruct (peq x pred); subst.
        rewrite forest_pred_gss. replace (ps !! pred) with (true && ps !! pred) by auto.
        assert (sem_pexpr state0 (¬ (from_pred_op (forest_preds f) p0 ∧ from_pred_op (forest_preds f) p')) true).
        { replace true with (negb false) by auto. apply sem_pexpr_negate.
          constructor. left. eapply sem_pexpr_eval. inv H3. inv H9. eauto.
          auto.
        }
        apply sem_pexpr_Pand. constructor; tauto.
        apply sem_pexpr_impl. inv H3. inv H10. eauto.
        { constructor. left. eapply sem_pexpr_eval. inv H3. inv H10. eauto.
          rewrite eval_predf_negate. rewrite H0. auto.
        }
        rewrite forest_pred_gso by auto. inv H3. inv H9. auto.
      * rewrite forest_pred_reg. apply sem_pred_not_in. inv H3. auto.
        apply pred_not_in_forestP. unfold assert_ in Heqo0. now destr.
      * apply sem_pred_not_in. inv H3; auto. cbn.
        apply pred_not_in_forest_exitP. unfold assert_ in Heqo0. now destr.
    - unfold Option.bind in *. destr. inv H2. inv H3. constructor.
      * constructor. inv H8. auto.
      * constructor. intros. inv H9. eauto.
      * auto.
      * cbn. eapply sem_pred_expr_prune_predicated; [| |eauto]. inv H9; eassumption.
        eapply sem_pred_expr_app_predicated_false; auto.
        inv H9. eauto.
        rewrite eval_predf_Pand. cbn -[eval_predf]. rewrite H0. auto.
  Qed.

  Lemma sem_update_falsy_input:
    forall A state f f' rs ps m p a p' exitcf,
      eval_predf ps p = false ->
      update (p, f) a = Some (p', f') ->
      sem state f (mk_instr_state rs ps m, exitcf) ->
      @sem A state f' (mk_instr_state rs ps m, exitcf)
        /\ eval_predf ps p' = false.
  Proof.
    intros; destruct a; cbn [update] in *; intros.
    - inv H0. auto.
    - unfold Option.bind in *. destr. inv H0. split; [|solve [auto]].
      constructor.
      * constructor. intros. destruct (peq x r); subst.
        rewrite forest_reg_gss. cbn.
        eapply sem_pred_expr_prune_predicated; eauto. inv H1; inv H8; eassumption.
        eapply sem_pred_expr_app_predicated_false. inv H1. inv H7. auto.
        inv H1. inv H8. eauto. rewrite eval_predf_Pand.
        rewrite H. eauto with bool.
        rewrite forest_reg_gso. inv H1. inv H7. auto.
        unfold not; intros; apply n0. now inv H0.
      * constructor; intros. rewrite forest_reg_pred. inv H1. inv H8. auto.
      * rewrite forest_reg_gso. inv H1. auto. unfold not; intros. inversion H0.
      * inv H1. auto.
    - unfold Option.bind in *. destr. inv H0. split; [|solve [auto]].
      constructor.
      * constructor. intros. destruct (peq x r); subst.
        rewrite forest_reg_gss. cbn.
        eapply sem_pred_expr_prune_predicated; eauto. inv H1; inv H8; eassumption.
        eapply sem_pred_expr_app_predicated_false. inv H1. inv H7. auto.
        inv H1. inv H8. eauto. rewrite eval_predf_Pand. cbn -[eval_predf].
        rewrite H. eauto with bool.
        rewrite forest_reg_gso. inv H1. inv H7. auto.
        unfold not; intros; apply n0. now inv H0.
      * constructor; intros. rewrite forest_reg_pred. inv H1. inv H8. auto.
      * rewrite forest_reg_gso. inv H1. auto. unfold not; intros. inversion H0.
      * inv H1. auto.
    - unfold Option.bind in *. destr. inv H0. split; [|solve [auto]].
      constructor.
      * constructor. intros. rewrite forest_reg_gso by discriminate. inv H1. inv H7. auto.
      * constructor; intros. rewrite forest_reg_pred. inv H1. inv H8. auto.
      * rewrite forest_reg_gss. cbn. eapply sem_pred_expr_prune_predicated; eauto. inv H1; inv H8; eassumption.
        eapply sem_pred_expr_app_predicated_false. inv H1. auto. inv H1. inv H8. eauto.
        rewrite eval_predf_Pand. cbn -[eval_predf]. rewrite H. eauto with bool.
      * inv H1. auto.
    - unfold Option.bind in *. repeat destr. inv H0. split; [|solve [auto]].
      constructor.
      * constructor; intros. rewrite forest_pred_reg. apply sem_pred_not_in.
        inv H1. inv H7. auto. apply pred_not_in_forestP. unfold assert_ in Heqo1. now destr.
      * constructor. intros. destruct (peq x p0); subst.
        rewrite forest_pred_gss. replace (ps !! p0) with (true && ps !! p0) by auto.
        assert (sem_pexpr state0 (¬ (from_pred_op (forest_preds f) (dfltp o) ∧ from_pred_op (forest_preds f) p')) true).
        { replace true with (negb false) by auto. apply sem_pexpr_negate.
          constructor. right. eapply sem_pexpr_eval. inv H1. inv H8. eauto.
          auto.
        }
        apply sem_pexpr_Pand. constructor; tauto.
        apply sem_pexpr_impl. inv H1. inv H9. eauto.
        { constructor. right. eapply sem_pexpr_eval. inv H1. inv H9. eauto.
          rewrite eval_predf_negate. rewrite H. auto.
        }
        rewrite forest_pred_gso by auto. inv H1. inv H8. auto.
      * rewrite forest_pred_reg. apply sem_pred_not_in. inv H1. auto.
        apply pred_not_in_forestP. unfold assert_ in Heqo1. now destr.
      * apply sem_pred_not_in. inv H1; auto. cbn.
        apply pred_not_in_forest_exitP. unfold assert_ in Heqo1. now destr.
    - unfold Option.bind in *. destr. inv H0. inv H1. split.
      -- constructor.
         * constructor. inv H7. auto.
         * constructor. intros. inv H8. eauto.
         * auto.
         * cbn. eapply sem_pred_expr_prune_predicated; [| |eauto]. inv H8; eassumption.
           eapply sem_pred_expr_app_predicated_false; auto.
           inv H8. eauto.
           rewrite eval_predf_Pand. cbn -[eval_predf]. rewrite H. eauto with bool.
      -- rewrite eval_predf_simplify. rewrite eval_predf_Pand. rewrite H. eauto with bool.
  Qed.

  Definition setpred_wf (i: instr): bool :=
    match i with
    | RBsetpred (Some op) _ _ p => negb (predin peq p op)
    | _ => true
    end.

  Lemma sem_update_instr :
    forall f i' i'' a sp p i p' f',
      step_instr ge sp (Iexec i') a (Iexec i'') ->
      valid_mem (is_mem i) (is_mem i') ->
      sem (mk_ctx i sp ge) f (i', None) ->
      update (p, f) a = Some (p', f') ->
      eval_predf (is_ps i') p = true ->
      sem (mk_ctx i sp ge) f' (i'', None).
  Proof.
    inversion 1; subst; clear H; intros VALID SEM UPD EVAL_PRED; pose proof SEM as SEM2.
    - inv UPD; auto.
    - eauto using sem_update_Iop_top.
    - eauto using sem_update_Iload_top.
    - eauto using sem_update_Istore_top.
    - eauto using sem_update_Isetpred_top.
    - destruct i''. eauto using sem_update_falsy.
  Qed.

  Lemma Pand_true_left :
    forall ps a b,
      eval_predf ps a = false ->
      eval_predf ps (a ∧ b) = false.
  Proof.
    intros.
    rewrite eval_predf_Pand. now rewrite H.
  Qed.

  Lemma Pand_true_right :
    forall ps a b,
      eval_predf ps b = false ->
      eval_predf ps (a ∧ b) = false.
  Proof.
    intros.
    rewrite eval_predf_Pand. rewrite H.
    eauto with bool.
  Qed.

  Lemma sem_update_instr_term :
    forall f i' i'' sp i cf p p' p'' f',
      sem (mk_ctx i sp ge) f (i', None) ->
      step_instr ge sp (Iexec i') (RBexit p cf) (Iterm i'' cf) ->
      update (p', f) (RBexit p cf) = Some (p'', f') ->
      eval_predf (is_ps i') p' = true ->
      sem (mk_ctx i sp ge) f' (i'', Some cf)
           /\ eval_predf (is_ps i') p'' = false.
  Proof.
    intros. inv H0. simpl in *.
    unfold Option.bind in *. destruct_match; try discriminate.
    apply truthy_dflt in H6. inv H1.
    assert (eval_predf (Gible.is_ps i'') (¬ dfltp p) = false).
    { rewrite eval_predf_negate. now rewrite negb_false_iff. }
    apply Pand_true_left with (b := p') in H0.
    rewrite <- eval_predf_simplify in H0. split; auto.
    unfold "<-e". destruct i''.
    inv H. constructor; auto.
    constructor. inv H9. intros. cbn. eauto.
    inv H10. constructor; intros. eauto.
    cbn.
    eapply sem_pred_expr_prune_predicated; eauto. inv H10; eassumption.
    eapply sem_pred_expr_app_predicated.
    constructor. constructor. constructor.
    inv H10. eauto. cbn -[eval_predf] in *.
    rewrite eval_predf_Pand. rewrite H2. now rewrite H6.
  Qed.

  Lemma step_instr_lessdef_term :
    forall sp a i i' ti cf,
      step_instr ge sp (Iexec i) a (Iterm i' cf) ->
      state_lessdef i ti ->
      exists ti', step_instr ge sp (Iexec ti) a (Iterm ti' cf) /\ state_lessdef i' ti'.
  Proof.
    inversion 1; intros; subst.
    econstructor. split; eauto. constructor.
    destruct p. constructor. erewrite eval_predf_pr_equiv. inv H4.
    eauto. inv H6. eauto. constructor.
  Qed.

  Lemma combined_falsy :
    forall i o1 o,
      falsy i o1 ->
      falsy i (combine_pred o o1).
  Proof.
    inversion 1; subst; crush. destruct o; simplify.
    constructor. rewrite eval_predf_Pand. rewrite H0. crush.
    constructor. auto.
  Qed.

  Lemma Abstr_match_states_sem :
    forall i sp f i' ti cf,
      sem (mk_ctx i sp ge) f (i', cf) ->
      state_lessdef i ti ->
      exists ti', sem (mk_ctx ti sp ge) f (ti', cf) /\ state_lessdef i' ti'.
  Proof.
    intros.
    eapply sem_correct in H. exists i'; split; eauto. reflexivity.
    constructor; eauto. unfold ge_preserved; auto.
  Qed.

  Lemma mfold_left_update_Some :
    forall xs x v,
      mfold_left update xs x = Some v ->
      exists y, x = Some y.
  Proof.
    induction xs; intros.
    { cbn in *. inv H. eauto. }
    cbn in *. unfold Option.bind in *. exploit IHxs; eauto.
    intros. simplify. destruct x; crush.
    eauto.
  Qed.

  Lemma step_instr_term_exists :
    forall A B ge sp v x v2 cf,
      @step_instr A B ge sp (Iexec v) x (Iterm v2 cf) ->
      exists p, x = RBexit p cf.
  Proof using. inversion 1; eauto. Qed.

  Lemma eval_predf_update_true :
    forall i i' curr_p next_p f f_next instr sp,
      update (curr_p, f) instr = Some (next_p, f_next) ->
      step_instr ge sp (Iexec i) instr (Iexec i') ->
      eval_predf (is_ps i) curr_p = true ->
      eval_predf (is_ps i') next_p = true.
  Proof.
    intros * UPD STEP EVAL. destruct instr; cbn [update] in UPD;
      try solve [unfold Option.bind in *; try destr; inv UPD; inv STEP; auto].
    - unfold Option.bind in *. repeat destr. inv UPD. inv STEP; auto. cbn [is_ps] in *.
      unfold is_initial_pred_and_notin in Heqo2. unfold assert_ in Heqo2. repeat destr.
      subst. assert (~ PredIn p2 next_p).
      unfold not; intros. apply negb_true_iff in Heqb0. apply not_true_iff_false in Heqb0.
      apply Heqb0. now apply predin_PredIn. rewrite eval_predf_not_PredIn; auto.
    - unfold Option.bind in *. destr. inv UPD. inv STEP. inv H3. cbn.
      rewrite eval_predf_simplify. rewrite eval_predf_Pand. rewrite eval_predf_negate.
      destruct i'; cbn in *. rewrite H0. auto.
  Qed.

  Lemma seq_app_cons :
    forall A B  f a l p0 p1,
      @seq_app A B (pred_ret f) (NE.cons a l) = NE.cons p0 p1 ->
      @seq_app A B (pred_ret f) l = p1.
  Proof. intros. cbn in *. inv H. eauto. Qed.

  Lemma sem_update_valid_mem :
    forall i i' i'' curr_p next_p f f_next instr sp,
      step_instr ge sp (Iexec i') instr (Iexec i'') ->
      update (curr_p, f) instr = Some (next_p, f_next) ->
      sem (mk_ctx i sp ge) f (i', None) ->
      valid_mem (is_mem i') (is_mem i'').
  Proof.
    inversion 1; crush.
    unfold Option.bind in *. destr. inv H7.
    eapply storev_valid_pointer; eauto.
  Qed.

  Lemma eval_predf_lessdef :
    forall p a b,
      state_lessdef a b ->
      eval_predf (is_ps a) p = eval_predf (is_ps b) p.
  Proof using.
    induction p; crush.
    - inv H. simpl. unfold eval_predf. simpl.
      repeat destr. inv Heqp0. rewrite H1. auto.
    - rewrite !eval_predf_Pand.
      erewrite IHp1 by eassumption.
      now erewrite IHp2 by eassumption.
    - rewrite !eval_predf_Por.
      erewrite IHp1 by eassumption.
      now erewrite IHp2 by eassumption.
  Qed.

(*|
``abstr_fold_falsy``: This lemma states that when we are at the end of an
execution, the values in the register map do not continue to change.
|*)

  Lemma abstr_fold_falsy :
    forall A ilist i sp ge f res p f' p',
      @sem A (mk_ctx i sp ge) f res ->
      mfold_left update ilist (Some (p, f)) = Some (p', f') ->
      eval_predf (is_ps (fst res)) p = false ->
      sem (mk_ctx i sp ge) f' res.
  Proof.
    induction ilist.
    - intros. cbn in *. inv H0. auto.
    - intros. cbn -[update] in H0.
      exploit mfold_left_update_Some. eauto. intros. inv H2.
      rewrite H3 in H0. destruct x.
      destruct res. destruct i0.
      exploit sem_update_falsy_input; try eassumption; intros.
      inversion_clear H2.
      eapply IHilist; eassumption.
  Qed.

  Lemma abstr_fold_correct :
    forall sp x i i' i'' cf f p f' curr_p
        (VALID: valid_mem (is_mem i) (is_mem i')),
      SeqBB.step ge sp (Iexec i') x (Iterm i'' cf) ->
      sem (mk_ctx i sp ge) f (i', None) ->
      eval_predf (is_ps i') curr_p = true ->
      mfold_left update x (Some (curr_p, f)) = Some (p, f') ->
      forall ti,
        state_lessdef i ti ->
        exists ti', sem (mk_ctx ti sp ge) f' (ti', Some cf)
               /\ state_lessdef i'' ti'
               /\ valid_mem (is_mem i) (is_mem i'').
  Proof.
    induction x as [| x xs IHx ]; intros; cbn -[update] in *; inv H; cbn [fst snd] in *.
    - (* inductive case *)
      exploit mfold_left_update_Some; eauto; intros Hexists;
        inversion Hexists as [[curr_p_inter f_inter] EXEQ]; clear Hexists.
        exploit eval_predf_update_true;
        eauto; intros EVALTRUE.
      rewrite EXEQ in H2. eapply IHx in H2; cbn [fst snd] in *.
      eauto.
      transitivity (is_mem i'); auto.
      eapply sem_update_valid_mem; eauto.
      eauto.
      eapply sem_update_instr; eauto. eauto. eauto.
    - (* terminal case *)
      exploit mfold_left_update_Some; eauto; intros Hexists;
        inversion Hexists as [[curr_p_inter f_inter] EXEQ]; clear Hexists. rewrite EXEQ in H2.
      exploit Abstr_match_states_sem; (* TODO *)
      eauto; intros H; inversion H as [v [Hi LESSDEF]]; clear H.
      exploit step_instr_lessdef_term;
      eauto; intros H; inversion H as [v2 [Hi2 LESSDEF2]]; clear H.
      exploit step_instr_term_exists; eauto; inversion 1 as [? ?]; subst; clear H.
      erewrite eval_predf_lessdef in H1 by eassumption.
      exploit sem_update_instr_term;
      eauto; intros [A B].
      exists v2.
      exploit abstr_fold_falsy.
      apply A.
      eassumption. auto. cbn. inversion Hi2; subst. auto. intros.
      split; auto. split; auto.
      inversion H7; subst; auto.
  Qed.

  Lemma sem_regset_empty :
    forall A ctx, @sem_regset A ctx empty (ctx_rs ctx).
  Proof using.
    intros; constructor; intros.
    constructor; auto. constructor.
    constructor.
  Qed.

  Lemma sem_predset_empty :
    forall A ctx, @sem_predset A ctx empty (ctx_ps ctx).
  Proof using.
    intros; constructor; intros.
    constructor; auto. constructor.
  Qed.

  Lemma sem_empty :
    forall A ctx, @sem A ctx empty (ctx_is ctx, None).
  Proof using.
    intros. destruct ctx. destruct ctx_is.
    constructor; try solve [constructor; constructor; crush].
    eapply sem_regset_empty.
    eapply sem_predset_empty.
  Qed.

  Lemma abstr_sequence_correct :
    forall sp x i i'' cf x',
      SeqBB.step ge sp (Iexec i) x (Iterm i'' cf) ->
      abstract_sequence x = Some x' ->
      forall ti,
        state_lessdef i ti ->
        exists ti', sem (mk_ctx ti sp ge) x' (ti', Some cf)
               /\ state_lessdef i'' ti'.
  Proof.
    unfold abstract_sequence. intros. unfold Option.map in H0.
    destruct_match; try easy.
    destruct p as [p TMP]; simplify.
    exploit abstr_fold_correct; eauto; crush.
    { apply sem_empty. }
    exists x0. auto.
  Qed.

End CORRECTNESS.
