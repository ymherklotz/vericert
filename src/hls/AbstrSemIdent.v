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

Inductive sem_ident {B A: Type} (c: @Abstr.ctx B) (a: A): A -> Prop :=
| sem_ident_intro : sem_ident c a a.

Section PROOF.

Context (A B G: Type).
Context (ctx: @Abstr.ctx G).
Context (a_sem: @Abstr.ctx G -> A -> B -> Prop).

Lemma eval_predf_negate :
  forall ps p,
    eval_predf ps (negate p) = negb (eval_predf ps p).
Proof.
  unfold eval_predf; intros. rewrite negate_correct. auto.
Qed.

Lemma is_truthy_negate :
  forall ps p pred,
    truthy ps p ->
    falsy ps (combine_pred (Some (negate (Option.default T p))) pred).
Proof.
  inversion 1; subst; simplify.
  - destruct pred; constructor; auto.
  - destruct pred; constructor.
    rewrite eval_predf_Pand. rewrite eval_predf_negate. rewrite H0. auto.
    rewrite eval_predf_negate. rewrite H0. auto.
Qed.

Lemma sem_pred_expr_NEapp :
  forall f_p a b v,
    sem_pred_expr f_p a_sem ctx a v ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v.
Proof.
  induction a; crush.
  - inv H. constructor; auto.
  - inv H. constructor; eauto.
    eapply sem_pred_expr_cons_false; eauto.
Qed.

Lemma sem_pred_expr_app_predicated_false :
  forall f_p y x v p ps,
    sem_pred_expr f_p a_sem ctx y v ->
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    eval_predf ps p = false ->
    sem_pred_expr f_p a_sem ctx (app_predicated p y x) v.
Proof.
  unfold app_predicated.
  induction y.
  - intros. cbn. inv H. constructor; auto. cbn. constructor; auto.
    eapply sem_pexpr_eval; eauto. rewrite eval_predf_negate. now rewrite H1.
  - intros. inv H.
    + cbn. constructor; auto. cbn. constructor; auto.
      eapply sem_pexpr_eval; eauto. rewrite eval_predf_negate; now rewrite H1.
    + cbn. eapply sem_pred_expr_cons_false. cbn. constructor. tauto.
      eauto.
Qed.

Lemma sem_pred_expr_app_prediceted_false2' :
  forall f_p ps x p v,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    sem_pexpr ctx (from_pred_op f_p p) false ->
    ~ sem_pred_expr f_p a_sem ctx (GiblePargenproofEquiv.NE.map (fun x : Predicate.pred_op * A => (p ∧ fst x, snd x)) x) v.
Proof.
  induction x; crush.
  - unfold not; intros. inv H1. inv H5.
    eapply sem_pexpr_eval_inv in H0; auto.
    eapply sem_pexpr_eval_inv in H3; auto.
    now rewrite H3 in H0.
  - unfold not; intros. eapply IHx; eauto.
    inv H1; eauto.
    inv H7.
    eapply sem_pexpr_eval_inv in H0; auto.
    eapply sem_pexpr_eval_inv in H3; auto.
    now rewrite H3 in H0.
Qed.

Lemma sem_pred_expr_app_predicated_false2 :
  forall f_p y x v p ps,
    sem_pred_expr f_p a_sem ctx (app_predicated p y x) v ->
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    eval_predf ps p = false ->
    sem_pred_expr f_p a_sem ctx y v.
Proof.
  induction y.
  - intros. cbn in *. inv H.
    + destruct a. constructor; auto. now inv H7.
    + cbn in *. exploit sem_pred_expr_app_prediceted_false2'; eauto.
      eapply sem_pexpr_eval; eauto. contradiction.
  - intros. cbn in *. inv H.
    + inv H7. destruct a. constructor; auto.
    + cbn in *. destruct a. eapply sem_pred_expr_cons_false; eauto.
      inv H7. inv H2; auto.
      eapply sem_pexpr_eval_inv in H; eauto. rewrite eval_predf_negate in H.
      now rewrite H1 in H.
Qed.

Lemma sem_pred_expr_prune_predicated :
  forall f_p ps x y v,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    sem_pred_expr f_p a_sem ctx x v ->
    prune_predicated x = Some y ->
    sem_pred_expr f_p a_sem ctx y v.
Proof.
  induction x.
  - cbn in *; intros * HPREDSEM **. repeat destr.
    inv H0. inv H. constructor; auto; cbn in *.
    eapply sem_pexpr_eval; [eassumption|].
    eapply sem_pexpr_eval_inv in H1; [|eassumption].
    now rewrite eval_predf_deep_simplify.
  - cbn in *; intros * HPREDSEM **. destruct_match; repeat destr.
    2: { clear Heqb. inv H; cbn in *.
         eapply sem_pexpr_eval_inv in H4; [|eassumption].
         rewrite <- 2 eval_predf_deep_simplify with (peq:=peq) in H4.
         setoid_rewrite Heqp in H4. now cbn in H4.
         eauto. }
    destruct_match.
    + inv H0. inv H.
      * constructor; auto. eapply sem_pexpr_eval; [eassumption|].
        eapply sem_pexpr_eval_inv in H3; [|eassumption].
        now rewrite eval_predf_deep_simplify.
      * eapply sem_pred_expr_cons_false; eauto.
        eapply sem_pexpr_eval; [eassumption|].
        eapply sem_pexpr_eval_inv in H3; [|eassumption].
        now rewrite eval_predf_deep_simplify.
    + inv H0. inv H.
      * constructor; auto.
        eapply sem_pexpr_eval; [eassumption|].
        eapply sem_pexpr_eval_inv in H3; [|eassumption].
        now rewrite eval_predf_deep_simplify.
      * cbn in *. exploit NE.filter_None. eapply Heqo. cbn. intros.
        exploit sem_pred_expr_in_true. eapply H5. intros [p_true [e_true [HIN [HSEMP HASEM]]]].
        pose proof (NE.In_map _ _ (fun x : Predicate.pred_op * A => (deep_simplify peq (fst x), snd x)) _ _ HIN).
        cbn in *. eapply NE.Forall_forall in H; [|eassumption].
        destr. clear H. cbn in *.
        eapply sem_pexpr_eval_inv in HSEMP; [|eassumption].
        rewrite <- 2 eval_predf_deep_simplify with (peq:=peq) in HSEMP.
        setoid_rewrite Heqp in HSEMP. now cbn in HSEMP.
Qed.

Lemma sem_pred_expr_prune_predicated2 :
  forall f_p ps x y v,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    sem_pred_expr f_p a_sem ctx y v ->
    prune_predicated x = Some y ->
    sem_pred_expr f_p a_sem ctx x v.
Proof.
  induction x; intros * SEMPRED SEM PRUNE. unfold prune_predicated in *.
  - cbn in *. destr. inv PRUNE. inv SEM.
    destruct a; constructor; auto.
    eapply sem_pexpr_eval_inv in H2; eauto.
    eapply sem_pexpr_eval; eauto.
    rewrite eval_predf_deep_simplify in H2; auto.
  - cbn in *. destruct_match.
    2: { destr. destruct a. eapply sem_pred_expr_cons_false; eauto.
         eapply sem_pexpr_eval; eauto.
         rewrite <- 2 eval_predf_deep_simplify with (peq:=peq). now setoid_rewrite Heqp.
    }
    destruct_match.
    + inv PRUNE. destruct a; inv SEM; [constructor|eapply sem_pred_expr_cons_false]; eauto;
      eapply sem_pexpr_eval; eauto; rewrite <- eval_predf_deep_simplify with (peq:=peq);
      eapply sem_pexpr_eval_inv in H4; eauto.
    + inv PRUNE. inv SEM. destruct a. constructor; auto.
      eapply sem_pexpr_eval; eauto. eapply sem_pexpr_eval_inv in H2; eauto.
      now rewrite <- eval_predf_deep_simplify with (peq:=peq).
Qed.

Lemma sem_pred_expr_pred_ret :
  forall (i: A) ps,
    sem_pred_expr ps sem_ident ctx (pred_ret i) i.
Proof. intros; constructor; constructor. Qed.

Lemma sem_pred_expr_ident_det :
  forall A ps x (v v2: A),
    sem_pred_expr ps sem_ident ctx x v ->
    sem_pred_expr ps sem_ident ctx x v2 ->
    v = v2.
Proof.
  intros.
  exploit (@sem_pred_expr_det G G).
  apply similar_refl.
  2: { instantiate (4 := (fun x => @sem_ident x A0)).
       cbn. eauto. }
  intros. inv H1. inv H2. auto.
  apply H. auto.
Qed.

Lemma sem_pred_expr_NEapp2 :
  forall f_p a b v ps,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    (forall x, NE.In x a -> eval_predf ps (fst x) = false) ->
    sem_pred_expr f_p a_sem ctx b v ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v.
Proof.
  induction a; crush.
  - assert (IN: NE.In a (NE.singleton a)) by constructor.
    specialize (H0 _ IN). destruct a.
    eapply sem_pred_expr_cons_false; eauto. cbn [fst] in *.
    eapply sem_pexpr_eval; eauto.
  - assert (NE.In a (NE.cons a a0)) by (constructor; tauto).
    apply H0 in H2.
    destruct a. cbn [fst] in *.
    eapply sem_pred_expr_cons_false.
    eapply sem_pexpr_eval; eauto. eapply IHa; eauto.
    intros. eapply H0. constructor; tauto.
Qed.

Lemma sem_pred_expr_NEapp6 :
  forall f_p a b v ps,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    (forall x, NE.In x a -> eval_predf ps (fst x) = false) ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v ->
    sem_pred_expr f_p a_sem ctx b v.
Proof.
  induction a; crush.
  - assert (IN: NE.In a (NE.singleton a)) by constructor.
    inv H1; auto. eapply H0 in IN. eapply sem_pexpr_eval_inv in H5; eauto.
    now setoid_rewrite H5 in IN.
  - assert (NE.In a (NE.cons a a0)) by (constructor; tauto).
    eapply H0 in H2. destruct a. inv H1.
    + eapply sem_pexpr_eval_inv in H8; eauto. now setoid_rewrite H8 in H2.
    + eapply IHa; eauto. intros. eapply H0. constructor; tauto.
Qed.

Lemma sem_pred_expr_NEapp3 :
  forall f_p a b v,
    (forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false) ->
    sem_pred_expr f_p a_sem ctx b v ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v.
Proof.
  induction a; crush.
  - assert (IN: NE.In a (NE.singleton a)) by constructor.
    specialize (H _ IN). destruct a.
    eapply sem_pred_expr_cons_false; eauto.
  - assert (NE.In a (NE.cons a a0)) by (constructor; tauto).
    apply H in H1.
    destruct a. cbn [fst] in *.
    eapply sem_pred_expr_cons_false; auto.
    eapply IHa; eauto.
    intros. eapply H. constructor; tauto.
Qed.

Lemma sem_pred_expr_NEapp4 :
  forall f_p a b v,
    (forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false) ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v ->
    sem_pred_expr f_p a_sem ctx b v.
Proof.
  induction a; crush.
  - assert (IN: NE.In a (NE.singleton a)) by constructor.
    specialize (H _ IN). inv H0; auto.
    eapply sem_pexpr_det in H; eauto; now try apply similar_refl.
  - assert (NE.In a (NE.cons a a0)) by (constructor; tauto).
    apply H in H1. inv H0.
    eapply sem_pexpr_det in H1; eauto; now try apply similar_refl.
    eapply IHa; eauto. intros. eapply H. apply NE.In_cons; auto.
Qed.

Lemma sem_pred_expr_NEapp5 :
  forall f_p a b v,
    (exists x, NE.In x a /\ sem_pexpr ctx (from_pred_op f_p (fst x)) true) ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v ->
    sem_pred_expr f_p a_sem ctx a v.
Proof.
  induction a; crush.
  - inv H. inv H0. constructor; eauto.
    eapply sem_pexpr_det in H2; eauto; now try apply similar_refl.
  - inv H. inv H3. inv H0. constructor; auto.
    eapply sem_pexpr_det in H2; eauto; now try apply similar_refl. inv H0.
    constructor; auto. apply sem_pred_expr_cons_false; auto. eauto.
Qed.

Lemma sem_pred_expr_in_or_false :
  forall f_p ps a,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    (exists (x: pred_op * A), NE.In x a /\ sem_pexpr ctx (from_pred_op f_p (fst x)) true)
    \/ (forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false).
Proof.
  induction a; intros.
  - case_eq (eval_predf ps (fst a)); intros.
    + left. exists a. split; [constructor; auto|]. eapply sem_pexpr_eval; eauto.
    + right; intros. inv H1. eapply sem_pexpr_eval; eauto.
  - case_eq (eval_predf ps (fst a)); intros.
    + left. exists a. split; [constructor; auto|]. eapply sem_pexpr_eval; eauto.
    + pose proof H as X. eapply IHa in H. inv H; simplify.
      * left. exists x. split; [constructor; tauto|auto].
      * right; intros. inv H. inv H3; auto.
        eapply sem_pexpr_eval; eauto.
Qed.

Lemma sem_pred_expr_NEapp7 :
  forall f_p ps a b v,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    sem_pred_expr f_p a_sem ctx (NE.app a b) v ->
    sem_pred_expr f_p a_sem ctx a v
    \/ ((forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false)
         /\ sem_pred_expr f_p a_sem ctx b v).
Proof.
  intros.
  pose proof (sem_pred_expr_in_or_false _ _ a H) as YX.
  inv YX.
  - left. eapply sem_pred_expr_NEapp5; eauto.
  - right; split; auto. eapply sem_pred_expr_NEapp4; eauto.
Qed.

Lemma In_pexpr_eval :
  forall A f_p ps,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    forall (a: predicated A),
      (exists x, NE.In x a /\ sem_pexpr ctx (from_pred_op f_p (fst x)) true)
      \/ (forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false).
Proof.
  induction a; cbn in *.
  - pose proof (sem_pexpr_evaluable _ _ _ _ H (fst a)); simplify.
    destruct x.
    + left. exists a. split; auto. constructor.
    + right; intros. inv H0; auto.
  - inv IHa; simplify.
    + left. exists x. split; auto. apply NE.In_cons; auto.
    + pose proof (sem_pexpr_evaluable _ _ _ _ H (fst a)); simplify.
      destruct x.
      * left. exists a; split; auto. constructor; auto.
      * right; intros. inv H1. inv H4; auto.
Qed.

Lemma sem_pred_expr_map_not :
  forall A p ps y x0,
    eval_predf ps p = false ->
    NE.In x0 (NE.map (fun x => (p ∧ fst x, snd x)) y) ->
    eval_predf ps (@fst _ A x0) = false.
Proof.
  induction y; crush.
  - inv H0. simplify. rewrite eval_predf_Pand. rewrite H. auto.
  - inv H0. inv H2. cbn -[eval_predf]. rewrite eval_predf_Pand.
    rewrite H. auto. eauto.
Qed.

Lemma sem_pred_expr_map_Pand :
  forall f_p ps x v p,
    (forall x : positive, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
    eval_predf ps p = true ->
    sem_pred_expr f_p a_sem ctx x v ->
    sem_pred_expr f_p a_sem ctx
      (NE.map (fun x0 => (p ∧ fst x0, snd x0)) x) v.
Proof.
  induction x; crush.
  inv H1. simplify. constructor; eauto.
  simplify. replace true with (true && true) by auto.
  constructor; auto.
  eapply sem_pexpr_eval; eauto.
  inv H1. simplify. constructor; eauto.
  simplify. replace true with (true && true) by auto.
  constructor; auto.
  eapply sem_pexpr_eval; eauto.
  eapply sem_pred_expr_cons_false. cbn.
  replace false with (true && false) by auto. apply sem_pexpr_Pand; auto.
  eapply sem_pexpr_eval; eauto. eauto.
Qed.

Lemma sem_pred_expr_map_Pand2 :
  forall f_p ps x v p,
    (forall x : positive, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
    eval_predf ps p = true ->
    sem_pred_expr f_p a_sem ctx
      (NE.map (fun x0 => (p ∧ fst x0, snd x0)) x) v ->
    sem_pred_expr f_p a_sem ctx x v.
Proof.
  induction x; crush.
  - inv H1. destruct a; constructor; auto. eapply sem_pexpr_eval; eauto.
    eapply sem_pexpr_eval_inv in H5; eauto. rewrite eval_predf_Pand in H5.
    now rewrite H0 in H5.
  - inv H1.
    + destruct a; constructor; auto. eapply sem_pexpr_eval; eauto.
      eapply sem_pexpr_eval_inv in H7; eauto. rewrite eval_predf_Pand in H7.
      now rewrite H0 in H7.
    + destruct a; eapply sem_pred_expr_cons_false; eauto.
      eapply sem_pexpr_eval; eauto.
      eapply sem_pexpr_eval_inv in H7; eauto.
      rewrite eval_predf_Pand in H7.
      now rewrite H0 in H7.
Qed.

Lemma sem_pred_expr_app_predicated :
  forall f_p y x v p ps,
    sem_pred_expr f_p a_sem ctx x v ->
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    eval_predf ps p = true ->
    sem_pred_expr f_p a_sem ctx (app_predicated p y x) v.
Proof.
  intros * SEM PS EVAL. unfold app_predicated.
  eapply sem_pred_expr_NEapp2; eauto.
  intros. eapply sem_pred_expr_map_not; eauto.
  rewrite eval_predf_negate. rewrite EVAL. auto.
  eapply sem_pred_expr_map_Pand; eauto.
Qed.

Lemma sem_pred_expr_app_predicated2 :
  forall f_p y x v p ps,
    sem_pred_expr f_p a_sem ctx (app_predicated p y x) v ->
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    eval_predf ps p = true ->
    sem_pred_expr f_p a_sem ctx x v.
Proof.
  intros * SEM PS EVAL. unfold app_predicated in *.
  eapply sem_pred_expr_NEapp6 in SEM; eauto.
  - eapply sem_pred_expr_map_Pand2; eauto.
  - intros. eapply sem_pred_expr_map_not; [|eassumption].
    rewrite eval_predf_negate. now rewrite EVAL.
Qed.

Lemma sem_pred_expr_ident :
  forall ps l l_,
    sem_pred_expr ps sem_ident ctx l l_ ->
    forall (v: B),
      a_sem ctx l_ v ->
      sem_pred_expr ps a_sem ctx l v.
Proof.
  induction 1.
  - intros. constructor; auto. inv H0. auto.
  - intros. apply sem_pred_expr_cons_false; auto.
  - intros. inv H0. constructor; auto.
Qed.

Lemma sem_pred_expr_ident2 :
  forall ps l v,
    sem_pred_expr ps a_sem ctx l v ->
    exists l_, sem_pred_expr ps sem_ident ctx l l_ /\ a_sem ctx l_ v.
Proof.
  induction 1.
  - exists e; split; auto. constructor; auto. constructor.
  - inversion_clear IHsem_pred_expr as [x IH].
    inversion_clear IH as [SEM EVALS].
    exists x; split; auto. apply sem_pred_expr_cons_false; auto.
  - exists e; split; auto; constructor; auto; constructor.
Qed.

Fixpoint of_elist (e: expression_list): list expression :=
  match e with
  | Econs a b => a :: of_elist b
  | Enil => nil
  end.

Fixpoint to_elist (e: list expression): expression_list :=
  match e with
  | a :: b => Econs a (to_elist b)
  | nil => Enil
  end.

Lemma sem_val_list_elist :
  forall l j,
    sem_val_list ctx (to_elist l) j ->
    Forall2 (sem_value ctx) l j.
Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

Lemma sem_val_list_elist2 :
  forall l j,
    Forall2 (sem_value ctx) l j ->
    sem_val_list ctx (to_elist l) j.
Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

Lemma sem_val_list_elist3 :
  forall l j,
    sem_val_list ctx l j ->
    Forall2 (sem_value ctx) (of_elist l) j.
Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

Lemma sem_val_list_elist4 :
  forall l j,
    Forall2 (sem_value ctx) (of_elist l) j ->
    sem_val_list ctx l j.
Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

Lemma sem_pred_expr_predicated_map :
  forall pr (f: A -> B) pred pred',
    sem_pred_expr pr sem_ident ctx pred pred' ->
    sem_pred_expr pr sem_ident ctx (predicated_map f pred) (f pred').
Proof.
  induction pred; unfold predicated_map; intros.
  - inv H. inv H3. constructor; eauto. constructor.
  - inv H. inv H5. constructor; eauto. constructor.
    eapply sem_pred_expr_cons_false; eauto.
Qed.

Lemma sem_pred_expr_predicated_map2 :
  forall pr (f: A -> B) pred x,
    sem_pred_expr pr sem_ident ctx (predicated_map f pred) x ->
    exists pred', sem_pred_expr pr sem_ident ctx pred pred' /\ x = f pred'.
Proof.
  induction pred; unfold predicated_map; intros.
  - cbn in *. inv H. inv H5. destruct a. exists a.
    split; auto. constructor; auto. constructor.
  - cbn in *. inv H. destruct a. inv H6. cbn [fst snd] in *.
    exists a; repeat constructor; auto.
    exploit IHpred; eauto; simplify.
    exists x0; split; auto.
    destruct a. apply sem_pred_expr_cons_false; auto.
Qed.

End PROOF.

Section PROOF.

Context (G: Type).
Context (ctx: @Abstr.ctx G).

Lemma sem_pred_expr_predicated_prod :
  forall A B pr (a: predicated A) (b: predicated B) a' b',
    sem_pred_expr pr sem_ident ctx a a' ->
    sem_pred_expr pr sem_ident ctx b b' ->
    sem_pred_expr pr sem_ident ctx (predicated_prod a b) (a', b').
Proof.
  induction a; intros.
  - inv H. inv H4. unfold predicated_prod.
    generalize dependent b. induction b; intros.
    + cbn. destruct_match. inv Heqp. inv H0. inv H6.
      constructor. simplify. replace true with (true && true) by auto.
      eapply sem_pexpr_Pand; eauto. constructor.
    + inv H0. inv H6. cbn. constructor; cbn.
      replace true with (true && true) by auto.
      constructor; auto. constructor.
      eapply sem_pred_expr_cons_false; eauto. cbn.
      replace false with (true && false) by auto.
      apply sem_pexpr_Pand; auto.
  - unfold predicated_prod. simplify.
    rewrite NE.app_NEmap.
    inv H. eapply sem_pred_expr_NEapp.
    { induction b; crush.
      destruct a. inv H0. constructor.
      replace true with (true && true) by auto.
      eapply sem_pexpr_Pand; auto. inv H6. inv H7.
      constructor.

      destruct a. inv H0. constructor.
      replace true with (true && true) by auto.
      constructor; auto. inv H8. inv H6. constructor.

      specialize (IHb H8). eapply sem_pred_expr_cons_false; auto.
      replace false with (true && false) by auto.
      apply sem_pexpr_Pand; auto.
    }
    { exploit IHa. eauto. eauto. intros.
      unfold predicated_prod in *.
      eapply sem_pred_expr_NEapp3; eauto; [].
      clear H. clear H0.
      induction b.
      { intros. inv H. destruct a. simpl.
        constructor; tauto. }
      { intros. inv H. inv H1. destruct a. simpl.
        constructor; tauto. eauto. } }
Qed.

Lemma sem_pred_expr_predicated_pair :
  forall A B f a b a1 b0,
    sem_pred_expr f sem_ident ctx
         (NE.map
            (fun x : Predicate.pred_op * A * (Predicate.pred_op * B) =>
             let (y, y0) := x in let (a, b) := y in let (c, d) := y0 in (a ∧ c, (b, d)))
            (GiblePargenproofEquiv.NE.map (fun x : pred_op * B => (a, x)) b)) (a1, b0) ->
    sem_pred_expr f sem_ident ctx (NE.singleton a) a1.
Proof.
  induction b.
  - cbn; intros. inv H. repeat destr. inv Heqp. inv H0. inv H3. constructor.
    inv H1; auto. constructor.
  - cbn in *; intros. inv H; repeat destr; inv H0. inv H5. inv H3.
    repeat (constructor; auto).
    eapply IHb; eauto.
Qed.

Lemma sem_pred_expr_predicated_pair2 :
  forall A B f ps a b a1 b0,
    (forall x, sem_pexpr ctx (get_forest_p' x f) (ps !! x)) ->
    sem_pred_expr f sem_ident ctx
         (NE.map
            (fun x : Predicate.pred_op * A * (Predicate.pred_op * B) =>
             let (y, y0) := x in let (a, b) := y in let (c, d) := y0 in (a ∧ c, (b, d)))
            (GiblePargenproofEquiv.NE.map (fun x : pred_op * B => (a, x)) b)) (a1, b0) ->
    sem_pred_expr f sem_ident ctx b b0.
Proof.
  induction b.
  - cbn; intros * HFOREST **. inv H. repeat destr. inv Heqp. inv H0. inv H3. constructor.
    inv H1; auto. constructor.
  - cbn in *; intros * HFOREST **. inv H; repeat destr; inv H0. inv H5. inv H3.
    repeat (constructor; auto).
    inv H3. inv H0.
    + exploit sem_pred_expr_predicated_pair; eauto; intros. inv H0.
      eapply sem_pexpr_eval_inv in H; eauto.
      eapply sem_pexpr_eval_inv in H4; eauto. now rewrite H in H4.
    + eapply sem_pred_expr_cons_false; eauto. 
Qed.

Lemma sem_pred_expr_predicated_false :
  forall A B f ps a b b0,
    (forall x, sem_pexpr ctx (get_forest_p' x f) (ps !! x)) ->
    (forall x, NE.In x (NE.map
      (fun x : Predicate.pred_op * A * (Predicate.pred_op * B) =>
        let (y, y0) := x in let (a, b) := y in let (c, d) := y0 in (a ∧ c, (b, d)))
          (GiblePargenproofEquiv.NE.map (fun x : pred_op * B => (a, x)) b)) -> eval_predf ps (fst x) = false) ->
    sem_pred_expr f sem_ident ctx b b0 ->
    eval_predf ps (fst a) = false.
Proof.
  induction b; cbn; intros.
  - inv H1. eapply sem_pexpr_eval_inv in H3; eauto.
    repeat destr. inv Heqp. exploit H0. constructor. intros.
    cbn [fst snd] in *. rewrite eval_predf_Pand in H1.
    eapply andb_false_iff in H1. inv H1; auto. now rewrite H3 in H2.
  - inv H1.
    * exploit H0. constructor. left. eauto. intros.
      repeat destr. cbn [fst snd] in *. rewrite eval_predf_Pand in H1.
      eapply andb_false_iff in H1. inv H1; auto.
      eapply sem_pexpr_eval_inv in H5; [|eassumption].
      now rewrite H2 in H5.
    * eapply IHb; eauto. intros.
      exploit H0; eauto. constructor; tauto.
Qed.

Lemma sem_pred_expr_predicated_prod2 :
  forall A B f ps (a: predicated A) (b: predicated B) x,
    (forall x, sem_pexpr ctx (get_forest_p' x f) (ps !! x)) ->
    sem_pred_expr f sem_ident ctx (predicated_prod a b) x ->
    sem_pred_expr f sem_ident ctx a (fst x)
    /\ sem_pred_expr f sem_ident ctx b (snd x).
Proof.
  induction a; intros.
  - generalize dependent x. generalize dependent b. induction b; intros.
    + cbn in *; repeat destr; destruct a, a0. inv Heqp. inv Heqp0.
      inv H0. inv H6; split.
      * constructor. inv H4. tauto. constructor.
      * cbn in *. inv H4. constructor. tauto. constructor.
    + destruct x; cbn in *. repeat destr. inv Heqp0. inv H0.
      * inv H6. inv H7. repeat (constructor; auto).
      * exploit IHb; eauto; intros. inv H0. cbn in *. inv H6.
        inv H3. inv H1. eapply sem_pexpr_det in H0; try eassumption. discriminate.
        apply similar_refl. split; auto.
        apply sem_pred_expr_cons_false; auto.
  - destruct x; cbn [fst snd] in *.
    unfold predicated_prod in H0. cbn in H0.
    rewrite NE.app_NEmap in H0.
    eapply sem_pred_expr_NEapp7 in H0; [|eassumption]. inv H0.
    + exploit sem_pred_expr_predicated_pair; eauto.
      exploit sem_pred_expr_predicated_pair2; eauto.
      intros. split; auto. inv H2. constructor; auto.
    + inv H1.
      assert (sem_pred_expr f sem_ident ctx a0 a1 /\ sem_pred_expr f sem_ident ctx b b0).
      { replace a1 with (fst (a1, b0)) by auto. replace b0 with (snd (a1, b0)) by auto.
        eapply IHa; eauto. } inv H1.
      split; auto.
      exploit sem_pred_expr_predicated_false; eauto. intros.
      exploit H0; eauto. intros. eapply sem_pexpr_eval_inv in H5; eauto.
      intros. destruct a. apply sem_pred_expr_cons_false; auto.
      eapply sem_pexpr_eval; eauto.
Qed.

Lemma sem_pred_expr_seq_app :
  forall A B (f: predicated (A -> B)) ps l f_ l_,
    sem_pred_expr ps sem_ident ctx l l_ ->
    sem_pred_expr ps sem_ident ctx f f_ ->
    sem_pred_expr ps sem_ident ctx (seq_app f l) (f_ l_).
Proof.
  unfold seq_app; intros.
  remember (fun x : (A -> B) * A => fst x (snd x)) as app.
  replace (f_ l_) with (app (f_, l_)) by (rewrite Heqapp; auto).
  eapply sem_pred_expr_predicated_map. eapply sem_pred_expr_predicated_prod; auto.
Qed.

Lemma sem_pred_expr_seq_app2 :
  forall A B (f: predicated (A -> B)) ps pr l x_,
    (forall x, sem_pexpr ctx (get_forest_p' x ps) (pr !! x)) ->
    sem_pred_expr ps sem_ident ctx (seq_app f l) x_ ->
    exists l_ f_,
      x_ = f_ l_
      /\ sem_pred_expr ps sem_ident ctx l l_
      /\ sem_pred_expr ps sem_ident ctx f f_.
Proof.
  unfold seq_app; intros.
  remember (fun x : (A -> B) * A => fst x (snd x)) as app.
  exploit sem_pred_expr_predicated_map2; eauto; simplify.
  exploit sem_pred_expr_predicated_prod2; eauto; simplify.
  eauto.
Qed.

Lemma sem_pred_expr_map :
  forall A B ps (f: A -> B) y v,
    sem_pred_expr ps sem_ident ctx y v ->
    sem_pred_expr ps sem_ident ctx (NE.map (fun x => (fst x, f (snd x))) y) (f v).
Proof.
  induction y; crush. inv H. constructor; crush. inv H3. constructor.
  inv H. inv H5. constructor; eauto. constructor.
  eapply sem_pred_expr_cons_false; eauto.
Qed.

Lemma sem_pred_expr_flap :
  forall A B C (f: predicated (A -> B -> C)) ps l f_,
    sem_pred_expr ps sem_ident ctx f f_ ->
    sem_pred_expr ps sem_ident ctx (flap f l) (f_ l).
Proof.
  induction f. unfold flap; intros. inv H. inv H3.
  constructor; eauto. constructor.
  intros. inv H. cbn.
  constructor; eauto. inv H5. constructor.
  eapply sem_pred_expr_cons_false; eauto.
Qed.

Lemma sem_pred_expr_flap2 :
  forall A B C (f: predicated (A -> B -> C)) ps l1 l2 f_,
    sem_pred_expr ps sem_ident ctx f f_ ->
    sem_pred_expr ps sem_ident ctx (flap2 f l1 l2) (f_ l1 l2).
Proof.
  induction f. unfold flap2; intros. inv H. inv H3.
  constructor; eauto. constructor.
  intros. inv H. cbn.
  constructor; eauto. inv H5. constructor.
  eapply sem_pred_expr_cons_false; eauto.
Qed.

Lemma sem_pred_expr_flap2_2 :
  forall A B C (f: predicated (A -> B -> C)) ps l1 l2 x,
    sem_pred_expr ps sem_ident ctx (flap2 f l1 l2) x ->
    exists f_, sem_pred_expr ps sem_ident ctx f f_ /\ f_ l1 l2 = x.
Proof.
  induction f; cbn; intros.
  - inv H; destruct a; cbn in *. inv H5. eexists; split; eauto.
    constructor; auto. constructor.
  - destruct a. cbn [fst snd] in *. inv H.
    + inv H6. eexists; split; eauto. constructor; auto. constructor.
    + exploit IHf; eauto; simplify.
      eexists; split; eauto. eapply sem_pred_expr_cons_false; eauto.
Qed.

Lemma sem_pred_expr_seq_app_val :
  forall A B V (s: @Abstr.ctx G -> B -> V -> Prop)
      (f: predicated (A -> B))
      ps l v f_ l_,
    sem_pred_expr ps sem_ident ctx l l_ ->
    sem_pred_expr ps sem_ident ctx f f_ ->
    s ctx (f_ l_) v ->
    sem_pred_expr ps s ctx (seq_app f l) v.
Proof.
  intros. eapply sem_pred_expr_ident; [|eassumption].
  eapply sem_pred_expr_seq_app; eauto.
Qed.

Lemma sem_pred_expr_seq_app_val2 :
  forall A B V (s: @Abstr.ctx G -> B -> V -> Prop)
      (f: predicated (A -> B)) ps pr l v,
    (forall x, sem_pexpr ctx (get_forest_p' x ps) (pr !! x)) ->
    sem_pred_expr ps s ctx (seq_app f l) v ->
    exists f_ l_,
      sem_pred_expr ps sem_ident ctx l l_
      /\ sem_pred_expr ps sem_ident ctx f f_
      /\ s ctx (f_ l_) v.
Proof.
  intros; exploit sem_pred_expr_ident2; eauto; simplify.
  exploit sem_pred_expr_seq_app2; eauto; simplify.
  eauto.
Qed.

Fixpoint Eapp a b :=
  match a with
  | Enil => b
  | Econs ax axs => Econs ax (Eapp axs b)
  end.

Lemma Eapp_right_nil :
  forall a, Eapp a Enil = a.
Proof. induction a; cbn; try rewrite IHa; auto. Qed.

Lemma Eapp_left_nil :
  forall a, Eapp Enil a = a.
Proof. auto. Qed.

Lemma sem_pred_expr_cons_pred_expr :
  forall pr s s' a e,
    sem_pred_expr pr sem_ident ctx s s' ->
    sem_pred_expr pr sem_ident ctx a e ->
    sem_pred_expr pr sem_ident ctx (cons_pred_expr a s) (Econs e s').
Proof.
  intros. unfold cons_pred_expr.
  replace (Econs e s') with ((uncurry Econs) (e, s')) by auto.
  eapply sem_pred_expr_predicated_map.
  eapply sem_pred_expr_predicated_prod; eauto.
Qed.

Lemma sem_pred_expr_cons_pred_expr2 :
  forall ps pr s a x,
    (forall x, sem_pexpr ctx (get_forest_p' x pr) (ps !! x)) ->
    sem_pred_expr pr sem_ident ctx (cons_pred_expr a s) x ->
    exists s' e, sem_pred_expr pr sem_ident ctx s s'
      /\ sem_pred_expr pr sem_ident ctx a e
      /\ x = Econs e s'.
Proof.
  intros * HPRED **. unfold cons_pred_expr in *.
  exploit sem_pred_expr_predicated_map2; eauto; simplify.
  exploit sem_pred_expr_predicated_prod2; eauto; simplify.
  destruct x0; cbn in *.
  eexists; simplify; eauto.
Qed.

Lemma sem_pred_expr_fold_right :
  forall pr s a a' s',
    sem_pred_expr pr sem_ident ctx s s' ->
    Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a') ->
    sem_pred_expr pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s').
Proof.
  induction a; crush. inv H0. inv H5. destruct a'; crush. destruct a'; crush.
  inv H3. eapply sem_pred_expr_cons_pred_expr; eauto.
  inv H0. destruct a'; crush. inv H3.
  eapply sem_pred_expr_cons_pred_expr; eauto.
Qed.

Lemma Eapp_Econs :
  forall x y z,
    Eapp x (Econs y z) = Eapp (Eapp x (Econs y Enil)) z.
Proof.
  induction x; cbn; intros.
  - auto.
  - f_equal. auto.
Qed.

Lemma Eapp_Econs_eq' :
  forall b' a' x,
    Eapp b' (Econs x Enil) = Eapp a' (Econs x Enil) -> b' = a'.
Proof.
  induction b'; cbn; intros.
  - destruct a'; auto. cbn in *.
    inv H. destruct a'; eauto. cbn in *. discriminate.
  - cbn in *. destruct a'. cbn in *. inv H.
    { exfalso. destruct b'; cbn in *; discriminate. }
    cbn in *. inv H. eauto. eapply IHb' in H2. subst. auto.
Qed.

Lemma Eapp_Econs_eq :
  forall s' a' b',
    Eapp a' s' = Eapp b' s' ->
    a' = b'.
Proof.
  induction s'; cbn; intros.
  - rewrite ! Eapp_right_nil in H; auto.
  - rewrite Eapp_Econs in H. symmetry in H.
    rewrite Eapp_Econs in H. eapply IHs' in H.
    eapply Eapp_Econs_eq'; eauto.
Qed.

Lemma sem_pred_expr_fold_right2' :
  forall ps pr s a x s',
    (forall x, sem_pexpr ctx (get_forest_p' x pr) (ps !! x)) ->
    sem_pred_expr pr sem_ident ctx s s' ->
    sem_pred_expr pr sem_ident ctx (NE.fold_right cons_pred_expr s a) x ->
    exists a', x = (Eapp a' s') /\ Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a').
Proof.
  induction a; cbn; intros.
  - exploit sem_pred_expr_cons_pred_expr2; eauto; simplify.
    eapply sem_pred_expr_ident_det in H0; eauto; subst.
    exists (Econs x1 Enil); split; auto.
    constructor; [auto|constructor].
  - exploit sem_pred_expr_cons_pred_expr2; eauto; simplify.
    exploit IHa; eauto; simplify.
    exists (Econs x1 x); split; auto.
    constructor; auto.
Qed.

Lemma sem_pred_expr_fold_right2 :
  forall ps pr s a a' s',
    (forall x, sem_pexpr ctx (get_forest_p' x pr) (ps !! x)) ->
    sem_pred_expr pr sem_ident ctx s s' ->
    sem_pred_expr pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s') ->
    Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a').
Proof.
  intros. exploit sem_pred_expr_fold_right2'. eauto. eapply H0. eauto.
  simplify. eapply Eapp_Econs_eq in H2; subst; auto.
Qed.

Lemma of_to_list :
  forall x, of_elist (to_elist x) = x.
Proof.
  induction x; auto.
  cbn. rewrite IHx; auto.
Qed.

Lemma sem_pred_expr_merge :
  forall ps l args,
    Forall2 (sem_pred_expr ps sem_ident ctx) args l ->
    sem_pred_expr ps sem_ident ctx (merge args) (to_elist l).
Proof.
  induction l; intros.
  - inv H. cbn; repeat constructor.
  - inv H. cbn. unfold merge.
    exploit NE.of_list_exists. intros [x0 HOFLIST]. rewrite HOFLIST.
    replace (Econs a (to_elist l)) with (Eapp (Econs a (to_elist l)) Enil)
      by apply Eapp_right_nil.
    eapply sem_pred_expr_fold_right. constructor; auto. constructor. constructor.
    cbn. apply NE.of_list_to_list in HOFLIST.
    setoid_rewrite HOFLIST. constructor; eauto.
    rewrite of_to_list. auto.
Qed.

Lemma sem_pred_expr_merge2 :
  forall pr ps l l',
    (forall x, sem_pexpr ctx (get_forest_p' x pr) (ps !! x)) ->
    sem_pred_expr pr sem_ident ctx (merge l) l' ->
    Forall2 (sem_pred_expr pr sem_ident ctx) l (of_elist l').
Proof.
  induction l; intros * HPEXPR **; crush.
  - unfold merge in *; cbn in *.
    inv H. inv H5. constructor.
  - unfold merge in H.
    pose proof (NE.of_list_exists _ l a) as Y.
    inversion_clear Y as [x HNE]. rewrite HNE in H.
    erewrite <- (NE.of_list_to_list _ (a :: l)) by eassumption.
    apply sem_pred_expr_fold_right2 with
      (s := (NE.singleton (T, Enil)))
      (s' := Enil)
      (ps := ps); auto.
    repeat constructor.
    rewrite Eapp_right_nil. auto.
Qed.

(* [[id:f307d227-d0e9-49a0-823f-2d7e0db76972]] *)
Lemma sem_merge_list :
  forall f rs ps m args,
    sem ctx f ((mk_instr_state rs ps m), None) ->
    sem_pred_expr (forest_preds f) sem_val_list ctx
      (merge (list_translation args f)) (rs ## args).
Proof.
  induction args; intros * **; crush. cbn. constructor; constructor.
  unfold merge. specialize (IHargs H).
  eapply sem_pred_expr_ident2 in IHargs.
  inversion_clear IHargs as [l_ [HSEM HVAL]].
  destruct_match; [|exfalso; eapply NE.of_list_contra; eauto].
  destruct args; cbn -[NE.of_list] in *.
  - unfold merge in *. simplify.
    inv H. inv H6. specialize (H a).
    eapply sem_pred_expr_ident2 in H.
    inversion_clear H as [l_2 [HSEM2 HVAL2]].
    unfold cons_pred_expr.
    eapply sem_pred_expr_ident.
    eapply sem_pred_expr_predicated_map.
    eapply sem_pred_expr_predicated_prod; [eassumption|repeat constructor].
    repeat constructor; auto.
  - pose proof (NE.of_list_exists2 _ (list_translation args f) (f #r (Reg r)) (f #r (Reg a))) as Y.
    inversion_clear Y as [x [Y1 Y2]]. rewrite Heqo in Y1. inv Y1.
    inversion_clear H as [? ? ? ? ? ? REG PRED MEM EXIT].
    inversion_clear REG as [? ? ? REG'].
    inversion_clear PRED as [? ? ? PRED'].
    pose proof (REG' a) as REGa. pose proof (REG' r) as REGr.
    exploit sem_pred_expr_ident2; [exact REGa|].
    intro REGI'; inversion_clear REGI' as [a' [SEMa SEMa']].
    exploit sem_pred_expr_ident2; [exact REGr|].
    intro REGI'; inversion_clear REGI' as [r' [SEMr SEMr']].
    apply sem_pred_expr_ident with (l_ := Econs a' l_); [|constructor; auto].
    replace (Econs a' l_) with (Eapp (Econs a' l_) Enil) by (now apply Eapp_right_nil).
    apply sem_pred_expr_fold_right; eauto.
    repeat constructor.
    constructor; eauto.
    erewrite NE.of_list_to_list; eauto.
    eapply sem_pred_expr_merge2; auto.
    eauto.
Qed.

Lemma sem_pred_expr_list_translation :
  forall args f i,
    sem ctx f (i, None) ->
    exists l,
      Forall2 (sem_pred_expr (forest_preds f) sem_ident ctx) (list_translation args f) l
      /\ sem_val_list ctx (to_elist l) ((is_rs i)##args).
Proof.
  induction args; intros.
  - exists nil; cbn; split; auto; constructor.
  - exploit IHargs; try eassumption; intro EX.
    inversion_clear EX as [l [FOR SEM]].
    destruct i as [rs' m' ps'].
    inversion_clear H as [? ? ? ? ? ? REGSET PREDSET MEM EXIT].
    inversion_clear REGSET as [? ? ? REG].
    pose proof (REG a).
    exploit sem_pred_expr_ident2; eauto; intro IDENT.
    inversion_clear IDENT as [l_ [SEMP SV]].
    exists (l_ :: l). split. constructor; auto.
    cbn; constructor; auto.
Qed.

(*|
This is currently not provable as it needs mutual exclusion of the predicate
expression.
|*)

Lemma from_predicated_sem_pred_expr_true:
  forall preds pe,
    (forall x, NE.In x pe -> sem_pexpr ctx (from_pred_op preds (fst x)) false) ->
    sem_pexpr ctx (from_predicated true preds pe) true.
Proof.
  induction pe; cbn; repeat destr; unfold "→"; intros.
  - constructor. left. inv Heqp.
    replace true with (negb false) by auto.
    apply sem_pexpr_negate.
    replace p with (fst (p, p0)) by auto.
    apply H. constructor.
  - constructor.
    constructor. left.
    replace true with (negb false) by auto.
    apply sem_pexpr_negate. inv Heqp.
    replace p with (fst (p, p0)) by auto.
    apply H. constructor; tauto.
    apply IHpe; intros. apply H. constructor; tauto.
Qed.

Lemma Pimplies_eval_pred :
  forall ps x y,
    x ⇒ y -> eval_predf ps x = true -> eval_predf ps y = true.
Proof. eauto. Qed.

Lemma from_predicated_sem_pred_expr :
  forall preds ps pe b,
    (forall x, sem_pexpr ctx (get_forest_p' x preds) (ps !! x)) ->
    predicated_mutexcl pe ->
    sem_pred_expr preds sem_pred ctx pe b ->
    sem_pexpr ctx (from_predicated true preds pe) b.
Proof.
  induction pe.
  - intros * HPREDS **. inv H0. cbn. unfold "→".
    destruct b; cbn. constructor. right. constructor. auto.
    constructor. replace false with (negb true) by auto. now apply sem_pexpr_negate.
    constructor; auto.
  - destruct b.
    + intros * HPREDS **; cbn; unfold "→"; repeat destr. inv Heqp. inv H0.
      * constructor. constructor. right. constructor; auto.
        apply from_predicated_sem_pred_expr_true.
        intros.
        assert (NE.In x (NE.cons (p, p0) pe)) by (constructor; tauto).
        assert ((p, p0) <> x).
        { unfold not; intros. inv H2. inv H. inv H3; auto. }
        inv H. specialize (H3 _ _ ltac:(constructor; left; auto) H1 H2).
        destruct x; cbn [fst snd] in *.
        eapply sem_pexpr_eval_inv in H6; eauto.
        eapply sem_pexpr_eval; eauto.
        apply negb_inj; cbn.
        rewrite <- eval_predf_negate.
        eapply H3; eauto.
      * constructor; eauto. constructor. left.
        replace true with (negb false) by auto. now apply sem_pexpr_negate.
        eauto using predicated_cons.
    + intros * HPREDS **; cbn in *; unfold "→"; repeat destr. inv Heqp. inv H0.
      * constructor. left. constructor. replace false with (negb true) by auto. now apply sem_pexpr_negate.
        constructor; auto.
      * constructor. right. eauto using predicated_cons.
Qed.

Lemma from_predicated_sem_pred_expr2':
  forall preds ps pe b b',
    (forall x, sem_pexpr ctx (get_forest_p' x preds) (ps !! x)) ->
    predicated_mutexcl pe ->
    sem_pexpr ctx (from_predicated true preds pe) b ->
    sem_pred_expr preds sem_pred ctx pe b' ->
    b = b'.
Proof.
  induction pe; intros * HPREDS **; cbn in *; repeat destr.
  - inv H0. inv H1; inv H5.
    + replace true with (negb false) in H0 by auto. apply sem_pexpr_negate2 in H0.
      eapply sem_pexpr_eval_inv in H4; eauto.
      eapply sem_pexpr_eval_inv in H0; eauto.
      now rewrite H0 in H4.
    + inv H0. eapply sem_pred_det; eauto. reflexivity.
    + inv H1. inv H6. eapply sem_pred_det; eauto. reflexivity.
  - inv Heqp. inv H0; [inv H5|]; [inv H0| |].
    + inv H5. inv H1.
      * eapply sem_pred_det; eauto. reflexivity.
      * replace false with (negb true) in H4 by auto. apply sem_pexpr_negate2 in H4.
        eapply sem_pexpr_det in H4; eauto; [discriminate|reflexivity].
    + inv H1; eauto using predicated_cons.
      exploit from_predicated_sem_pred_expr_true.
      instantiate (2 := pe). instantiate (1 := preds).
      intros.
      assert (NE.In x (NE.cons (p, p0) pe)) by (constructor; tauto).
      inv H.
      assert ((p, p0) <> x).
      { unfold not; intros. subst. inv H4. contradiction. }
      specialize (H3 _ _ ltac:(constructor; left; auto) H2 H).
      destruct x; cbn in *.
      eapply sem_pexpr_eval; eauto. eapply sem_pexpr_eval_inv in H7; eauto.
      apply negb_inj; cbn.
      rewrite <- eval_predf_negate.
      eapply H3; eauto.
      intros. eapply sem_pexpr_det in H0; now try eapply H1.      
    + inv H4. inv H2; inv H1; eauto using predicated_cons.
      * replace true with (negb false) in H0 by auto.
        apply sem_pexpr_negate2 in H0.
        eapply sem_pexpr_det in H0; now try apply H8.
      * inv H0. eapply sem_pred_det in H9; now eauto.
Qed.

Lemma from_predicated_inv_exists_true :
  forall ps pe,
    eval_predf ps (from_predicated_inv pe) = true ->
    exists y, NE.In y pe /\ (eval_predf ps (fst y) = true).
Proof.
  induction pe; cbn -[eval_predf]; intros; repeat destr; inv Heqp.
  - exists (p, p0); intuition constructor.
  - rewrite eval_predf_Por in H. apply orb_prop in H. inv H.
    + exists (p, p0); intuition constructor; tauto.
    + exploit IHpe; auto; simplify.
      exists x; intuition constructor; tauto.
Qed.

Lemma from_predicated_sem_pred_expr2:
  forall preds ps pe b,
    (forall x, sem_pexpr ctx (get_forest_p' x preds) (ps !! x)) ->
    predicated_mutexcl pe ->
    sem_pexpr ctx (from_predicated true preds pe) b ->
    eval_predf ps (from_predicated_inv pe) = true ->
    sem_pred_expr preds sem_pred ctx pe b.
Proof.
  induction pe.
  - cbn -[eval_predf]; intros; repeat destr. inv Heqp. inv H1. inv H6.
    + replace true with (negb false) in H1 by auto.
      apply sem_pexpr_negate2 in H1.
      eapply sem_pexpr_eval_inv in H1; eauto.
      now rewrite H1 in H2.
    + inv H1. constructor; auto. eapply sem_pexpr_eval; eauto.
    + inv H7. constructor; auto. eapply sem_pexpr_eval; eauto.
  - cbn -[eval_predf]; intros; repeat destr. inv Heqp.
    rewrite eval_predf_Por in H2. apply orb_prop in H2. inv H2.
    + inv H1. inv H6.
      * inv H1. inv H6. constructor; eauto using sem_pexpr_eval.
      * (* contradiction, because eval_predf p true means that all other
        implications in H1 are false, therefore sem_pexpr will evaluate to
        true. *)
        exploit from_predicated_sem_pred_expr_true.
        -- instantiate (2 := pe). instantiate (1 := preds).
           intros. destruct x.
           assert (HIN1: NE.In (p, p0) (NE.cons (p, p0) pe))
             by (intuition constructor; tauto).
           assert (HIN2: NE.In (p1, p2) (NE.cons (p, p0) pe))
             by (intuition constructor; tauto).
           assert (HNEQ: (p, p0) <> (p1, p2)).
           { unfold not; inversion 1; subst. clear H4. inv H0. inv H5. contradiction. }
           cbn. eapply sem_pexpr_eval; eauto.
           symmetry. rewrite <- negb_involutive. symmetry.
           rewrite <- eval_predf_negate. rewrite <- negb_involutive.
           f_equal; cbn.
           inv H0. specialize (H4 _ _ HIN1 HIN2 HNEQ). cbn in H4.
           eapply H4; auto.
        -- intros. eapply sem_pexpr_det in H1; now eauto.
      * inv H5. inv H2.
        -- eapply sem_pexpr_negate2' in H1. eapply sem_pexpr_eval_inv in H; eauto.
           now rewrite H in H3.
        -- inv H1. constructor; eauto using sem_pexpr_eval.
    + assert (eval_predf ps p = false).
      { case_eq (eval_predf ps p); auto; intros HCASE; exfalso.
        exploit from_predicated_inv_exists_true; eauto; simplify.
        destruct x; cbn -[eval_predf] in *.
        assert (HNEQ: (p, p0) <> (p1, p2)).
        { unfold not; intros. inv H4. inv H0. inv H6. contradiction. }
        assert (HIN2: NE.In (p1, p2) (NE.cons (p, p0) pe))
          by (intuition constructor; tauto).
        assert (HIN1: NE.In (p, p0) (NE.cons (p, p0) pe))
          by (intuition constructor; tauto).
        inv H0. specialize (H4 _ _ HIN1 HIN2 HNEQ). eapply H4 in HCASE. cbn in HCASE.
        rewrite negate_correct in HCASE. now setoid_rewrite H5 in HCASE.
      }
      inv H1. inv H7.
      * inv H1.
        apply sem_pexpr_negate2' in H6. eapply sem_pexpr_eval_inv in H6; eauto.
        now rewrite H2 in H6.
      * eapply sem_pred_expr_cons_false;
          eauto using sem_pexpr_eval, predicated_cons.
      * inv H6. inv H4; eapply sem_pred_expr_cons_false;
          eauto using sem_pexpr_eval, predicated_cons.
Qed.

End PROOF.
