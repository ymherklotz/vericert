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

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

#[local] Opaque simplify.
#[local] Opaque deep_simplify.


Definition evaluable {A B C} (sem: ctx -> B -> C -> Prop) (ctx: @ctx A) p := exists b, sem ctx p b.

Definition p_evaluable {A} := @evaluable A _ _ sem_pexpr.

Definition evaluable_expr {A} := @evaluable A _ _ sem_pred.

Definition all_evaluable {A B} (ctx: @ctx A) f_p (l: predicated B) :=
  forall p y, NE.In (p, y) l -> p_evaluable ctx (from_pred_op f_p p).

Definition all_evaluable2 {A B C} (ctx: @ctx A) (sem: Abstr.ctx -> B -> C -> Prop) (l: predicated B) :=
  forall p y, NE.In (p, y) l -> evaluable sem ctx y.

Definition pred_forest_evaluable {A} (ctx: @ctx A) (ps: PTree.t pred_pexpr) :=
  forall i p, ps ! i = Some p -> p_evaluable ctx p.

Definition forest_evaluable {A} (ctx: @ctx A) (f: forest) :=
  pred_forest_evaluable ctx f.(forest_preds).

Lemma all_evaluable_cons :
  forall A B pr ctx b a,
    all_evaluable ctx pr (NE.cons a b) ->
    @all_evaluable A B ctx pr b.
Proof.
  unfold all_evaluable; intros.
  enough (NE.In (p, y) (NE.cons a b)); eauto.
  constructor; tauto.
Qed.

Lemma all_evaluable2_cons :
  forall A B C sem ctx b a,
    all_evaluable2 ctx sem (NE.cons a b) ->
    @all_evaluable2 A B C ctx sem b.
Proof.
  unfold all_evaluable2; intros.
  enough (NE.In (p, y) (NE.cons a b)); eauto.
  constructor; tauto.
Qed.

Lemma all_evaluable_cons2 :
  forall A B pr ctx b a p,
    @all_evaluable A B ctx pr (NE.cons (p, a) b) ->
    p_evaluable ctx (from_pred_op pr p).
Proof.
  unfold all_evaluable; intros.
  eapply H. constructor; eauto.
Qed.

Lemma all_evaluable2_cons2 :
  forall A B C sem ctx b a p,
    @all_evaluable2 A B C ctx sem (NE.cons (p, a) b) ->
    evaluable sem ctx a.
Proof.
  unfold all_evaluable; intros.
  eapply H. constructor; eauto.
Qed.

Lemma all_evaluable_cons3 :
  forall A B pr ctx b p a,
    all_evaluable ctx pr b ->
    p_evaluable ctx (from_pred_op pr p) ->
    @all_evaluable A B ctx pr (NE.cons (p, a) b).
Proof.
  unfold all_evaluable; intros. inv H1. inv H3. inv H1. auto.
  eauto.
Qed.

Lemma all_evaluable_singleton :
  forall A B pr ctx b p,
    @all_evaluable A B ctx pr (NE.singleton (p, b)) ->
    p_evaluable ctx (from_pred_op pr p).
Proof.
  unfold all_evaluable; intros. eapply H. constructor.
Qed.

Lemma get_forest_p_evaluable :
  forall A (ctx: @ctx A) f r,
    forest_evaluable ctx f ->
    p_evaluable ctx (f #p r).
Proof.
  intros. unfold "#p", get_forest_p'.
  destruct_match. unfold forest_evaluable in *.
  unfold pred_forest_evaluable in *. eauto.
  unfold p_evaluable, evaluable. eexists.
  constructor. constructor.
Qed.

Lemma set_forest_p_evaluable :
  forall A (ctx: @ctx A) f r p,
    forest_evaluable ctx f ->
    p_evaluable ctx p ->
    forest_evaluable ctx (f #p r <- p).
Proof.
  unfold forest_evaluable, pred_forest_evaluable; intros.
  destruct (peq i r); subst.
  - rewrite forest_pred_gss2 in H1. now inv H1.
  - rewrite forest_pred_gso2 in H1 by auto; eauto.
Qed.

  Lemma evaluable_singleton :
    forall A B ctx fp r,
      @all_evaluable A B ctx fp (NE.singleton (T, r)).
  Proof.
    unfold all_evaluable, evaluable; intros.
    inv H. simpl. exists true. constructor.
  Qed.

Lemma evaluable_negate :
  forall G (ctx: @ctx G) p,
    p_evaluable ctx p ->
    p_evaluable ctx (¬ p).
Proof.
  unfold p_evaluable, evaluable in *; intros.
  inv H. eapply sem_pexpr_negate in H0. econstructor; eauto.
Qed.

Lemma predicated_evaluable :
  forall G (ctx: @ctx G) ps (p: pred_op),
    pred_forest_evaluable ctx ps ->
    p_evaluable ctx (from_pred_op ps p).
Proof.
  unfold pred_forest_evaluable; intros. induction p; intros; cbn.
  - repeat destruct_match; subst; unfold get_forest_p'.
    destruct_match. eapply H; eauto. econstructor. constructor. constructor.
    eapply evaluable_negate.
    destruct_match. eapply H; eauto. econstructor. constructor. constructor.
  - repeat econstructor.
  - repeat econstructor.
  - inv IHp1. inv IHp2. econstructor. apply sem_pexpr_Pand; eauto.
  - inv IHp1. inv IHp2. econstructor. apply sem_pexpr_Por; eauto.
Qed.

Lemma predicated_evaluable_all :
  forall A G (ctx: @ctx G) ps (p: predicated A),
    pred_forest_evaluable ctx ps ->
    all_evaluable ctx ps p.
Proof.
  unfold all_evaluable; intros.
  eapply predicated_evaluable. eauto.
Qed.

Lemma predicated_evaluable_all_list :
  forall A G (ctx: @ctx G) ps (p: list (predicated A)),
    pred_forest_evaluable ctx ps ->
    Forall (all_evaluable ctx ps) p.
Proof.
  induction p.
  - intros. constructor.
  - intros. constructor; eauto. apply predicated_evaluable_all; auto.
Qed.

#[local] Hint Resolve evaluable_singleton : core.
#[local] Hint Resolve predicated_evaluable : core.
#[local] Hint Resolve predicated_evaluable_all : core.
#[local] Hint Resolve predicated_evaluable_all_list : core.

Lemma evaluable_and_true :
  forall G (ctx: @ctx G) ps p,
    p_evaluable ctx (from_pred_op ps p) ->
    p_evaluable ctx (from_pred_op ps (p ∧ T)).
Proof.
  intros. unfold evaluable in *. inv H. exists (x && true). cbn.
  apply sem_pexpr_Pand; auto. constructor.
Qed.

Lemma all_evaluable_predicated_map :
  forall A B G (ctx: @ctx G) ps (f: A -> B) p,
    all_evaluable ctx ps p ->
    all_evaluable ctx ps (predicated_map f p).
Proof.
  induction p.
  - unfold all_evaluable; intros.
    exploit NEin_map; eauto; intros. inv H1. inv H2.
    eapply H; eauto.
  - intros. cbn.
    eapply all_evaluable_cons3. eapply IHp. eapply all_evaluable_cons; eauto.
    cbn. destruct a. cbn in *. eapply all_evaluable_cons2; eauto.
Qed.

Lemma all_evaluable_predicated_map2 :
  forall A B G (ctx: @ctx G) ps (f: A -> B) p,
    all_evaluable ctx ps (predicated_map f p) ->
    all_evaluable ctx ps p.
Proof.
  induction p.
  - unfold all_evaluable in *; intros.
    eapply H. eapply NEin_map2; eauto.
  - intros. cbn. destruct a.
    cbn in H. pose proof H. eapply all_evaluable_cons in H; eauto.
    eapply all_evaluable_cons2 in H0; eauto.
    unfold all_evaluable. specialize (IHp H).
    unfold all_evaluable in IHp.
    intros. inv H1. inv H3. inv H1; eauto.
    specialize (IHp _ _ H1). eauto.
Qed.

Lemma all_evaluable_map_and :
  forall A B G (ctx: @ctx G) ps (a: NE.non_empty ((pred_op * A) * (pred_op * B))),
    (forall p1 x p2 y,
       NE.In ((p1, x), (p2, y)) a ->
            p_evaluable ctx (from_pred_op ps p1)
            /\ p_evaluable ctx (from_pred_op ps p2)) ->
    all_evaluable ctx ps (NE.map (fun x => match x with ((a, b), (c, d)) => (Pand a c, (b, d)) end) a).
Proof.
  induction a.
  - intros. cbn. repeat destruct_match. inv Heqp.
    unfold all_evaluable; intros. inv H0.
    unfold evaluable.
    exploit H. constructor.
    intros [Ha Hb]. inv Ha. inv Hb.
    exists (x && x0). apply sem_pexpr_Pand; auto.
  - intros. unfold all_evaluable; cbn; intros. inv H0. inv H2.
    + repeat destruct_match. inv Heqp0. inv H0.
      specialize (H p2 a1 p3 b ltac:(constructor; eauto)).
      inv H. inv H0. inv H1. exists (x && x0).
      apply sem_pexpr_Pand; eauto.
    + eapply IHa; intros. eapply H. econstructor. right. eauto.
      eauto.
Qed.

Lemma all_evaluable_map_add :
  forall A B G (ctx: @ctx G) ps (a: pred_op * A) (b: predicated B) p1 x p2 y,
    p_evaluable ctx (from_pred_op ps (fst a)) ->
    all_evaluable ctx ps b ->
    NE.In (p1, x, (p2, y)) (NE.map (fun x : pred_op * B => (a, x)) b) ->
    p_evaluable ctx (from_pred_op ps p1) /\ p_evaluable ctx (from_pred_op ps p2).
Proof.
  induction b; intros.
  - cbn in *. inv H1. unfold all_evaluable in *. specialize (H0 _ _ ltac:(constructor)).
    auto.
  - cbn in *. inv H1. inv H3.
    + inv H1. unfold all_evaluable in H0. specialize (H0 _ _ ltac:(constructor; eauto)); auto.
    + eapply all_evaluable_cons in H0. specialize (IHb _ _ _ _ H H0 H1). auto.
Qed.

Lemma all_evaluable_non_empty_prod :
  forall A B G (ctx: @ctx G) ps p1 x p2 y (a: predicated A) (b: predicated B),
    all_evaluable ctx ps a ->
    all_evaluable ctx ps b ->
    NE.In ((p1, x), (p2, y)) (NE.non_empty_prod a b) ->
    p_evaluable ctx (from_pred_op ps p1)
    /\ p_evaluable ctx (from_pred_op ps p2).
Proof.
  induction a; intros.
  - cbn in *. eapply all_evaluable_map_add; eauto. destruct a; cbn in *. eapply H; constructor.
  - cbn in *. eapply NE.in_NEapp5 in H1. inv H1. eapply all_evaluable_map_add; eauto.
    destruct a; cbn in *. eapply all_evaluable_cons2; eauto.
    eapply all_evaluable_cons in H. eauto.
Qed.

Lemma merge_all_evaluable :
  forall G (ctx: @ctx G) ps,
    pred_forest_evaluable ctx ps ->
    forall f args,
      all_evaluable ctx ps (merge (list_translation args f)).
Proof.
  intros. eapply predicated_evaluable_all. eauto.
Qed.

  Lemma forest_evaluable_regset :
    forall A f (ctx: @ctx A) n x,
      forest_evaluable ctx f ->
      forest_evaluable ctx f #r x <- n.
  Proof.
    unfold forest_evaluable, pred_forest_evaluable; intros.
    eapply H. eauto.
  Qed.

Lemma evaluable_impl :
  forall A (ctx: @ctx A) a b,
    p_evaluable ctx a ->
    p_evaluable ctx b ->
    p_evaluable ctx (a → b).
Proof.
  unfold evaluable.
  inversion_clear 1 as [b1 SEM1].
  inversion_clear 1 as [b2 SEM2].
  unfold Pimplies.
  econstructor. apply sem_pexpr_Por;
  eauto using sem_pexpr_negate.
Qed.

Lemma parts_evaluable :
  forall A (ctx: @ctx A) b p0,
    evaluable sem_pred ctx p0 ->
    evaluable sem_pexpr ctx (Plit (b, p0)).
Proof.
  intros. unfold evaluable in *. inv H.
  destruct b. do 2 econstructor. eauto.
  exists (negb x). constructor. rewrite negb_involutive. auto.
Qed.

Lemma p_evaluable_Pand :
  forall A (ctx: @ctx A) a b,
    p_evaluable ctx a ->
    p_evaluable ctx b ->
    p_evaluable ctx (a ∧ b).
Proof.
  intros. inv H. inv H0.
  econstructor. apply sem_pexpr_Pand; eauto.
Qed.

Lemma from_predicated_evaluable :
  forall A (ctx: @ctx A) f b a,
    pred_forest_evaluable ctx f ->
    all_evaluable2 ctx sem_pred a ->
    p_evaluable ctx (from_predicated b f a).
Proof.
  induction a.
  cbn. destruct_match; intros.
  eapply evaluable_impl.
  eauto using predicated_evaluable.
  unfold all_evaluable2 in H0. unfold p_evaluable.
  eapply parts_evaluable. eapply H0. econstructor.

  intros. cbn. destruct_match.
  eapply p_evaluable_Pand.
  eapply all_evaluable2_cons2 in H0.
  eapply evaluable_impl.
  eauto using predicated_evaluable.
  unfold all_evaluable2 in H0. unfold p_evaluable.
  eapply parts_evaluable. eapply H0.
  eapply all_evaluable2_cons in H0. eauto.
Qed.

Lemma p_evaluable_imp :
  forall A (ctx: @ctx A) a b,
    sem_pexpr ctx a false ->
    p_evaluable ctx (a → b).
Proof.
  intros. unfold "→".
  unfold p_evaluable, evaluable. exists true.
  constructor. replace true with (negb false) by trivial. left.
  now apply sem_pexpr_negate.
Qed.
