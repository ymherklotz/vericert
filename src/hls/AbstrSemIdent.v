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
Admitted.

Lemma sem_pred_expr_prune_predicated :
  forall f_p y x v,
    sem_pred_expr f_p a_sem ctx x v ->
    prune_predicated x = Some y ->
    sem_pred_expr f_p a_sem ctx y v.
Proof.
  intros * SEM PRUNE. unfold prune_predicated in *.
Admitted.

Lemma sem_pred_expr_prune_predicated2 :
  forall f_p y x v,
    sem_pred_expr f_p a_sem ctx y v ->
    prune_predicated x = Some y ->
    sem_pred_expr f_p a_sem ctx x v.
Proof.
  intros * SEM PRUNE. unfold prune_predicated in *.
  Admitted.

Lemma sem_pred_expr_app_predicated_false2 :
  forall f_p y x v p ps,
    sem_pred_expr f_p a_sem ctx (app_predicated p y x) v ->
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
    eval_predf ps p = false ->
    sem_pred_expr f_p a_sem ctx y v.
Admitted.

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

Lemma sem_pred_expr_NEapp3 :
  forall f_p ctx a b v,
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
  forall f_p ctx a b v,
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
  forall f_p ctx a b v,
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
Proof. Admitted.

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
  - destruct x in *; cbn in *.
    rewrite NE.app_NEmap in H0.
    generalize dependent b; induction b; intros.
    + cbn in *; repeat destr. inv Heqp0. inv H0.
      * inv H6. inv H7. solve [repeat constructor; auto].
      * inv H6. inv H1.
        -- exploit IHa; eauto; intros. inv H1. split; auto.
           apply sem_pred_expr_cons_false; eauto.
        -- exploit IHa; eauto; intros. inv H1. inv H3.
           eapply sem_pexpr_det in H0; try eassumption. discriminate.
           apply similar_refl.
    + Admitted.

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
Proof. Admitted.

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

Lemma sem_pred_expr_fold_right2 :
  forall A pr ctx s a a' s',
    sem_pred_expr pr sem_ident ctx s s' ->
    @sem_pred_expr A _ _ pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s') ->
    Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a').
Proof.
  induction a. Admitted.

Lemma sem_pred_expr_merge :
  forall G (ctx: @Abstr.ctx G) ps l args,
    Forall2 (sem_pred_expr ps sem_ident ctx) args l ->
    sem_pred_expr ps sem_ident ctx (merge args) (to_elist l).
Proof.
  induction l; intros.
  - inv H. cbn; repeat constructor.
  - inv H. cbn. unfold merge. Admitted.

Lemma sem_pred_expr_merge2 :
  forall pr l l',
    sem_pred_expr pr sem_ident ctx (merge l) l' ->
    Forall2 (sem_pred_expr pr sem_ident ctx) l (of_elist l').
Proof.
  induction l; crush.
  - unfold merge in *; cbn in *.
    inv H. inv H5. constructor.
  - unfold merge in H.
    pose proof (NE.of_list_exists _ l a) as Y.
    inversion_clear Y as [x HNE]. rewrite HNE in H.
    erewrite <- (NE.of_list_to_list _ (a :: l)) by eassumption.
    apply sem_pred_expr_fold_right2 with (s := (NE.singleton (T, Enil))) (s' := Enil).
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
  induction args; crush. cbn. constructor; constructor.
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

Lemma from_predicated_sem_pred_expr :
  forall preds pe b,
    sem_pred_expr preds sem_pred ctx pe b ->
    sem_pexpr ctx (from_predicated true preds pe) b.
Proof. Admitted.

Lemma from_predicated_sem_pred_expr2 :
  forall preds pe b,
    sem_pexpr ctx (from_predicated true preds pe) b ->
    sem_pred_expr preds sem_pred ctx pe b.
Proof. Admitted.

End PROOF.
