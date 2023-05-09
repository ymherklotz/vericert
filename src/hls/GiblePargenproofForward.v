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

Lemma match_states_list :
  forall A (rs: Regmap.t A) rs',
  (forall r, rs !! r = rs' !! r) ->
  forall l, rs ## l = rs' ## l.
Proof. induction l; crush. Qed.

Lemma PTree_matches :
  forall A (v: A) res rs rs',
  (forall r, rs !! r = rs' !! r) ->
  forall x, (Regmap.set res v rs) !! x = (Regmap.set res v rs') !! x.
Proof.
  intros; destruct (Pos.eq_dec x res); subst;
  [ repeat rewrite Regmap.gss by auto
  | repeat rewrite Regmap.gso by auto ]; auto.
Qed.

Section CORRECTNESS.

  Context (prog: GibleSeq.program) (tprog : GiblePar.program).

  Let ge : GibleSeq.genv := Globalenvs.Genv.globalenv prog.
  Let tge : GiblePar.genv := Globalenvs.Genv.globalenv tprog.

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
    forall A B C sem f_p ctx a b v,
      sem_pred_expr f_p sem ctx a v ->
      @sem_pred_expr A B C f_p sem ctx (NE.app a b) v.
  Proof.
    induction a; crush.
    - inv H. constructor; auto.
    - inv H. constructor; eauto.
      eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma sem_pred_expr_NEapp2 :
    forall A B C sem f_p ctx a b v ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
      (forall x, NE.In x a -> eval_predf ps (fst x) = false) ->
      sem_pred_expr f_p sem ctx b v ->
      @sem_pred_expr A B C f_p sem ctx (NE.app a b) v.
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
    forall A B C sem f_p ctx (a b: predicated B) v,
      (forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false) ->
      sem_pred_expr f_p sem ctx b v ->
      @sem_pred_expr A B C f_p sem ctx (NE.app a b) v.
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
    forall A B C sem ctx f_p ps x v p,
      (forall x : positive, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      eval_predf ps p = true ->
      sem_pred_expr f_p sem ctx x v ->
      @sem_pred_expr A B C f_p sem ctx
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
    forall A B C sem ctx f_p y x v p ps,
      sem_pred_expr f_p sem ctx x v ->
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
      eval_predf ps p = true ->
      @sem_pred_expr A B C f_p sem ctx (app_predicated p y x) v.
  Proof.
    intros * SEM PS EVAL. unfold app_predicated.
    eapply sem_pred_expr_NEapp2; eauto.
    intros. eapply sem_pred_expr_map_not; eauto.
    rewrite eval_predf_negate. rewrite EVAL. auto.
    eapply sem_pred_expr_map_Pand; eauto.
  Qed.

  Lemma sem_pred_expr_app_predicated_false :
    forall A B C sem ctx f_p y x v p ps,
      sem_pred_expr f_p sem ctx y v ->
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
      eval_predf ps p = false ->
      @sem_pred_expr A B C f_p sem ctx (app_predicated p y x) v.
  Admitted.

  Lemma sem_pred_expr_prune_predicated :
    forall A B C sem ctx f_p y x v,
      sem_pred_expr f_p sem ctx x v ->
      prune_predicated x = Some y ->
      @sem_pred_expr A B C f_p sem ctx y v.
  Proof.
    intros * SEM PRUNE. unfold prune_predicated in *.
    Admitted.

  Inductive sem_ident {B A: Type} (c: @ctx B) (a: A): A -> Prop :=
  | sem_ident_intro : sem_ident c a a.

  Lemma sem_pred_expr_pred_ret :
    forall G A (ctx: @Abstr.ctx G) (i: A) ps,
      sem_pred_expr ps sem_ident ctx (pred_ret i) i.
  Proof. intros; constructor; constructor. Qed.

  Lemma sem_pred_expr_ident :
    forall G A B ps (ctx: @Abstr.ctx G) (l: predicated A) (s: @Abstr.ctx G -> A -> B -> Prop) l_,
      sem_pred_expr ps sem_ident ctx l l_ ->
      forall (v: B),
        s ctx l_ v ->
        sem_pred_expr ps s ctx l v.
  Proof.
    induction 1.
    - intros. constructor; auto. inv H0. auto.
    - intros. apply sem_pred_expr_cons_false; auto.
    - intros. inv H0. constructor; auto.
  Qed.

  Lemma sem_pred_expr_ident2 :
    forall G A B ps (ctx: @Abstr.ctx G) (l: predicated A) (s: @Abstr.ctx G -> A -> B -> Prop) (v: B),
        sem_pred_expr ps s ctx l v ->
        exists l_, sem_pred_expr ps sem_ident ctx l l_ /\ s ctx l_ v.
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
    forall G (ctx: @Abstr.ctx G) l j,
      sem_val_list ctx (to_elist l) j ->
      Forall2 (sem_value ctx) l j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_val_list_elist2 :
    forall G (ctx: @Abstr.ctx G) l j,
      Forall2 (sem_value ctx) l j ->
      sem_val_list ctx (to_elist l) j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_val_list_elist3 :
    forall G (ctx: @Abstr.ctx G) l j,
      sem_val_list ctx l j ->
      Forall2 (sem_value ctx) (of_elist l) j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_val_list_elist4 :
    forall G (ctx: @Abstr.ctx G) l j,
      Forall2 (sem_value ctx) (of_elist l) j ->
      sem_val_list ctx l j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_pred_expr_predicated_map :
    forall A B C pr (f: C -> B) ctx (pred: predicated C) (pred': C),
      sem_pred_expr pr sem_ident ctx pred pred' ->
      @sem_pred_expr A _ _ pr sem_ident ctx (predicated_map f pred) (f pred').
  Proof.
    induction pred; unfold predicated_map; intros.
    - inv H. inv H3. constructor; eauto. constructor.
    - inv H. inv H5. constructor; eauto. constructor.
      eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma NEapp_NEmap :
    forall A B (f: A -> B) a b,
      NE.map f (NE.app a b) = NE.app (NE.map f a) (NE.map f b).
  Proof. induction a; crush. Qed.

  Lemma sem_pred_expr_predicated_prod :
    forall A B C pr ctx (a: predicated C) (b: predicated B) a' b',
      sem_pred_expr pr sem_ident ctx a a' ->
      sem_pred_expr pr sem_ident ctx b b' ->
      @sem_pred_expr A _ _ pr sem_ident ctx (predicated_prod a b) (a', b').
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
      rewrite NEapp_NEmap.
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

  Lemma sem_pred_expr_seq_app :
    forall G A B (f: predicated (A -> B))
        ps (ctx: @ctx G) l f_ l_,
      sem_pred_expr ps sem_ident ctx l l_ ->
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (seq_app f l) (f_ l_).
  Proof.
    unfold seq_app; intros.
    remember (fun x : (A -> B) * A => fst x (snd x)) as app.
    replace (f_ l_) with (app (f_, l_)) by (rewrite Heqapp; auto).
    eapply sem_pred_expr_predicated_map. eapply sem_pred_expr_predicated_prod; auto.
  Qed.

  Lemma sem_pred_expr_map :
    forall A B C (ctx: @ctx A) ps (f: B -> C) y v,
      sem_pred_expr ps sem_ident ctx y v ->
      sem_pred_expr ps sem_ident ctx (NE.map (fun x => (fst x, f (snd x))) y) (f v).
  Proof.
    induction y; crush. inv H. constructor; crush. inv H3. constructor.
    inv H. inv H5. constructor; eauto. constructor.
    eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma sem_pred_expr_flap :
    forall G A B C (f: predicated (A -> B -> C))
        ps (ctx: @ctx G) l f_,
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (flap f l) (f_ l).
  Proof.
    induction f. unfold flap2; intros. inv H. inv H3.
    constructor; eauto. constructor.
    intros. inv H. cbn.
    constructor; eauto. inv H5. constructor.
    eapply sem_pred_expr_cons_false; eauto.
   Qed.

  Lemma sem_pred_expr_flap2 :
    forall G A B C (f: predicated (A -> B -> C))
        ps (ctx: @ctx G) l1 l2 f_,
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (flap2 f l1 l2) (f_ l1 l2).
  Proof.
    induction f. unfold flap2; intros. inv H. inv H3.
    constructor; eauto. constructor.
    intros. inv H. cbn.
    constructor; eauto. inv H5. constructor.
    eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma sem_pred_expr_seq_app_val :
    forall G A B V (s: @Abstr.ctx G -> B -> V -> Prop)
        (f: predicated (A -> B))
        ps ctx l v f_ l_,
      sem_pred_expr ps sem_ident ctx l l_ ->
      sem_pred_expr ps sem_ident ctx f f_ ->
      s ctx (f_ l_) v ->
      sem_pred_expr ps s ctx (seq_app f l) v.
  Proof.
    intros. eapply sem_pred_expr_ident; [|eassumption].
    eapply sem_pred_expr_seq_app; eauto.
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
    forall A (ctx: @ctx A) pr s s' a e,
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
    forall A pr ctx s a a' s',
      sem_pred_expr pr sem_ident ctx s s' ->
      Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a') ->
      @sem_pred_expr A _ _ pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s').
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

  Lemma NEof_list_some :
    forall A a a' (e: A),
      NE.of_list a = Some a' ->
      NE.of_list (e :: a) = Some (NE.cons e a').
  Proof.
    induction a; [crush|].
    intros.
    cbn in H. destruct a0. inv H. auto.
    destruct_match; [|discriminate].
    inv H. specialize (IHa n a ltac:(trivial)).
    cbn. destruct_match. unfold NE.of_list in IHa.
    fold (@NE.of_list A) in IHa. rewrite IHa in Heqo0. inv Heqo0. auto.
    unfold NE.of_list in IHa. fold (@NE.of_list A) in IHa. rewrite IHa in Heqo0. inv Heqo0.
  Qed.

  Lemma NEof_list_contra :
    forall A b (a: A),
      ~ NE.of_list (a :: b) = None.
  Proof.
    induction b; try solve [crush].
    intros.
    specialize (IHb a).
    enough (X: exists x, NE.of_list (a :: b) = Some x).
    inversion_clear X as [x X'].
    erewrite NEof_list_some; eauto; discriminate.
    destruct (NE.of_list (a :: b)) eqn:?; [eauto|contradiction].
  Qed.

  Lemma NEof_list_exists :
    forall A b (a: A),
      exists x, NE.of_list (a :: b) = Some x.
  Proof.
    intros. pose proof (NEof_list_contra _ b a).
    destruct (NE.of_list (a :: b)); try contradiction.
    eauto.
  Qed.

  Lemma NEof_list_exists2 :
    forall A b (a c: A),
      exists x,
        NE.of_list (c :: a :: b) = Some (NE.cons c x)
        /\ NE.of_list (a :: b) = Some x.
  Proof.
    intros. pose proof (NEof_list_exists _ b a).
    inversion_clear H as [x B].
    econstructor; split; eauto.
    eapply NEof_list_some; eauto.
  Qed.

  Lemma NEof_list_to_list :
    forall A (x: list A) y,
      NE.of_list x = Some y ->
      NE.to_list y = x.
  Proof.
    induction x; [crush|].
    intros. destruct x; [crush|].
    pose proof (NEof_list_exists2 _ x a0 a).
    inversion_clear H0 as [x0 [HN1 HN2]]. rewrite HN1 in H. inv H.
    cbn. f_equal. eauto.
  Qed.

  Lemma sem_pred_expr_merge :
    forall G (ctx: @Abstr.ctx G) ps l args,
      Forall2 (sem_pred_expr ps sem_ident ctx) args l ->
      sem_pred_expr ps sem_ident ctx (merge args) (to_elist l).
  Proof.
    induction l; intros.
    - inv H. cbn; repeat constructor.
    - inv H. cbn. unfold merge. Admitted.

  Lemma sem_pred_expr_merge2 :
    forall A (ctx: @ctx A) pr l l',
      sem_pred_expr pr sem_ident ctx (merge l) l' ->
      Forall2 (sem_pred_expr pr sem_ident ctx) l (of_elist l').
  Proof.
    induction l; crush.
    - unfold merge in *; cbn in *.
      inv H. inv H5. constructor.
    - unfold merge in H.
      pose proof (NEof_list_exists _ l a) as Y.
      inversion_clear Y as [x HNE]. rewrite HNE in H.
      erewrite <- (NEof_list_to_list _ (a :: l)) by eassumption.
      apply sem_pred_expr_fold_right2 with (s := (NE.singleton (T, Enil))) (s' := Enil).
      repeat constructor.
      rewrite Eapp_right_nil. auto.
  Qed.

  Lemma sem_merge_list :
    forall A ctx f rs ps m args,
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_val_list ctx
        (merge (list_translation args f)) (rs ## args).
  Proof.
    induction args; crush. cbn. constructor; constructor.
    unfold merge. specialize (IHargs H).
    eapply sem_pred_expr_ident2 in IHargs.
    inversion_clear IHargs as [l_ [HSEM HVAL]].
    destruct_match; [|exfalso; eapply NEof_list_contra; eauto].
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
    - pose proof (NEof_list_exists2 _ (list_translation args f) (f #r (Reg r)) (f #r (Reg a))) as Y.
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
      erewrite NEof_list_to_list; eauto.
      eapply sem_pred_expr_merge2; auto.
  Qed.

  Lemma sem_pred_expr_list_translation :
    forall G ctx args f i,
      @sem G ctx f (i, None) ->
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

  Lemma storev_valid_pointer1 :
    forall chunk m m' s d b z,
      Mem.storev chunk m s d = Some m' ->
      Mem.valid_pointer m b z = true ->
      Mem.valid_pointer m' b z = true.
  Proof using.
    intros. unfold Mem.storev in *. destruct_match; try discriminate; subst.
    apply Mem.valid_pointer_nonempty_perm. apply Mem.valid_pointer_nonempty_perm in H0.
    eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma storev_valid_pointer2 :
    forall chunk m m' s d b z,
      Mem.storev chunk m s d = Some m' ->
      Mem.valid_pointer m' b z = true ->
      Mem.valid_pointer m b z = true.
  Proof using.
    intros. unfold Mem.storev in *. destruct_match; try discriminate; subst.
    apply Mem.valid_pointer_nonempty_perm. apply Mem.valid_pointer_nonempty_perm in H0.
    eapply Mem.perm_store_2; eauto.
  Qed.

  Definition valid_mem m m' :=
    forall b z, Mem.valid_pointer m b z = Mem.valid_pointer m' b z.

  #[global] Program Instance valid_mem_Equivalence : Equivalence valid_mem.
  Next Obligation. unfold valid_mem; auto. Qed. (* Reflexivity *)
  Next Obligation. unfold valid_mem; auto. Qed. (* Symmetry *)
  Next Obligation. unfold valid_mem; eauto. Qed. (* Transitity *)

  Lemma storev_valid_pointer :
    forall chunk m m' s d,
      Mem.storev chunk m s d = Some m' ->
      valid_mem m m'.
  Proof using.
    unfold valid_mem. symmetry.
    intros. destruct (Mem.valid_pointer m b z) eqn:?;
                     eauto using storev_valid_pointer1.
    apply not_true_iff_false.
    apply not_true_iff_false in Heqb0.
    eauto using storev_valid_pointer2.
  Qed.

  Lemma storev_cmpu_bool :
    forall m m' c v v0,
      valid_mem m m' ->
      Val.cmpu_bool (Mem.valid_pointer m) c v v0 = Val.cmpu_bool (Mem.valid_pointer m') c v v0.
  Proof using.
    unfold valid_mem.
    intros. destruct v, v0; crush.
    { destruct_match; crush.
      destruct_match; crush.
      destruct_match; crush.
      apply orb_true_iff in H1.
      inv H1. rewrite H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush.
      destruct_match; auto. simplify.
      apply orb_true_iff in H1.
      inv H1. rewrite <- H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite <- H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush. }

    { destruct_match; crush.
      destruct_match; crush.
      destruct_match; crush.
      apply orb_true_iff in H1.
      inv H1. rewrite H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush.
      destruct_match; auto. simplify.
      apply orb_true_iff in H1.
      inv H1. rewrite <- H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite <- H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush. }

    { destruct_match; auto. destruct_match; auto; crush.
      { destruct_match; crush.
        { destruct_match; crush.
          setoid_rewrite H in H0; eauto.
          setoid_rewrite H in H1; eauto.
          rewrite H0 in Heqb. rewrite H1 in Heqb; crush.
        }
        { destruct_match; crush.
          setoid_rewrite H in Heqb0; eauto.
          rewrite H0 in Heqb0. rewrite H1 in Heqb0; crush. } }
      { destruct_match; crush.
        { destruct_match; crush.
          setoid_rewrite H in H0; eauto.
          setoid_rewrite H in H1; eauto.
          rewrite H0 in Heqb0. rewrite H1 in Heqb0; crush.
        }
        { destruct_match; crush.
          setoid_rewrite H in Heqb0; eauto.
          rewrite H0 in Heqb0. rewrite H1 in Heqb0; crush. } } }
  Qed.

  Lemma storev_eval_condition :
    forall m m' c rs,
      valid_mem m m' ->
      Op.eval_condition c rs m = Op.eval_condition c rs m'.
  Proof using.
    intros. destruct c; crush.
    destruct rs; crush.
    destruct rs; crush.
    destruct rs; crush.
    eapply storev_cmpu_bool; eauto.
    destruct rs; crush.
    destruct rs; crush.
    eapply storev_cmpu_bool; eauto.
  Qed.

  Lemma eval_operation_valid_pointer :
    forall A B (ge: Genv.t A B) sp op args m m' v,
      valid_mem m m' ->
      Op.eval_operation ge sp op args m' = Some v ->
      Op.eval_operation ge sp op args m = Some v.
  Proof.
    intros * VALID OP. destruct op; auto.
    - destruct cond; auto; cbn in *.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
    - destruct c; auto; cbn in *.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
  Qed.

  Lemma bb_memory_consistency_eval_operation :
    forall A B (ge: Genv.t A B) sp state i state' args op v,
      step_instr ge sp (Iexec state) i (Iexec state') ->
      Op.eval_operation ge sp op args (is_mem state) = Some v ->
      Op.eval_operation ge sp op args (is_mem state') = Some v.
  Proof.
    inversion_clear 1; intro EVAL; auto.
    cbn in *.
    eapply eval_operation_valid_pointer. unfold valid_mem. symmetry.
    eapply storev_valid_pointer; eauto.
    auto.
  Qed.

  Lemma truthy_dflt :
    forall ps p,
      truthy ps p -> eval_predf ps (dfltp p) = true.
  Proof. intros. destruct p; cbn; inv H; auto. Qed.

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
          eapply sem_pred_expr_prune_predicated; eauto.
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
          eapply sem_pred_expr_prune_predicated; eauto.
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

  Lemma exists_sem_pred :
    forall A B C (ctx: @ctx A) s pr r v,
      @sem_pred_expr A B C pr s ctx r v ->
      exists r',
        NE.In r' r /\ s ctx (snd r') v.
  Proof.
    induction r; crush.
    - inv H. econstructor. split. constructor. auto.
    - inv H.
      + econstructor. split. constructor. left; auto. auto.
      + exploit IHr; eauto. intros HH. inversion_clear HH as [x HH']. inv HH'.
        econstructor. split. constructor. right. eauto. auto.
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
      eapply sem_pred_expr_prune_predicated; eauto.
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

  Definition predicated_not_inP {A} (p: Gible.predicate) (l: predicated A) :=
    forall op e, NE.In (op, e) l -> ~ PredIn p op.

  Lemma predicated_not_inP_cons :
    forall A p (a: (pred_op * A)) l,
      predicated_not_inP p (NE.cons a l) ->
      predicated_not_inP p l.
  Proof.
    unfold predicated_not_inP; intros. eapply H. econstructor. right; eauto.
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

  Lemma pred_not_in_forestP :
    forall pred f,
      predicated_not_in_forest pred f = true ->
      forall x, predicated_not_inP pred (f #r x).
  Proof. Admitted.

  Lemma pred_not_in_forest_exitP :
    forall pred f,
      predicated_not_in_forest pred f = true ->
      predicated_not_inP pred (forest_exit f).
  Proof. Admitted.

  Lemma from_predicated_sem_pred_expr :
    forall A (ctx: @ctx A) preds pe b,
      sem_pred_expr preds sem_pred ctx pe b ->
      sem_pexpr ctx (from_predicated true preds pe) b.
  Proof. Admitted.

  Lemma sem_update_Isetpred:
    forall A (ctx: @ctx A) f pr p0 c args b rs m,
      valid_mem (ctx_mem ctx) m ->
      sem ctx f (mk_instr_state rs pr m, None) ->
      Op.eval_condition c rs ## args m = Some b ->
      truthy pr p0 ->
      sem_pexpr ctx
      (from_predicated true (forest_preds f) (seq_app (pred_ret (PEsetpred c)) (merge (list_translation args f)))) b.
  Proof.
    intros. eapply from_predicated_sem_pred_expr.
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
    inversion UPD as [PRUNE]. unfold Option.bind in PRUNE. destr. destr.
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
        cbn [update] in *. unfold Option.bind in *. destr. destr. inv UPD.
        replace b with (b && true) by eauto with bool.
        apply sem_pexpr_Pand.
        destruct b. constructor. right.
        eapply sem_update_Isetpred; eauto.
        constructor. constructor. replace false with (negb true) by auto.
        apply sem_pexpr_negate. inv TRUTHY. constructor.
        cbn. eapply sem_pexpr_eval. inv PRED. eauto. auto.
        replace false with (negb true) by auto.
        apply sem_pexpr_negate.
        eapply sem_pexpr_eval. inv PRED. eauto. auto.
        eapply sem_update_Isetpred; eauto.
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
        eapply sem_pred_expr_prune_predicated; eauto.
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
        eapply sem_pred_expr_prune_predicated; eauto.
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
      * rewrite forest_reg_gss. cbn. eapply sem_pred_expr_prune_predicated; eauto.
        eapply sem_pred_expr_app_predicated_false. inv H3. auto. inv H3. inv H9. eauto.
        rewrite eval_predf_Pand. cbn -[eval_predf]. rewrite H0. auto.
      * inv H3. auto.
    - unfold Option.bind in *. destr. destr. inv H2.
      constructor.
      * constructor; intros. rewrite forest_pred_reg. apply sem_pred_not_in.
        inv H3. inv H8. auto. apply pred_not_in_forestP. unfold assert_ in Heqo. now destr.
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
        apply pred_not_in_forestP. unfold assert_ in Heqo. now destr.
      * apply sem_pred_not_in. inv H3; auto. cbn.
        apply pred_not_in_forest_exitP. unfold assert_ in Heqo. now destr.
    - unfold Option.bind in *. destr. inv H2. inv H3. constructor.
      * constructor. inv H8. auto.
      * constructor. intros. inv H9. eauto.
      * auto.
      * cbn. eapply sem_pred_expr_prune_predicated; [|eauto].
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
        eapply sem_pred_expr_prune_predicated; eauto.
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
        eapply sem_pred_expr_prune_predicated; eauto.
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
      * rewrite forest_reg_gss. cbn. eapply sem_pred_expr_prune_predicated; eauto.
        eapply sem_pred_expr_app_predicated_false. inv H1. auto. inv H1. inv H8. eauto.
        rewrite eval_predf_Pand. cbn -[eval_predf]. rewrite H. eauto with bool.
      * inv H1. auto.
    - unfold Option.bind in *. destr. destr. inv H0. split; [|solve [auto]].
      constructor.
      * constructor; intros. rewrite forest_pred_reg. apply sem_pred_not_in.
        inv H1. inv H7. auto. apply pred_not_in_forestP. unfold assert_ in Heqo0. now destr.
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
        apply pred_not_in_forestP. unfold assert_ in Heqo0. now destr.
      * apply sem_pred_not_in. inv H1; auto. cbn.
        apply pred_not_in_forest_exitP. unfold assert_ in Heqo0. now destr.
    - unfold Option.bind in *. destr. inv H0. inv H1. split.
      -- constructor.
         * constructor. inv H7. auto.
         * constructor. intros. inv H8. eauto.
         * auto.
         * cbn. eapply sem_pred_expr_prune_predicated; [|eauto].
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
    eapply sem_pred_expr_prune_predicated; eauto.
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
  Proof. Admitted. (* This needs a bit more in Abstr.v *)

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
    - unfold Option.bind in *. destr. destr. inv UPD. inv STEP; auto. cbn [is_ps] in *.
      unfold is_initial_pred_and_notin in Heqo1. unfold assert_ in Heqo1. destr. destr.
      destr. destr. destr. destr. subst. assert (~ PredIn p2 next_p).
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
