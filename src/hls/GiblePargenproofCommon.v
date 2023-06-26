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
Require Import vericert.hls.AbstrSemIdent.
Require Import vericert.common.Monad.

Module Import OptionExtra := MonadExtra(Option).

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

#[local] Opaque simplify.
#[local] Opaque deep_simplify.

#[local] Ltac destr := destruct_match; try discriminate; [].

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

Definition predicated_not_inP {A} (p: Gible.predicate) (l: predicated A) :=
  forall op e, NE.In (op, e) l -> ~ PredIn p op.

Lemma predicated_not_inP_cons :
  forall A p (a: (pred_op * A)) l,
    predicated_not_inP p (NE.cons a l) ->
    predicated_not_inP p l.
Proof.
  unfold predicated_not_inP; intros. eapply H. econstructor. right; eauto.
Qed.

Lemma predicated_not_inP_equiv :
  forall A (a: predicated A) p,
    predicated_not_in p a = true -> predicated_not_inP p a.
Proof.
  induction a.
  - intros. cbn in *. unfold predicated_not_inP; intros.
    unfold not; intros. inv H0. cbn in *.
    destruct (predin peq p op) eqn:?; try discriminate. eapply predin_PredIn in H1.
    rewrite H1 in Heqb. discriminate.
  - intros. cbn in H. eapply andb_prop in H. inv H. eapply IHa in H0.
    unfold predicated_not_inP in *; intros. inv H. inv H3; cbn in *; eauto.
    unfold not; intros. eapply predin_PredIn in H. now rewrite H in H1.
Qed.    

Lemma truthy_dec:
  forall ps a, truthy ps a \/ falsy ps a.
Proof.
  destruct a; try case_eq (eval_predf ps p); intuition (constructor; auto).
Qed.

Definition all_mutexcl (f: forest) : Prop :=
  forall x, predicated_mutexcl (f #r x).

(* Lemma map_mutexcl' : *)
(*   forall A B (x: predicated A) (f: (pred_op * A) -> (pred_op * B)), *)
(*     predicated_mutexcl x -> *)
(*     (forall a pop, fst (f (pop, a)) ⇒ pop) -> *)
(*     (forall a b, f a = f b -> a = b) -> *)
(*     predicated_mutexcl (NE.map f x). *)
(* Proof. *)
(*   induction x; cbn; intros. *)
(*   - cbn. repeat constructor; intros. inv H2. inv H3. contradiction. *)
(*   - constructor. intros. *)
(*     assert (exists x0', x0 = f x0') by admit. *)
(*     assert (exists y', y = f y') by admit. *)
(*     simplify. unfold "⇒" in *; intros. *)
(*     destruct x2, x1. *)
(*     eapply H0 in H5. *)
(*     inv H. *)
(*     specialize (H6 (p, a0) (p0, a1)). *)
(*     assert ((fst (p, a0)) ⇒ ¬ (fst (p0, a1))) by admit. *)
(*     unfold "⇒" in H; simplify. *)
(*     apply H in H5. *)

Lemma map_deep_simplify :
  forall A x (eqd: forall a b: pred_op * A, {a = b} + {a <> b}),
    predicated_mutexcl x ->
    predicated_mutexcl
      (GiblePargenproofEquiv.NE.map (fun x : Predicate.pred_op * A => (deep_simplify peq (fst x), snd x)) x).
Proof.
  intros. inv H.
  assert (forall x0 y : pred_op * A,
  GiblePargenproofEquiv.NE.In x0
    (GiblePargenproofEquiv.NE.map (fun x1 : Predicate.pred_op * A => (deep_simplify peq (fst x1), snd x1)) x) ->
  GiblePargenproofEquiv.NE.In y
    (GiblePargenproofEquiv.NE.map (fun x1 : Predicate.pred_op * A => (deep_simplify peq (fst x1), snd x1)) x) ->
  x0 <> y -> fst x0 ⇒ ¬ fst y).
  { intros. exploit NE.In_map2. eapply H. simplify.
    exploit NE.In_map2. eapply H2. simplify.
    specialize (H0 _ _ H4 H5).
    destruct (eqd x1 x0); subst; try contradiction.
    apply H0 in n.
    unfold "⇒" in *; intros. rewrite negate_correct.
    rewrite deep_simplify_correct. rewrite <- negate_correct. apply n.
    erewrite <- deep_simplify_correct; eassumption. }
  constructor; auto.
  generalize dependent x. induction x; crush; [constructor|].
  inv H1.
  assert (forall x0 y, GiblePargenproofEquiv.NE.In x0 x -> GiblePargenproofEquiv.NE.In y x -> x0 <> y -> fst x0 ⇒ ¬ fst y).
  { intros. eapply H0; auto; constructor; tauto. }
  assert (forall x0 y : pred_op * A,
    GiblePargenproofEquiv.NE.In x0
      (GiblePargenproofEquiv.NE.map (fun x1 : Predicate.pred_op * A => (deep_simplify peq (fst x1), snd x1)) x) ->
    GiblePargenproofEquiv.NE.In y
      (GiblePargenproofEquiv.NE.map (fun x1 : Predicate.pred_op * A => (deep_simplify peq (fst x1), snd x1)) x) ->
    x0 <> y -> fst x0 ⇒ ¬ fst y).
  { intros. eapply H; auto; constructor; tauto. }
  constructor; eauto.
  unfold not; intros.
  Abort.

Lemma prune_predicated_mutexcl :
  forall A (x: predicated A) y,
    predicated_mutexcl x ->
    prune_predicated x = Some y ->
    predicated_mutexcl y.
Proof.
  unfold prune_predicated; intros.
  Abort.
(*#[local] Hint Resolve prune_predicated_mutexcl : mte.*)

Lemma app_predicated_mutexcl :
  forall A p (x: predicated A) y,
    predicated_mutexcl x ->
    predicated_mutexcl y ->
    predicated_mutexcl (app_predicated p x y).
Proof. Abort.
(*#[local] Hint Resolve app_predicated_mutexcl : mte.*)

Lemma seq_app_predicated_mutexcl :
  forall A B (f: predicated (A -> B)) y,
    predicated_mutexcl f ->
    predicated_mutexcl y ->
    predicated_mutexcl (seq_app f y).
Proof. Abort.
(* #[local] Hint Resolve seq_app_predicated_mutexcl : mte. *)

Lemma all_predicated_mutexcl:
  forall f l,
    all_mutexcl f ->
    predicated_mutexcl (merge (list_translation l f)).
Proof. Abort.
(* #[local] Hint Resolve all_predicated_mutexcl : mte. *)

Lemma flap2_predicated_mutexcl :
  forall A B C (f: predicated (A -> B -> C)) x y,
    predicated_mutexcl f ->
    predicated_mutexcl (flap2 f x y).
Proof. Abort.
(* #[local] Hint Resolve flap2_predicated_mutexcl : mte. *)

Lemma all_mutexcl_set :
  forall f n r,
    all_mutexcl f ->
    predicated_mutexcl n ->
    all_mutexcl f #r r <- n.
Proof.
  unfold all_mutexcl; intros.
  destruct (resource_eq x r); subst.
  { now rewrite forest_reg_gss. }
  now rewrite forest_reg_gso by auto.
Qed.
#[local] Hint Resolve all_mutexcl_set : mte.

Lemma pred_ret_mutexcl :
  forall A (a: A), predicated_mutexcl (pred_ret a).
Proof.
  unfold pred_ret. repeat constructor; intros. inv H. inv H0. contradiction.
Qed.
#[local] Hint Resolve pred_ret_mutexcl : mte.

Lemma all_mutexcl_maintained :
  forall f p p' f' i,
    all_mutexcl f ->
    update (p, f) i = Some (p', f') ->
    all_mutexcl f'.
Proof.
  destruct i; cbn -[seq_app]; intros; unfold Option.bind in *; repeat destr; inv H0.
  - trivial.
  (* - apply prune_predicated_mutexcl in Heqo1; auto with mte. *)
  (* - apply prune_predicated_mutexcl in Heqo0; auto with mte. *)
  (* - apply prune_predicated_mutexcl in Heqo0; auto with mte. *)
  (*   apply app_predicated_mutexcl; auto with mte. *)
  (* - unfold all_mutexcl; intros; rewrite forest_pred_reg; auto. *)
  (* - unfold all_mutexcl; intros. unfold "<-e". unfold "#r". cbn. *)
  (*   fold (get_forest x f). auto. *)
Abort.
