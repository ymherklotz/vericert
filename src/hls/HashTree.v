(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021-2022 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.Structures.Equalities.

Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.

#[local] Open Scope positive.

#[local] Hint Resolve in_eq : core.
#[local] Hint Resolve in_cons : core.

Definition max_key {A} (t: PTree.t A) :=
  fold_right Pos.max 1%positive (map fst (PTree.elements t)).

Lemma max_key_correct' :
  forall l hi, In hi l -> hi <= fold_right Pos.max 1 l.
Proof.
  induction l; crush.
  inv H. lia.
  destruct (Pos.max_dec a (fold_right Pos.max 1 l)); rewrite e.
  - apply Pos.max_l_iff in e.
    assert (forall a b c, a <= c -> c <= b -> a <= b) by lia.
    eapply H; eauto.
  - apply IHl; auto.
Qed.

Lemma max_key_correct :
  forall A h_tree hi (c: A),
    h_tree ! hi = Some c ->
    hi <= max_key h_tree.
Proof.
  unfold max_key. intros. apply PTree.elements_correct in H.
  apply max_key_correct'.
  eapply in_map with (f := fst) in H. auto.
Qed.

Lemma max_not_present :
  forall A k (h: PTree.t A), k > max_key h -> h ! k = None.
Proof.
  intros. destruct (h ! k) eqn:?; auto.
  apply max_key_correct in Heqo. lia.
Qed.

Lemma filter_none :
  forall A f l (x: A), filter f l = nil -> In x l -> f x = false.
Proof. induction l; crush; inv H0; subst; destruct_match; crush. Qed.

Lemma filter_set :
  forall A l l' f (x: A),
    (In x l -> In x l') ->
    In x (filter f l) ->
    In x (filter f l').
Proof.
  induction l; crush.
  destruct_match; crush. inv H0; crush.
  apply filter_In. simplify; crush.
Qed.

Lemma filter_cons_true :
  forall A f l (a: A) l',
    filter f l = a :: l' -> f a = true.
Proof.
  induction l; crush. destruct (f a) eqn:?.
  inv H. auto. eapply IHl; eauto.
Qed.

Lemma PTree_set_elements :
  forall A t x x' (c: A),
    In x (PTree.elements t) ->
    x' <> (fst x) ->
    In x (PTree.elements (PTree.set x' c t)).
Proof.
  intros. destruct x.
  eapply PTree.elements_correct. simplify.
  rewrite PTree.gso; auto. apply PTree.elements_complete in H. auto.
Qed.

Lemma filter_set2 :
  forall A x y z (h: PTree.t A),
    In z (PTree.elements (PTree.set x y h)) ->
    In z (PTree.elements h) \/ fst z = x.
Proof.
  intros. destruct z.
  destruct (Pos.eq_dec p x); subst.
  tauto.
  left. apply PTree.elements_correct. apply PTree.elements_complete in H.
  rewrite PTree.gso in H; auto.
Qed.

Lemma in_filter : forall A f l (x: A), In x (filter f l) -> In x l.
Proof. induction l; crush. destruct_match; crush. inv H; crush. Qed.

Lemma filter_norepet:
  forall A f (l: list A),
    list_norepet l ->
    list_norepet (filter f l).
Proof.
  induction l; crush.
  inv H. destruct (f a).
  constructor. unfold not in *; intros. apply H2.
  eapply in_filter; eauto.
  apply IHl; auto.
  apply IHl; auto.
Qed.

Lemma filter_norepet2:
  forall A B g (l: list (A * B)),
    list_norepet (map fst l) ->
    list_norepet (map fst (filter g l)).
Proof.
  induction l; crush.
  inv H. destruct (g a) eqn:?.
  simplify. constructor. unfold not in *. intros.
  eapply H2.
  apply list_in_map_inv in H. simplify; subst.
  rewrite H.
  apply filter_In in H1. simplify.
  apply in_map. eauto.
  eapply IHl. eauto.
  eapply IHl. eauto.
Qed.

Module Type Hashable := UsualDecidableType.

Module HashTree(H: Hashable).

  Import H.

  Definition hash := positive.
  Definition hash_tree := PTree.t t.

  Definition find_tree (el: t) (h: hash_tree) : option hash :=
    match filter (fun x => if eq_dec el (snd x) then true else false) (PTree.elements h) with
    | (p, _) :: nil => Some p
    | _ => None
    end.

  Definition hash_value (max: hash) (e: t) (h: hash_tree): hash * hash_tree :=
    match find_tree e h with
    | Some p => (p, h)
    | None =>
      let nkey := Pos.max max (max_key h) + 1 in
      (nkey, PTree.set nkey e h)
    end.

  Definition wf_hash_table h_tree :=
    forall x c, h_tree ! x = Some c -> find_tree c h_tree = Some x.

  Lemma find_tree_correct :
    forall c h_tree p,
      find_tree c h_tree = Some p ->
      h_tree ! p = Some c.
  Proof.
    intros.
    unfold find_tree in H. destruct_match; crush.
    destruct_match; simplify.
    destruct_match; crush.
    assert (In (p, t0) (filter
                          (fun x : hash * t =>
                             if eq_dec c (snd x) then true else false) (PTree.elements h_tree))).
    { setoid_rewrite Heql. constructor; auto. }
    apply filter_In in H. simplify. destruct_match; crush. subst.
    apply PTree.elements_complete; auto.
  Qed.

  Lemma find_tree_unique :
    forall c h_tree p p',
      find_tree c h_tree = Some p ->
      h_tree ! p' = Some c ->
      p = p'.
  Proof.
    intros.
    unfold find_tree in H.
    repeat (destruct_match; crush; []).
    assert (In (p, t0) (filter
                          (fun x : hash * t =>
                             if eq_dec c (snd x) then true else false) (PTree.elements h_tree))).
    { setoid_rewrite Heql. constructor; auto. }
    apply filter_In in H. simplify.
    destruct (Pos.eq_dec p p'); auto.
    exfalso.
    destruct_match; subst; crush.
    assert (In (p', t0) (PTree.elements h_tree) /\ (fun x : hash * t =>
                                                      if eq_dec t0 (snd x) then true else false) (p', t0) = true).
    { split. apply PTree.elements_correct. auto. setoid_rewrite Heqs. auto. }
    apply filter_In in H. setoid_rewrite Heql in H. inv H. simplify. crush. crush.
  Qed.

  Lemma hash_no_element' :
    forall c h_tree,
      find_tree c h_tree = None ->
      wf_hash_table h_tree ->
      ~ forall x, h_tree ! x = Some c.
  Proof.
    unfold not, wf_hash_table; intros.
    specialize (H1 1). eapply H0 in H1. crush.
  Qed.

  Lemma hash_no_element :
    forall c h_tree,
      find_tree c h_tree = None ->
      wf_hash_table h_tree ->
      ~ exists x, h_tree ! x = Some c.
  Proof.
    unfold not, wf_hash_table; intros.
    simplify. apply H0 in H2. rewrite H in H2. crush.
  Qed.

  Lemma wf_hash_table_set_gso' :
    forall h x p0 c',
      filter
        (fun x : hash * t =>
           if eq_dec c' (snd x) then true else false) (PTree.elements h) =
      (x, p0) :: nil ->
      h ! x = Some p0 /\ p0 = c'.
  Proof.
    intros.
    match goal with
    | H: filter ?f ?el = ?x::?xs |- _ =>
      assert (In x (filter f el)) by (rewrite H; crush)
    end.
    apply filter_In in H0. simplify. destruct_match; subst; crush.
    apply PTree.elements_complete; auto.
    destruct_match; crush.
  Qed.

  Lemma wf_hash_table_set_gso :
    forall x x' c' c h,
      x <> x' ->
      wf_hash_table h ->
      find_tree c' h = Some x ->
      find_tree c h = None ->
      find_tree c' (PTree.set x' c h) = Some x.
  Proof.
    intros. pose proof H1 as X. unfold find_tree in H1.
    destruct_match; crush.
    destruct p. destruct l; crush.
    apply wf_hash_table_set_gso' in Heql. simplify.
    pose proof H2 as Z. apply hash_no_element in H2; auto.
    destruct (eq_dec c c'); subst.
    { exfalso. eapply H2. econstructor; eauto. }
    unfold wf_hash_table in H0.
    assert (In (x', c) (PTree.elements (PTree.set x' c h))).
    { apply PTree.elements_correct. rewrite PTree.gss; auto. }
    assert (In (x, c') (PTree.elements h)).
    { apply PTree.elements_correct; auto. }
    assert (In (x, c') (PTree.elements (PTree.set x' c h))).
    { apply PTree.elements_correct. rewrite PTree.gso; auto. }
    pose proof X as Y.
    unfold find_tree in X. repeat (destruct_match; crush; []).
    match goal with
    | H: filter ?f ?el = ?x::?xs |- _ =>
      assert (In x (filter f el)) by (rewrite H; crush)
    end.
    apply filter_In in H6. simplify. destruct_match; crush; subst.
    unfold find_tree. repeat (destruct_match; crush).
    { eapply filter_none in Heql0.
      2: { apply PTree.elements_correct. rewrite PTree.gso; eauto. }
      destruct_match; crush. }

    { subst.
      repeat match goal with
             | H: filter ?f ?el = ?x::?xs |- _ =>
               learn H; assert (In x (filter f el)) by (rewrite H; crush)
             end.
      eapply filter_set in H10. rewrite Heql0 in H10. inv H10. simplify. auto.
      inv H11. auto. inv H11. intros. eapply PTree_set_elements; auto. }

    { exfalso. subst.
      repeat match goal with
             | H: filter ?f ?el = ?x::?xs |- _ =>
               learn H; assert (In x (filter f el)) by (rewrite H; crush)
             end.

      pose proof H8 as X2. destruct p1.
      pose proof X2 as X4.
      apply in_filter in X2. apply PTree.elements_complete in X2.
      assert (In (p, t2) (filter
                            (fun x : positive * t => if eq_dec t0 (snd x) then true else false)
                            (PTree.elements (PTree.set x' c h)))) by (rewrite H6; eauto).
      pose proof H11 as X3.
      apply in_filter in H11. apply PTree.elements_complete in H11.
      destruct (peq p0 p); subst.
      {
        assert (list_norepet (map fst (filter
                                         (fun x : positive * t => if eq_dec t0 (snd x) then true else false)
                                         (PTree.elements (PTree.set x' c h))))).
        { eapply filter_norepet2. eapply PTree.elements_keys_norepet. }
        rewrite Heql0 in H12. simplify. inv H12. eapply H15. apply in_eq.
      }
      { apply filter_In in X4. simplify. destruct_match; crush; subst.
        apply filter_In in X3. simplify. destruct_match; crush; subst.
        destruct (peq p x'); subst.
        { rewrite PTree.gss in H11; crush. }
        { destruct (peq p0 x'); subst.
          { rewrite PTree.gss in X2; crush. }
          { rewrite PTree.gso in X2 by auto.
            rewrite PTree.gso in H11 by auto.
            assert (p = p0) by (eapply find_tree_unique; eauto).
            crush. } } } }
  Qed.

  Lemma wf_hash_table_set :
    forall h_tree c v (GT: v > max_key h_tree),
      find_tree c h_tree = None ->
      wf_hash_table h_tree ->
      wf_hash_table (PTree.set v c h_tree).
  Proof.
    unfold wf_hash_table; simplify.
    destruct (peq v x); subst.
    pose proof (hash_no_element c h_tree H H0).
    rewrite PTree.gss in H1. simplify.
    unfold find_tree.
    assert (In (x, c0) (PTree.elements (PTree.set x c0 h_tree))
            /\ (fun x : positive * t => if eq_dec c0 (snd x) then true else false)
                 (x, c0) = true).
    { simplify. apply PTree.elements_correct. rewrite PTree.gss. auto.
      destruct (eq_dec c0 c0); crush. }
    destruct_match.
    apply filter_In in H1. rewrite Heql in H1. crush.
    apply filter_In in H1. repeat (destruct_match; crush; []). subst.
    destruct l. simplify. rewrite Heql in H1. inv H1. inv H3. auto.
    crush.

    exfalso. apply H2. destruct p.
    pose proof Heql as X. apply filter_cons_true in X. destruct_match; crush; subst.
    assert (In (p0, t0) (filter
                           (fun x : positive * t => if eq_dec t0 (snd x) then true else false)
                           (PTree.elements (PTree.set x t0 h_tree)))) by (rewrite Heql; eauto).
    assert (In (p, t1) (filter
                          (fun x : positive * t => if eq_dec t0 (snd x) then true else false)
                          (PTree.elements (PTree.set x t0 h_tree)))) by (rewrite Heql; eauto).
    apply filter_In in H4. simplify. destruct_match; crush; subst.
    apply in_filter in H3. apply PTree.elements_complete in H5. apply PTree.elements_complete in H3.
    assert (list_norepet (map fst (filter
                                     (fun x : positive * t => if eq_dec t1 (snd x) then true else false)
                                     (PTree.elements (PTree.set x t1 h_tree))))).
    { eapply filter_norepet2. eapply PTree.elements_keys_norepet. }
    rewrite Heql in H4. simplify.
    destruct (peq p0 p); subst.
    { inv H4. exfalso. eapply H8. eauto. }
    destruct (peq x p); subst.
    rewrite PTree.gso in H3; auto. econstructor; eauto.
    rewrite PTree.gso in H5; auto. econstructor; eauto.

    rewrite PTree.gso in H1; auto.
    destruct (eq_dec c c0); subst.
    { apply H0 in H1. rewrite H in H1. discriminate. }
    apply H0 in H1.
    apply wf_hash_table_set_gso; eauto.
  Qed.

  Lemma wf_hash_table_distr :
    forall m p h_tree h h_tree',
      hash_value m p h_tree = (h, h_tree') ->
      wf_hash_table h_tree ->
      wf_hash_table h_tree'.
  Proof.
    unfold hash_value; simplify.
    destruct_match.
    - inv H; auto.
    - inv H. apply wf_hash_table_set; try lia; auto.
  Qed.

  Lemma wf_hash_table_eq :
    forall h_tree a b c,
      wf_hash_table h_tree ->
      h_tree ! a = Some c ->
      h_tree ! b = Some c ->
      a = b.
  Proof.
    unfold wf_hash_table; intros; apply H in H0; eapply find_tree_unique; eauto.
  Qed.

  Lemma hash_constant :
    forall p h h_tree hi c h_tree' m,
      h_tree ! hi = Some c ->
      hash_value m p h_tree = (h, h_tree') ->
      h_tree' ! hi = Some c.
  Proof.
    intros. unfold hash_value in H0. destruct_match.
    inv H0. eauto.
    inv H0.
    pose proof H. apply max_key_correct in H0.
    rewrite PTree.gso; solve [eauto | lia].
  Qed.

  Lemma find_tree_Some :
    forall el h v,
      find_tree el h = Some v ->
      h ! v = Some el.
  Proof.
    intros. unfold find_tree in *.
    destruct_match; crush. destruct p.
    destruct_match; crush.
    match goal with
    | H: filter ?f ?el = ?x::?xs |- _ =>
      assert (In x (filter f el)) by (rewrite H; crush)
    end.
    apply PTree.elements_complete.
    apply filter_In in H. inv H.
    destruct_match; crush.
  Qed.

  Lemma hash_present_eq :
    forall m e1 e2 p1 h h',
      hash_value m e2 h = (p1, h') ->
      h ! p1 = Some e1 -> e1 = e2.
  Proof.
    intros. unfold hash_value in *. destruct_match.
    - inv H. apply find_tree_Some in Heqo.
      rewrite Heqo in H0. inv H0. auto.
    - inv H. assert (h ! (Pos.max m (max_key h) + 1) = None)
        by (apply max_not_present; lia). crush.
  Qed.

End HashTree.
