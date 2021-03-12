(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *               2020 James Pollard <j@mes.dev>
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

Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.

Definition reg := positive.

Module AssocMap := Maps.PTree.

Module AssocMapExt.
  Import AssocMap.

  Hint Resolve elements_correct elements_complete
       elements_keys_norepet : assocmap.
  Hint Resolve gso gss : assocmap.

  Section Operations.

    Variable A : Type.

    Definition get_default (a : A) (k : reg) (m : t A) : A :=
      match get k m with
      | None => a
      | Some v => v
      end.

    Fixpoint merge (m1 m2 : t A) : t A :=
      match m1, m2 with
      | Node l1 (Some a) r1, Node l2 _ r2 => Node (merge l1 l2) (Some a) (merge r1 r2)
      | Node l1 None r1, Node l2 o r2 => Node (merge l1 l2) o (merge r1 r2)
      | Leaf, _ => m2
      | _, _ => m1
      end.

    Lemma merge_base_1 :
      forall am,
      merge (empty A) am = am.
    Proof. auto. Qed.
    Hint Resolve merge_base_1 : assocmap.

    Lemma merge_base_2 :
      forall am,
      merge am (empty A) = am.
    Proof.
      unfold merge.
      destruct am; trivial.
      destruct o; trivial.
    Qed.
    Hint Resolve merge_base_2 : assocmap.

    Lemma merge_add_assoc :
      forall r am am' v,
      merge (set r v am) am' = set r v (merge am am').
    Proof.
      induction r; intros; destruct am; destruct am'; try (destruct o); simpl;
        try rewrite IHr; try reflexivity.
    Qed.
    Hint Resolve merge_add_assoc : assocmap.

    Lemma merge_correct_1 :
      forall am bm k v,
      get k am = Some v ->
      get k (merge am bm) = Some v.
    Proof.
      induction am; intros; destruct k; destruct bm; try (destruct o); simpl;
        try rewrite gempty in H; try discriminate; try assumption; auto.
    Qed.
    Hint Resolve merge_correct_1 : assocmap.

    Lemma merge_correct_2 :
      forall am bm k v,
      get k am = None ->
      get k bm = Some v ->
      get k (merge am bm) = Some v.
    Proof.
      induction am; intros; destruct k; destruct bm; try (destruct o); simpl;
        try rewrite gempty in H; try discriminate; try assumption; auto.
    Qed.
    Hint Resolve merge_correct_2 : assocmap.

    Lemma merge_correct_3 :
      forall am bm k,
      get k am = None ->
      get k bm = None ->
      get k (merge am bm) = None.
    Proof.
      induction am; intros; destruct k; destruct bm; try (destruct o); simpl;
        try rewrite gempty in H; try discriminate; try assumption; auto.
    Qed.
    Hint Resolve merge_correct_3 : assocmap.

    Definition merge_fold (am bm : t A) : t A :=
      fold_right (fun p a => set (fst p) (snd p) a) bm (elements am).

    Lemma add_assoc :
      forall (k : elt) (v : A) l bm,
      List.In (k, v) l ->
      list_norepet (List.map fst l) ->
      @get A k (fold_right (fun p a => set (fst p) (snd p) a) bm l) = Some v.
    Proof.
      induction l; intros.
      - contradiction.
      - destruct a as [k' v'].
        destruct (peq k k').
        + inversion H. inversion H1. inversion H0. subst.
          simpl. auto with assocmap.

          inversion H0; subst. apply in_map with (f:=fst) in H1. contradiction.

        + inversion H. inversion H1. inversion H0. subst. simpl. rewrite gso; try assumption.
          apply IHl. contradiction. contradiction.
          simpl. rewrite gso; try assumption. apply IHl. assumption. inversion H0. subst. assumption.
    Qed.
    Hint Resolve add_assoc : assocmap.

    Lemma not_in_assoc :
      forall k v l bm,
      ~ List.In k (List.map (@fst elt A) l) ->
      @get A k bm = Some v ->
      get k (fold_right (fun p a => set (fst p) (snd p) a) bm l) = Some v.
    Proof.
      induction l; intros.
      - assumption.
      - destruct a as [k' v'].
        destruct (peq k k'); subst;
          simpl in *; apply Decidable.not_or in H; destruct H. contradiction.
        rewrite AssocMap.gso; auto.
    Qed.
    Hint Resolve not_in_assoc : assocmap.

    Lemma elements_iff :
      forall am k,
      (exists v, get k am = Some v) <->
      List.In k (List.map (@fst _ A) (elements am)).
    Proof.
      split; intros.
      destruct H. apply elements_correct in H. apply in_map with (f := fst) in H. apply H.
      apply list_in_map_inv in H. destruct H. destruct H. subst.
      exists (snd x). apply elements_complete. assert (x = (fst x, snd x)) by apply surjective_pairing.
      rewrite H in H0; assumption.
    Qed.
    Hint Resolve elements_iff : assocmap.

    Lemma elements_correct' :
      forall am k,
      ~ (exists v, get k am = Some v) <->
      ~ List.In k (List.map (@fst _ A) (elements am)).
    Proof. auto using not_iff_compat with assocmap. Qed.
    Hint Resolve elements_correct' : assocmap.

    Lemma elements_correct_none :
      forall am k,
      get k am = None ->
      ~ List.In k (List.map (@fst _ A) (elements am)).
    Proof.
      intros. apply elements_correct'. unfold not. intros.
      destruct H0. rewrite H in H0. discriminate.
    Qed.
    Hint Resolve elements_correct_none : assocmap.

    Lemma merge_fold_add :
      forall k v am bm,
      am ! k = Some v ->
      (merge_fold am bm) ! k = Some v.
    Proof. unfold merge_fold; auto with assocmap. Qed.
    Hint Resolve merge_fold_add : assocmap.

    Lemma merge_fold_not_in :
      forall k v am bm,
      get k am = None ->
      get k bm = Some v ->
      get k (merge_fold am bm) = Some v.
    Proof. intros. apply not_in_assoc; auto with assocmap. Qed.
    Hint Resolve merge_fold_not_in : assocmap.

    Lemma merge_fold_base :
      forall am,
      merge_fold (empty A) am = am.
    Proof. auto. Qed.
    Hint Resolve merge_fold_base : assocmap.

  End Operations.

End AssocMapExt.
Import AssocMapExt.

Definition assocmap := AssocMap.t value.

Definition find_assocmap (n : nat) : reg -> assocmap -> value :=
  get_default value (ZToValue 0).

Definition empty_assocmap : assocmap := AssocMap.empty value.

Definition merge_assocmap : assocmap -> assocmap -> assocmap := merge value.

Ltac unfold_merge :=
  unfold merge_assocmap; try (repeat (rewrite merge_add_assoc));
  rewrite AssocMapExt.merge_base_1.

Declare Scope assocmap.
Notation "a ! b" := (AssocMap.get b a) (at level 1) : assocmap.
Notation "a # ( b , c )" := (find_assocmap c b a) (at level 1) : assocmap.
Notation "a # b" := (find_assocmap 32 b a) (at level 1) : assocmap.
Notation "a ## b" := (List.map (fun c => find_assocmap 32 c a) b) (at level 1) : assocmap.
Notation "a # b '<-' c" := (AssocMap.set b c a) (at level 1, b at next level) : assocmap.

Local Open Scope assocmap.
Lemma find_get_assocmap :
  forall assoc r v,
  assoc ! r = Some v ->
  assoc # r = v.
Proof. intros. unfold find_assocmap, AssocMapExt.get_default. rewrite H. trivial. Qed.
