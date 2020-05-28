(*
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
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

From coqup Require Import Coquplib Value.
From Coq Require Import FSets.FMapPositive.

From compcert Require Import Maps.

Search Maps.PTree.get not List.In.

Definition reg := positive.

Module AssocMap := PositiveMap.

Module AssocMapExt.
  Import AssocMap.

  Hint Resolve elements_3w : assocmap.
  Hint Resolve elements_correct : assocmap.
  Hint Resolve gss : assocmap.
  Hint Resolve gso : assocmap.

  Section Operations.

    Variable elt : Type.

    Definition find_default (a : elt) (k : reg) (m : t elt) : elt :=
      match find k m with
      | None => a
      | Some v => v
      end.

    Definition merge (am bm : t elt) : t elt :=
      fold_right (fun p a => add (fst p) (snd p) a) bm (elements am).

    Lemma add_assoc :
      forall k v l bm,
      List.In (k, v) l ->
      SetoidList.NoDupA (@eq_key elt) l ->
      @find elt k (fold_right (fun p a => add (fst p) (snd p) a) bm l) = Some v.
    Proof.
      Hint Resolve SetoidList.InA_alt : assocmap.
      Hint Extern 1 (exists _, _) => apply list_in_map_inv : assocmap.

      induction l; intros.
      - contradiction.
      - destruct a as [k' v'].
        destruct (peq k k').
        + inversion H. inversion H1. inversion H0. subst.
          simpl. auto with assocmap.

          subst. inversion H0. subst. apply in_map with (f := fst) in H1. simpl in *.
          unfold not in H4. exfalso. apply H4. apply SetoidList.InA_alt.
          auto with assocmap.

        + inversion H. inversion H1. inversion H0. subst. simpl. rewrite gso; try assumption.
          apply IHl. contradiction. contradiction.
          simpl. rewrite gso; try assumption. apply IHl. assumption. inversion H0. subst. assumption.
    Qed.
    Hint Resolve add_assoc : assocmap.

    Lemma not_in_assoc :
      forall k v l bm,
      ~ List.In k (List.map (@fst key elt) l) ->
      @find elt k bm = Some v ->
      @find elt k (fold_right (fun p a => add (fst p) (snd p) a) bm l) = Some v.
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
      (exists v, find k am = Some v) <->
      List.In k (List.map (@fst _ elt) (elements am)).
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
      ~ (exists v, find k am = Some v) <->
      ~ List.In k (List.map (@fst _ elt) (elements am)).
    Proof. auto using not_iff_compat with assocmap. Qed.
    Hint Resolve elements_correct' : assocmap.

    Lemma elements_correct_none :
      forall am k,
      find k am = None ->
      ~ List.In k (List.map (@fst _ elt) (elements am)).
    Proof.
      intros. apply elements_correct'. unfold not. intros.
      destruct H0. rewrite H in H0. discriminate.
    Qed.
    Hint Resolve elements_correct_none : assocmap.

    Lemma merge_add :
      forall k v am bm,
      find k am = Some v ->
      find k (merge am bm) = Some v.
    Proof. unfold merge. auto with assocmap. Qed.
    Hint Resolve merge_add : assocmap.

    Lemma merge_not_in :
      forall k v am bm,
      find k am = None ->
      find k bm = Some v ->
      find k (merge am bm) = Some v.
    Proof. intros. apply not_in_assoc; auto with assocmap. Qed.
    Hint Resolve merge_not_in : assocmap.

    Lemma merge_base :
      forall am,
        merge (empty elt) am = am.
    Proof. auto. Qed.
    Hint Resolve merge_base : assocmap.

  End Operations.

End AssocMapExt.
Import AssocMapExt.

Definition assocmap := AssocMap.t value.

Definition find_assocmap (n : nat) : reg -> assocmap -> value :=
  find_default value (ZToValue n 0).

Definition empty_assocmap : assocmap := AssocMap.empty value.

Definition merge_assocmap : assocmap -> assocmap -> assocmap := merge value.

Module AssocMapNotation.
  Notation "a ! b" := (AssocMap.find b a) (at level 1).
  Notation "a # ( b , c )" := (find_assocmap c b a) (at level 1).
  Notation "a # b" := (find_assocmap 32 b a) (at level 1).
  Notation "a ## b" := (List.map (fun c => find_assocmap 32 c a) b) (at level 1).
End AssocMapNotation.
