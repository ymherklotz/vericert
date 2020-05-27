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

    Lemma merge_add :
      forall k v am bm,
      find k am = Some v ->
      find k (merge am bm) = Some v.
    Proof. unfold merge. auto with assocmap. Qed.

    Lemma merge_base :
      forall am,
        merge (empty elt) am = am.
    Proof. auto. Qed.

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
