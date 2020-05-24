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

  Section Operations.

    Variable elt : Type.

    Definition find_default (a : elt) (k : reg) (m : t elt) : elt :=
      match find k m with
      | None => a
      | Some v => v
      end.

    Definition merge (m1 m2 : t elt) : t elt :=
      fold_right (fun el m => match el with (k, v) => add k v m end) m2 (elements m1).

    Lemma merge_add_assoc2 :
      forall am am' r v,
        merge (add r v am) am' = add r v (merge am am').
    Proof.
      induction am; intros.
      unfold merge. simpl. unfold fold_right. simpl. Search MapsTo.
      Abort.

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
