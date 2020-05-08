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

(* begin hide *)
From bbv Require Import Word.
From bbv Require HexNotation WordScope.
From Coq Require Import ZArith.ZArith FSets.FMapPositive.
From compcert Require Import lib.Integers common.Values.
(* end hide *)

(** * Value

A [value] is a bitvector with a specific size. We are using the implementation
of the bitvector by mit-plv/bbv, because it has many theorems that we can reuse.
However, we need to wrap it with an [Inductive] so that we can specify and match
on the size of the [value]. This is necessary so that we can easily store
[value]s of different sizes in a list or in a map.

Using the default [word], this would not be possible, as the size is part of the type. *)

Record value : Type :=
  mkvalue {
    vsize: nat;
    vword: word vsize
  }.

(** ** Value conversions

Various conversions to different number types such as [N], [Z], [positive] and
[int], where the last one is a theory of integers of powers of 2 in CompCert. *)

Definition wordToValue : forall sz : nat, word sz -> value := mkvalue.

Definition valueToWord : forall v : value, word (vsize v) := vword.

Definition valueToNat (v :value) : nat :=
  wordToNat (vword v).

Definition natToValue sz (n : nat) : value :=
  mkvalue sz (natToWord sz n).

Definition valueToN (v : value) : N :=
  wordToN (vword v).

Definition NToValue sz (n : N) : value :=
  mkvalue sz (NToWord sz n).

Definition ZToValue (s : nat) (z : Z) : value :=
  mkvalue s (ZToWord s z).

Definition valueToZ (v : value) : Z :=
  wordToZ (vword v).

Definition uvalueToZ (v : value) : Z :=
  uwordToZ (vword v).

Definition posToValue sz (p : positive) : value :=
  mkvalue sz (posToWord sz p).

Definition posToValueAuto (p : positive) : value :=
  let size := Z.to_nat (Z.succ (log_inf p)) in
  mkvalue size (Word.posToWord size p).

Definition valueToPos (v : value) : positive :=
  match valueToZ v with
  | Zpos p => p
  | _ => 1
  end.

Definition intToValue (i : Integers.int) : value :=
  ZToValue Int.wordsize (Int.unsigned i).

Definition valueToInt (i : value) : Integers.int :=
  Int.repr (valueToZ i).

(** Convert a [value] to a [bool], so that choices can be made based on the
result. This is also because comparison operators will give back [value] instead
of [bool], so if they are in a condition, they will have to be converted before
they can be used. *)

Definition valueToBool (v : value) : bool :=
  negb (weqb (@wzero (vsize v)) (vword v)).

Definition boolToValue (sz : nat) (b : bool) : value :=
  natToValue sz (if b then 1 else 0).

(** ** Arithmetic operations *)

Definition unify_word (sz1 sz2 : nat) (w1 : word sz2): sz1 = sz2 -> word sz1.
intros; subst; assumption. Defined.

Definition value_eq_size:
  forall v1 v2 : value, { vsize v1 = vsize v2 } + { True }.
Proof.
  intros; destruct (Nat.eqb (vsize v1) (vsize v2)) eqn:?.
  left; apply Nat.eqb_eq in Heqb; assumption.
  right; trivial.
Defined.

Definition map_any {A : Type} (v1 v2 : value) (f : word (vsize v1) -> word (vsize v1) -> A)
           (EQ : vsize v1 = vsize v2) : A :=
    let w2 := unify_word (vsize v1) (vsize v2) (vword v2) EQ in
    f (vword v1) w2.

Definition map_any_opt {A : Type} (sz : nat) (v1 v2 : value) (f : word (vsize v1) -> word (vsize v1) -> A)
  : option A :=
  match value_eq_size v1 v2 with
  | left EQ =>
    Some (map_any v1 v2 f EQ)
  | _ => None
  end.

Definition map_word (f : forall sz : nat, word sz -> word sz) (v : value) : value :=
  mkvalue (vsize v) (f (vsize v) (vword v)).

Definition map_word2 (f : forall sz : nat, word sz -> word sz -> word sz) (v1 v2 : value)
           (EQ : (vsize v1 = vsize v2)) : value :=
    let w2 := unify_word (vsize v1) (vsize v2) (vword v2) EQ in
    mkvalue (vsize v1) (f (vsize v1) (vword v1) w2).

Definition map_word2_opt (f : forall sz : nat, word sz -> word sz -> word sz) (v1 v2 : value)
  : option value :=
  match value_eq_size v1 v2 with
  | left EQ => Some (map_word2 f v1 v2 EQ)
  | _ => None
  end.

Definition eq_to_opt (v1 v2 : value) (f : vsize v1 = vsize v2 -> value)
  : option value :=
  match value_eq_size v1 v2 with
  | left EQ => Some (f EQ)
  | _ => None
  end.

Lemma eqvalue {sz : nat} (x y : word sz) : x = y <-> mkvalue sz x = mkvalue sz y.
Proof.
  split; intros.
  subst. reflexivity. inversion H. apply existT_wordToZ in H1.
  apply wordToZ_inj. assumption.
Qed.

Lemma eqvaluef {sz : nat} (x y : word sz) : x = y -> mkvalue sz x = mkvalue sz y.
Proof. apply eqvalue. Qed.

Lemma nevalue {sz : nat} (x y : word sz) : x <> y <-> mkvalue sz x <> mkvalue sz y.
Proof. split; intros; intuition. apply H. apply eqvalue. assumption.
       apply H. rewrite H0. trivial.
Qed.

Lemma nevaluef {sz : nat} (x y : word sz) : x <> y -> mkvalue sz x <> mkvalue sz y.
Proof. apply nevalue. Qed.

(*Definition rewrite_word_size (initsz finalsz : nat) (w : word initsz)
  : option (word finalsz) :=
  match Nat.eqb initsz finalsz return option (word finalsz) with
  | true => Some _
  | false => None
  end.*)

Definition valueeq (sz : nat) (x y : word sz) :
  {mkvalue sz x = mkvalue sz y} + {mkvalue sz x <> mkvalue sz y} :=
  match weq x y with
  | left eq => left (eqvaluef x y eq)
  | right ne => right (nevaluef x y ne)
  end.

Definition valueeqb (x y : value) : bool :=
  match value_eq_size x y with
  | left EQ =>
    weqb (vword x) (unify_word (vsize x) (vsize y) (vword y) EQ)
  | right _ => false
  end.

Definition value_projZ_eqb (v1 v2 : value) : bool := Z.eqb (valueToZ v1) (valueToZ v2).

Theorem value_projZ_eqb_true :
  forall v1 v2,
  v1 = v2 -> value_projZ_eqb v1 v2 = true.
Proof. intros. subst. unfold value_projZ_eqb. apply Z.eqb_eq. trivial. Qed.

Theorem valueeqb_true_iff :
  forall v1 v2,
  valueeqb v1 v2 = true <-> v1 = v2.
Proof.
  split; intros.
  unfold valueeqb in H. destruct (value_eq_size v1 v2) eqn:?.
  - destruct v1, v2. simpl in H.
Abort.

Definition value_int_eqb (v : value) (i : int) : bool :=
  Z.eqb (valueToZ v) (Int.unsigned i).

(** Arithmetic operations over [value], interpreting them as signed or unsigned
depending on the operation.

The arithmetic operations over [word] are over [N] by default, however, can also
be called over [Z] explicitly, which is where the bits are interpreted in a
signed manner. *)

Definition vplus v1 v2 := map_word2 wplus v1 v2.
Definition vplus_opt v1 v2 := map_word2_opt wplus v1 v2.
Definition vminus v1 v2 := map_word2 wminus v1 v2.
Definition vmul v1 v2 := map_word2 wmult v1 v2.
Definition vdiv v1 v2 := map_word2 wdiv v1 v2.
Definition vmod v1 v2 := map_word2 wmod v1 v2.

Definition vmuls v1 v2 := map_word2 wmultZ v1 v2.
Definition vdivs v1 v2 := map_word2 wdivZ v1 v2.
Definition vmods v1 v2 := map_word2 wremZ v1 v2.

(** ** Bitwise operations

Bitwise operations over [value], which is independent of whether the number is
signed or unsigned. *)

Definition vnot v := map_word wnot v.
Definition vneg v := map_word wneg v.
Definition vbitneg v := boolToValue (vsize v) (negb (valueToBool v)).
Definition vor v1 v2 := map_word2 wor v1 v2.
Definition vand v1 v2 := map_word2 wand v1 v2.
Definition vxor v1 v2 := map_word2 wxor v1 v2.

(** ** Comparison operators

Comparison operators that return a bool, there should probably be an equivalent
which returns another number, however I might just add that as an explicit
conversion. *)

Definition veqb v1 v2 := map_any v1 v2 (@weqb (vsize v1)).
Definition vneb v1 v2 EQ := negb (veqb v1 v2 EQ).

Definition veq v1 v2 EQ := boolToValue (vsize v1) (veqb v1 v2 EQ).
Definition vne v1 v2 EQ := boolToValue (vsize v1) (vneb v1 v2 EQ).

Definition vltb v1 v2 := map_any v1 v2 wltb.
Definition vleb v1 v2 EQ := negb (map_any v2 v1 wltb (eq_sym EQ)).
Definition vgtb v1 v2 EQ := map_any v2 v1 wltb (eq_sym EQ).
Definition vgeb v1 v2 EQ := negb (map_any v1 v2 wltb EQ).

Definition vltsb v1 v2 := map_any v1 v2 wsltb.
Definition vlesb v1 v2 EQ := negb (map_any v2 v1 wsltb (eq_sym EQ)).
Definition vgtsb v1 v2 EQ := map_any v2 v1 wsltb (eq_sym EQ).
Definition vgesb v1 v2 EQ := negb (map_any v1 v2 wsltb EQ).

Definition vlt v1 v2 EQ := boolToValue (vsize v1) (vltb v1 v2 EQ).
Definition vle v1 v2 EQ := boolToValue (vsize v1) (vleb v1 v2 EQ).
Definition vgt v1 v2 EQ := boolToValue (vsize v1) (vgtb v1 v2 EQ).
Definition vge v1 v2 EQ := boolToValue (vsize v1) (vgeb v1 v2 EQ).

Definition vlts v1 v2 EQ := boolToValue (vsize v1) (vltsb v1 v2 EQ).
Definition vles v1 v2 EQ := boolToValue (vsize v1) (vlesb v1 v2 EQ).
Definition vgts v1 v2 EQ := boolToValue (vsize v1) (vgtsb v1 v2 EQ).
Definition vges v1 v2 EQ := boolToValue (vsize v1) (vgesb v1 v2 EQ).

(** ** Shift operators

Shift operators on values. *)

Definition shift_map (sz : nat) (f : word sz -> nat -> word sz) (w1 w2 : word sz) :=
  f w1 (wordToNat w2).

Definition vshl v1 v2 := map_word2 (fun sz => shift_map sz (@wlshift sz)) v1 v2.
Definition vshr v1 v2 := map_word2 (fun sz => shift_map sz (@wrshift sz)) v1 v2.

Module HexNotationValue.
  Export HexNotation.
  Import WordScope.

  Notation "sz ''h' a" := (NToValue sz (hex a)) (at level 50).

End HexNotationValue.

Inductive val_value_lessdef: val -> value -> Prop :=
| val_value_lessdef_int:
    forall i v',
    Integers.Int.unsigned i = valueToZ v' ->
    val_value_lessdef (Vint i) v'
| lessdef_undef: forall v, val_value_lessdef Vundef v.
