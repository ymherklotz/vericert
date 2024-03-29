(*
 * Vericert: Verified high-level synthesis.
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
From Coq Require Import ZArith.ZArith FSets.FMapPositive Lia.
From compcert Require Import lib.Integers common.Values.
From vericert Require Import Vericertlib.
(* end hide *)

(*|
=====
Value
=====

A ``value`` is a bitvector with a specific size. We are using the implementation
of the bitvector by mit-plv/bbv, because it has many theorems that we can reuse.
However, we need to wrap it with an ``Inductive`` so that we can specify and
match on the size of the ``value``. This is necessary so that we can easily
store ``value`` of different sizes in a list or in a map.

Using the default ``word``, this would not be possible, as the size is part of
the type.
|*)

Definition value : Type := int.

(*|
Value conversions
=================

Various conversions to different number types such as ``N``, ``Z``, ``positive``
and ``int``, where the last one is a theory of integers of powers of 2 in
CompCert.
|*)

Definition valueToNat (v : value) : nat :=
  Z.to_nat (Int.unsigned v).

Definition natToValue (n : nat) : value :=
  Int.repr (Z.of_nat n).

Definition valueToN (v : value) : N :=
  Z.to_N (Int.unsigned v).

Definition NToValue (n : N) : value :=
  Int.repr (Z.of_N n).

Definition ZToValue (z : Z) : value :=
  Int.repr z.

Definition valueToZ (v : value) : Z :=
  Int.signed v.

Definition uvalueToZ (v : value) : Z :=
  Int.unsigned v.

Definition posToValue (p : positive) : value :=
  Int.repr (Z.pos p).

Definition valueToPos (v : value) : positive :=
  Z.to_pos (Int.unsigned v).

Definition intToValue (i : Integers.int) : value := i.

Definition valueToInt (i : value) : Integers.int := i.

Definition ptrToValue (i : ptrofs) : value := Ptrofs.to_int i.

Definition valueToPtr (i : value) : Integers.ptrofs :=
  Ptrofs.of_int i.

Definition valToValue (v : Values.val) : option value :=
  match v with
  | Values.Vint i => Some (intToValue i)
  | Values.Vptr b off => Some (ptrToValue off)
  | Values.Vundef => Some (ZToValue 0%Z)
  | _ => None
  end.

(*|
Convert a ``value`` to a ``bool``, so that choices can be made based on the
result. This is also because comparison operators will give back ``value``
instead of ``bool``, so if they are in a condition, they will have to be
converted before they can be used.
|*)

Definition valueToBool (v : value) : bool :=
  if Z.eqb (uvalueToZ v) 0 then false else true.

Definition boolToValue (b : bool) : value :=
  natToValue (if b then 1 else 0).

(*|
Arithmetic operations
---------------------
|*)

Inductive val_value_lessdef: val -> value -> Prop :=
| val_value_lessdef_int:
    forall i v',
    i = valueToInt v' ->
    val_value_lessdef (Vint i) v'
| val_value_lessdef_ptr:
    forall b off v',
    off = valueToPtr v' ->
    val_value_lessdef (Vptr b off) v'
| lessdef_undef: forall v, val_value_lessdef Vundef v.

Inductive opt_val_value_lessdef: option val -> value -> Prop :=
| opt_lessdef_some:
    forall v v', val_value_lessdef v v' -> opt_val_value_lessdef (Some v) v'
| opt_lessdef_none: forall v, opt_val_value_lessdef None v.

Lemma valueToZ_ZToValue :
  forall z,
  (Int.min_signed <= z <= Int.max_signed)%Z ->
  valueToZ (ZToValue z) = z.
Proof. auto using Int.signed_repr. Qed.

Lemma uvalueToZ_ZToValue :
  forall z,
  (0 <= z <= Int.max_unsigned)%Z ->
  uvalueToZ (ZToValue z) = z.
Proof. auto using Int.unsigned_repr. Qed.

Lemma valueToPos_posToValue :
  forall v,
  0 <= Z.pos v <= Int.max_unsigned ->
  valueToPos (posToValue v) = v.
Proof.
  unfold valueToPos, posToValue.
  intros. rewrite Int.unsigned_repr.
  apply Pos2Z.id. assumption.
Qed.

Lemma valueToInt_intToValue :
  forall v,
  valueToInt (intToValue v) = v.
Proof. auto. Qed.

Lemma valToValue_lessdef :
  forall v v',
    valToValue v = Some v' ->
    val_value_lessdef v v'.
Proof.
  intros.
  destruct v; try discriminate; constructor.
  unfold valToValue in H. inversion H.
  unfold valueToInt. unfold intToValue in H1. auto.
  inv H. symmetry. unfold valueToPtr, ptrToValue. apply Ptrofs.of_int_to_int. trivial.
Qed.

Ltac simplify_val := repeat (simplify; unfold uvalueToZ, valueToPtr, Ptrofs.of_int, valueToInt, intToValue,
                                       ptrToValue in *).

Ltac crush_val := simplify_val; try discriminate; try congruence; try lia; liapp; try assumption.
