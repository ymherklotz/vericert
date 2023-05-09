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

Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.SetoidDec.
Require Import Coq.Logic.Decidable.

Inductive non_empty (A: Type) :=
| singleton : A -> non_empty A
| cons : A -> non_empty A -> non_empty A
.

Arguments singleton [A].
Arguments cons [A].

Declare Scope non_empty_scope.
Delimit Scope non_empty_scope with non_empty.

Module NonEmptyNotation.
  Infix "::|" := cons (at level 60, right associativity) : non_empty_scope.
End NonEmptyNotation.
Import NonEmptyNotation.

#[local] Open Scope non_empty_scope.

Fixpoint map {A B} (f: A -> B) (l: non_empty A): non_empty B :=
  match l with
  | singleton a => singleton (f a)
  | a ::| b => f a ::| map f b
  end.

Fixpoint to_list {A} (l: non_empty A): list A :=
  match l with
  | singleton a => a::nil
  | a ::| b => a :: to_list b
  end.

Fixpoint app {A} (l1 l2: non_empty A) :=
  match l1 with
  | singleton a => a ::| l2
  | a ::| b => a ::| app b l2
  end.

Fixpoint non_empty_prod {A B} (l: non_empty A) (l': non_empty B) :=
  match l with
  | singleton a => map (fun x => (a, x)) l'
  | a ::| b => app (map (fun x => (a, x)) l') (non_empty_prod b l')
  end.

Fixpoint of_list {A} (l: list A): option (non_empty A) :=
  match l with
  | a::nil => Some (singleton a)
  | a::b =>
      match of_list b with
      | Some b' => Some (a ::| b')
      | _ => None
      end
  | nil => None
  end.

Fixpoint of_list_def {A} (d: A) (l: list A): non_empty A :=
  match l with
  | a::b => a ::| of_list_def d b
  | nil => singleton d
  end.

Fixpoint replace {A} (f: A -> A -> bool) (a b: A) (l: non_empty A) :=
  match l with
  | a' ::| l' => if f a a' then b ::| replace f a b l' else a' ::| replace f a b l'
  | singleton a' => if f a a' then singleton b else singleton a'
  end.

Inductive In {A: Type} (x: A) : non_empty A -> Prop :=
| In_cons : forall a b, x = a \/ In x b -> In x (a ::| b)
| In_single : In x (singleton x).

Ltac inv X := inversion X; clear X; subst.

Lemma in_dec:
  forall A (a: A) (l: non_empty A),
    (forall a b: A, {a = b} + {a <> b}) ->
    {In a l} + {~ In a l}.
Proof.
  induction l; intros.
  { specialize (X a a0). inv X.
    left. constructor.
    right. unfold not. intros. apply H. inv H0. auto. }
  { pose proof X as X2.
    specialize (X a a0). inv X.
    left. constructor; tauto.
    apply IHl in X2. inv X2.
    left. constructor; tauto.
    right. unfold not in *; intros. apply H0. inv H1. now inv H3. }
Qed.

Fixpoint filter {A: Type} (f: A -> bool) (l: non_empty A) : option (non_empty A) :=
  match l with
  | singleton a =>
      if f a then Some (singleton a) else None
  | a ::| b =>
      if f a then
        match filter f b with Some x => Some (a ::| x) | None => Some (singleton a) end
      else filter f b
  end.

Fixpoint fold_left {A B} (f: A -> B -> A) (l: non_empty B) (a: A) {struct l} : A :=
  match l with
  | singleton a' => f a a'
  | b ::| t => fold_left f t (f a b)
  end.

Fixpoint fold_right {A B} (f: B -> A -> A) (a: A) (l: non_empty B) {struct l} : A :=
  match l with
  | singleton a' => f a' a
  | b ::| t => f b (fold_right f a t)
  end.

Fixpoint eqb {A} (val_eqb: forall a b: A, {a = b} + {a <> b})
  (n1 n2: non_empty A): bool :=
  match n1, n2 with
  | n1a ::| n1b, n2a ::| n2b =>
    if val_eqb n1a n2a
    then eqb val_eqb n1b n2b
    else false
  | singleton a, singleton b => if val_eqb a b then true else false
  | _, _ => false
  end.

Lemma eqb_sound:
  forall A val_eqb n1 n2,
    @eqb A val_eqb n1 n2 = true ->
    n1 = n2.
Proof.
  induction n1; destruct n2; intros; try discriminate;
    cbn in H; destruct (val_eqb a a0); try now subst; [].
  f_equal; now eauto.
Qed.

Lemma eqb_complete:
  forall A val_eqb n1 n2,
    n1 = n2 ->
    @eqb A val_eqb n1 n2 = true.
Proof.
  induction n1; destruct n2; intros; try discriminate;
    cbn in *; inv H; destruct (val_eqb a0 a0); auto.
Qed.

Definition eq_dec:
  forall A (val_eqb: forall a b: A, {a = b} + {a <> b}) (n1 n2: non_empty A),
    {n1 = n2} + {n1 <> n2}.
Proof.
  intros.
  case_eq (@eqb A val_eqb n1 n2); intros.
  - apply eqb_sound in H; tauto.
  - assert (n1 <> n2); unfold not; intros.
    apply Bool.not_true_iff_false in H. apply H.
    apply eqb_complete; auto. tauto.
Qed.

Inductive Forall {A : Type} (P : A -> Prop) : non_empty A -> Prop :=
| Forall_singleton a : P a -> Forall P (singleton a)
| Forall_cons x l : P x -> Forall P l -> Forall P (x ::| l).

Inductive Forall2 {A B : Type} (R : A -> B -> Prop) : non_empty A -> non_empty B -> Prop :=
| Forall2_singleton : forall a b, R a b -> Forall2 R (singleton a) (singleton b)
| Forall2_cons : forall (x : A) (y : B) (l : non_empty A) (l' : non_empty B),
  R x y -> Forall2 R l l' -> Forall2 R (x ::| l) (y ::| l').

Definition equivP {A R} `{Equivalence A R} n1 n2 := Forall2 R n1 n2.

Fixpoint equivb {A} `{EqDec A} (n1 n2: non_empty A): bool :=
  match n1, n2 with
  | n1a ::| n1b, n2a ::| n2b =>
    if n1a == n2a
    then equivb n1b n2b
    else false
  | singleton a, singleton b => if a == b then true else false
  | _, _ => false
  end.

Lemma equivb_symm : forall A (SET: Setoid A) (EQD: EqDec SET) (a b: non_empty A),
  equivb a b = equivb b a.
Proof.
  induction a; destruct b; try easy; cbn.
  - destruct (a == a0).
    + symmetry in e. destruct (a0 == a); easy.
    + destruct (a0 == a); try easy. now symmetry in e.
  - destruct (a == a1).
    + symmetry in e. destruct (a1 == a); easy.
    + destruct (a1 == a); try easy. now symmetry in e.
Qed.

Inductive norepet {A : Type} : non_empty A -> Prop :=
| norepet_singleton a : norepet (singleton a)
| list_norepet_cons hd tl :
  ~ In hd tl -> norepet tl -> norepet (hd ::| tl).

Lemma NEin_NEapp5 :
  forall A (a: A) x y,
    In a (app x y) ->
    In a x \/ In a y.
Proof.
  induction x; cbn in *; intros.
  - inv H. inv H1. left. constructor. tauto.
  - inv H. inv H1. left. constructor; tauto.
    apply IHx in H. inv H; intuition (constructor; auto).
Qed.
