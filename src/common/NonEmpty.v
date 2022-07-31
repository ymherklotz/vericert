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
  | a::b =>
      match of_list b with
      | Some b' => Some (a ::| b')
      | _ => None
      end
  | nil => None
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
