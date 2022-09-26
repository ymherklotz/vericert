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

From Coq Require Import Lists.List.

Declare Scope vericert_scope.
#[local] Open Scope vericert_scope.

Declare Scope monad_scope.

Module Type Monad.

  Parameter mon : Type -> Type.

  Parameter ret : forall (A : Type) (x : A), mon A.
  Arguments ret [A].

  Parameter bind : forall (A B : Type) (g : A -> mon B) (f : mon A), mon B.
  Arguments bind [A B].

  Parameter bind2 : forall (A B C: Type) (g: A -> B -> mon C) (f: mon (A * B)), mon C.
  Arguments bind2 [A B C].

End Monad.

Module MonadExtra(M : Monad).
  Import M.

  Module Import MonadNotation.

    Notation "'do' X <- A ; B" :=
      (bind (fun X => B) A)
        (at level 200, X name, A at level 100, B at level 200) : monad_scope.
    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 (fun X Y => B) A)
        (at level 200, X name, Y name, A at level 100, B at level 200) : monad_scope.

  End MonadNotation.

  #[local] Open Scope monad_scope.

  Fixpoint traverselist {A B: Type} (f: A -> mon B) (l: list A) {struct l}: mon (list B) :=
    match l with
    | nil => ret nil
    | x::xs =>
      do r <- f x;
      do rs <- traverselist f xs;
      ret (r::rs)
    end.

  Fixpoint collectlist {A : Type} (f : A -> mon unit) (l : list A) {struct l} : mon unit :=
    match l with
    | nil => ret tt
    | x::xs => do _ <- f x; collectlist f xs
    end.

  Definition mfold_left {A B} (f: A -> B -> mon A) (l: list B) (s: mon A): mon A :=
    fold_left (fun a b => do a' <- a; f a' b) l s.

End MonadExtra.

(** A [Params f n] instance forces the setoid rewriting mechanism not to
rewrite in the first [n] arguments of the function [f]. We will declare such
instances for all operational type classes in this development. *)
From Coq Require Export Morphisms RelationClasses.

From Coq Require Setoid.

Global Instance: Params (@Relation_Definitions.equiv) 2 := {}.

Class MRet (M : Type -> Type) := mret: forall {A}, A -> M A.
Global Arguments mret {_ _ _} _ : assert.
Global Instance: Params (@mret) 3 := {}.
Global Hint Mode MRet ! : typeclass_instances.

Class MBind (M : Type -> Type) := mbind : forall {A B}, (A -> M B) -> M A -> M B.
Global Arguments mbind {_ _ _ _} _ !_ / : assert.
Global Instance: Params (@mbind) 4 := {}.
Global Hint Mode MBind ! : typeclass_instances.

Class MJoin (M : Type -> Type) := mjoin: forall {A}, M (M A) -> M A.
Global Arguments mjoin {_ _ _} !_ / : assert.
Global Instance: Params (@mjoin) 3 := {}.
Global Hint Mode MJoin ! : typeclass_instances.

Class FMap (M : Type -> Type) := fmap : forall {A B}, (A -> B) -> M A -> M B.
Global Arguments fmap {_ _ _ _} _ !_ / : assert.
Global Instance: Params (@fmap) 4 := {}.
Global Hint Mode FMap ! : typeclass_instances.

Class OMap (M : Type -> Type) := omap: forall {A B}, (A -> option B) -> M A -> M B.
Global Arguments omap {_ _ _ _} _ !_ / : assert.
Global Instance: Params (@omap) 4 := {}.
Global Hint Mode OMap ! : typeclass_instances.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : vericert_scope.
Notation "( m ≫=.)" := (fun f => mbind f m) (only parsing) : vericert_scope.
Notation "(.≫= f )" := (mbind f) (only parsing) : vericert_scope.
Notation "(≫=)" := (fun m f => mbind f m) (only parsing) : vericert_scope.

Notation "x ← y ; z" := (y ≫= (fun x : _ => z))
  (at level 20, y at level 100, z at level 200, only parsing) : vericert_scope.

Notation "' x ← y ; z" := (y ≫= (fun x : _ => z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : vericert_scope.

Infix "<$>" := fmap (at level 61, left associativity) : vericert_scope.

Notation "x ;; z" := (x ≫= fun _ => z)
  (at level 100, z at level 200, only parsing, right associativity): vericert_scope.
