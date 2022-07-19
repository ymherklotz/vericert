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

Declare Scope monad_scope.

Module Type Monad.

  Parameter mon : Type -> Type.

  Parameter ret : forall (A : Type) (x : A), mon A.
  Arguments ret [A].

  Parameter bind : forall (A B : Type) (f : mon A) (g : A -> mon B), mon B.
  Arguments bind [A B].

  Parameter bind2 : forall (A B C: Type) (f: mon (A * B)) (g: A -> B -> mon C), mon C.
  Arguments bind2 [A B C].

End Monad.

Module MonadExtra(M : Monad).
  Import M.

  Module Import MonadNotation.

    Notation "'do' X <- A ; B" :=
      (bind A (fun X => B))
        (at level 200, X name, A at level 100, B at level 200) : monad_scope.
    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 A (fun X Y => B))
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

End MonadExtra.
