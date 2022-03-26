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

(*Set Implicit Arguments.

Require Export compcert.lib.Maps.

Require Import compcert.common.Errors.

Require Import vericert.common.Vericertlib.

Import PTree.

Local Open Scope error_monad_scope.

(*|
Instance of traverse for ``PTree`` and ``Errors``. This should maybe be generalised in the future.
|*)

Module PTree.

Fixpoint xtraverse (A B : Type) (f : positive -> A -> res B) (m : PTree.t A) (i : positive)
         {struct m} : res (PTree.t B) :=
  match m with
  | Leaf => OK Leaf
  | Node l o r =>
    let newo :=
        match o with
        | None => OK None
        | Some x =>
          match f (prev i) x with
          | Error err => Error err
          | OK val => OK (Some val)
          end
        end in
    match newo with
    | OK no =>
      do nl <- xtraverse f l (xO i);
      do nr <- xtraverse f r (xI i);
      OK (Node nl no nr)
    | Error msg => Error msg
    end
  end.

Definition traverse (A B : Type) (f : positive -> A -> res B) m := xtraverse f m xH.

Definition traverse1 (A B : Type) (f : A -> res B) := traverse (fun _ => f).

End PTree.
*)
