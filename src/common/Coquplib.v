(*
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

From Coq Require Export
     String
     ZArith
     Znumtheory
     List
     Bool.

Ltac unfold_rec c := unfold c; fold c.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      inversion H;
      match n with S (S (?n')) => subst; try constructor; solve_by_inverts (S n') end
    end
  end.

Ltac solve_by_invert := solve_by_inverts 1.
