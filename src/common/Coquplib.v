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

From coqup Require Import Show.

(* Depend on CompCert for the basic library, as they declare and prove some
   useful theorems. *)
From compcert.lib Require Export Coqlib.

Ltac unfold_rec c := unfold c; fold c.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      inversion H;
      match n with S (S (?n')) => subst; try constructor; solve_by_inverts (S n') end
    end
  end.

Ltac solve_by_invert := solve_by_inverts 1.

Ltac invert x := inversion x; subst; clear x.

Ltac clear_obvious :=
  repeat match goal with
         | [ H : ex _ |- _ ] => invert H
         | [ H : ?C _ = ?C _ |- _ ] => invert H
         end.

Ltac simplify := simpl in *; clear_obvious; simpl in *; try discriminate.

(* Definition const (A B : Type) (a : A) (b : B) : A := a.

Definition compose (A B C : Type) (f : B -> C) (g : A -> B) (x : A) : C := f (g x). *)

Module Option.

Definition default {T : Type} (x : T) (u : option T) : T :=
  match u with
  | Some y => y
  | _ => x
  end.

Definition map {S : Type} {T : Type} (f : S -> T) (u : option S) : option T :=
  match u with
  | Some y => Some (f y)
  | _ => None
  end.

Definition liftA2 {T : Type} (f : T -> T -> T) (a : option T) (b : option T) : option T :=
  match a with
  | Some x => map (f x) b
  | _ => None
  end.

Definition bind {A B : Type} (f : option A) (g : A -> option B) : option B :=
  match f with
  | Some a => g a
  | _ => None
  end.

Module Notation.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
End Notation.

End Option.

Parameter debug_print : string -> unit.

Definition debug_show {A B : Type} `{Show A} (a : A) (b : B) : B :=
  let unused := debug_print (show a) in b.

Definition debug_show_msg {A B : Type} `{Show A} (s : string) (a : A) (b : B) : B :=
  let unused := debug_print (s ++ show a) in b.
