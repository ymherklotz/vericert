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

From Coq Require Import FSets.FMapPositive.

From coqup Require Import HTL Verilog Coquplib.

From compcert Require Errors.

Definition node : Type := positive.
Definition reg : Type := positive.

Inductive statetrans : Type :=
  | StateGoto (p : node)
  | StateCond (c : expr) (t f : node).

Record state: Type := mkstate {
  st_variables: PositiveMap.t (nat * expr);
  st_stm : PositiveMap.t stmnt;
  st_statetrans : PositiveMap.t statetrans;
}.

Definition init_state : state :=
  mkstate (PositiveMap.empty (nat * expr)) (PositiveMap.empty stmnt) (PositiveMap.empty statetrans).

Inductive res (A: Type) (S: Type): Type :=
  | Error: Errors.errmsg -> res A S
  | OK: A -> S -> res A S.

Arguments OK [A S].
Arguments Error [A S].

Definition mon (A: Type) : Type := res A state.

Definition ret {A: Type} (x: A) (s: state) : mon A := OK x s.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
    match f with
    | Error msg => Error msg
    | OK a s => g a
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Definition bindS {A B: Type} (f: mon A) (g: A -> state -> mon B) : mon B :=
  match f with
  | Error msg => Error msg
  | OK a s => g a s
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bindS A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  match f with
  | OK a s' => OK a s'
  | Error _ => g
  end.

Module PTree.
  Export Maps.PTree.

  Fixpoint xtraverse {A B : Type} (f : positive -> A -> state -> mon B)
           (m : t A) (s : state) (i : positive)
           {struct m} : mon (t B) :=
    match m with
    | Leaf => OK Leaf s
    | Node l o r =>
      let newo :=
          match o with
          | None => OK None s
          | Some x =>
            match f (prev i) x s with
            | Error err => Error err
            | OK val s' => OK (Some val) s'
            end
          end in
      match newo with
      | OK no s =>
        do (nl, s') <- xtraverse f l s (xO i);
        do (nr, s'') <- xtraverse f r s' (xI i);
        OK (Node nl no nr) s''
      | Error msg => Error msg
      end
    end.

  Definition traverse {A B : Type} (f : positive -> A -> state -> mon B) m :=
    xtraverse f m init_state xH.

  Definition traverse1 {A B : Type} (f : A -> state -> mon B) := traverse (fun _ => f).

End PTree.

Definition translate_instr

Definition add_instr (n : node) (n' : node) (s : state) (st : stmnt) : mon node :=
  OK n' (mkstate s.(st_variables)
                 (PositiveMap.add n st s.(st_stm))
                 (PositiveMap.add n (StateGoto n') s.(st_statetrans))).

Definition transf_instr (n : node) (i : instruction) (s : state) : mon node :=
  match i with
  | Hnop n' =>
    add_instr n n' s Skip
  | Hnonblock op args dst n' =>
    add_instr n n' s (Nonblocking (Var dst) )
  | _ => Error (Errors.msg "Hello")
  end.

(** To start out with, the assumption is made that there is only one
    function/module in the original code. *)
Definition transf_function (m: module) : Errors.res verilog :=
  match PTree.traverse transf_instr m.(mod_code) with
  | OK _ s =>
    Errors.OK (Verilog nil)
  | Error err => Errors.Error err
  end.
