(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2019-2021 Yann Herklotz <yann@yannherklotz.com>
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

Set Implicit Arguments.

Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Require Export compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import vericert.common.Show.

(* Depend on CompCert for the basic library, as they declare and prove some
   useful theorems. *)

Local Open Scope Z_scope.

(* This tactic due to Clement Pit-Claudel with some minor additions by JDP to
   allow the result to be named: https://pit-claudel.fr/clement/MSc/#org96a1b5f *)
Inductive Learnt {A: Type} (a: A) :=
  | AlreadyKnown : Learnt a.

Ltac learn_tac fact name :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] =>
    fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] =>
          fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => let learnt := fresh "Learn" in
              pose proof (AlreadyKnown fact) as learnt; pose proof fact as name
        end
  end.

Tactic Notation "learn" constr(fact) := let name := fresh "H" in learn_tac fact name.
Tactic Notation "learn" constr(fact) "as" simple_intropattern(name) := learn_tac fact name.

Ltac auto_apply fact :=
  let H' := fresh "H" in
  match goal with
  | H : _ |- _ => pose proof H as H'; apply fact in H'
  end.

(** Specialize all hypotheses with a forall to a specific term *)
Tactic Notation "specialize_all" constr(v) :=
  let t := type of v in
  repeat match goal with
         | [H : (forall (x: t), _) |- _ ] => learn H; destruct H with v
         end.

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

(** For a hypothesis of a forall-type, instantiate every variable to a fresh existential *)
Ltac insterU1 H :=
  match type of H with
  | forall x : ?T, _ =>
    let x := fresh "x" in
    evar (x : T);
    let x' := eval unfold x in x in
        clear x; specialize (H x')
  end.

Ltac insterU H :=
  repeat (insterU1 H).

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?x with | _ => _ end ] ] => destruct x eqn:?
  | [ H: context[match ?x with | _ => _ end] |- _ ] => destruct x eqn:?
  end.

Ltac unfold_match H :=
  match type of H with
  | context[match ?g with _ => _ end] => destruct g eqn:?; try discriminate
  end.

Ltac auto_destruct x := destruct x eqn:?; simpl in *; try discriminate; try congruence.

Ltac nicify_hypotheses :=
  repeat match goal with
         | [ H : ex _ |- _ ] => invert H
         | [ H : Some _ = Some _ |- _ ] => invert H
         | [ H : ?x = ?x |- _ ] => clear H
         | [ H : _ /\ _ |- _ ] => invert H
         end.

Ltac nicify_goals :=
  repeat match goal with
         | [ |- _ /\ _ ] => split
         | [ |- Some _ = Some _ ] => f_equal
         | [ |- S _ = S _ ] => f_equal
         end.

Ltac kill_bools :=
  repeat match goal with
         | [ H : _ && _ = true |- _ ] => apply andb_prop in H
         | [ H : _ || _ = false |- _ ] => apply orb_false_elim in H

         | [ H : _ <=? _ = true |- _ ] => apply Z.leb_le in H
         | [ H : _ <=? _ = false |- _ ] => apply Z.leb_gt in H
         | [ H : _ <? _ = true |- _ ] => apply Z.ltb_lt in H
         | [ H : _ <? _ = false |- _ ] => apply Z.ltb_ge in H
         | [ H : _ >=? _ = _ |- _ ] => rewrite Z.geb_leb in H
         | [ H : _ >? _ = _ |- _ ] => rewrite Z.gtb_ltb in H

         | [ H : _ =? _ = true |- _ ] => apply Z.eqb_eq in H
         | [ H : _ =? _ = false |- _ ] => apply Z.eqb_neq in H
         end.

Ltac unfold_constants :=
  repeat match goal with
         | [ |- context[Integers.Ptrofs.modulus] ] =>
           replace Integers.Ptrofs.modulus with 4294967296 by reflexivity
         | [ H : context[Integers.Ptrofs.modulus] |- _ ] =>
           replace Integers.Ptrofs.modulus with 4294967296 in H by reflexivity

         | [ |- context[Integers.Ptrofs.min_signed] ] =>
           replace Integers.Ptrofs.min_signed with (-2147483648) by reflexivity
         | [ H : context[Integers.Ptrofs.min_signed] |- _ ] =>
           replace Integers.Ptrofs.min_signed with (-2147483648) in H by reflexivity

         | [ |- context[Integers.Ptrofs.max_signed] ] =>
           replace Integers.Ptrofs.max_signed with 2147483647 by reflexivity
         | [ H : context[Integers.Ptrofs.max_signed] |- _ ] =>
           replace Integers.Ptrofs.max_signed with 2147483647 in H by reflexivity

         | [ |- context[Integers.Ptrofs.max_unsigned] ] =>
           replace Integers.Ptrofs.max_unsigned with 4294967295 by reflexivity
         | [ H : context[Integers.Ptrofs.max_unsigned] |- _ ] =>
           replace Integers.Ptrofs.max_unsigned with 4294967295 in H by reflexivity

         | [ |- context[Integers.Int.modulus] ] =>
           replace Integers.Int.modulus with 4294967296 by reflexivity
         | [ H : context[Integers.Int.modulus] |- _ ] =>
           replace Integers.Int.modulus with 4294967296 in H by reflexivity

         | [ |- context[Integers.Int.min_signed] ] =>
           replace Integers.Int.min_signed with (-2147483648) by reflexivity
         | [ H : context[Integers.Int.min_signed] |- _ ] =>
           replace Integers.Int.min_signed with (-2147483648) in H by reflexivity

         | [ |- context[Integers.Int.max_signed] ] =>
           replace Integers.Int.max_signed with 2147483647 by reflexivity
         | [ H : context[Integers.Int.max_signed] |- _ ] =>
           replace Integers.Int.max_signed with 2147483647 in H by reflexivity

         | [ |- context[Integers.Int.max_unsigned] ] =>
           replace Integers.Int.max_unsigned with 4294967295 by reflexivity
         | [ H : context[Integers.Int.max_unsigned] |- _ ] =>
           replace Integers.Int.max_unsigned with 4294967295 in H by reflexivity

         | [ |- context[Integers.Ptrofs.unsigned (Integers.Ptrofs.repr ?x) ] ] =>
           match (eval compute in (0 <=? x)) with
           | true => replace (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr x))
                    with x by reflexivity
           | false => idtac
           end
         end.

Ltac substpp :=
  repeat match goal with
         | [ H1 : ?x = Some _, H2 : ?x = Some _ |- _ ] =>
           let EQ := fresh "EQ" in
           learn H1 as EQ; rewrite H2 in EQ; invert EQ
         | _ => idtac
         end.

Ltac simplify := intros; unfold_constants; simpl in *;
                 repeat (nicify_hypotheses; nicify_goals; kill_bools; substpp);
                 simpl in *.

Infix "==nat" := eq_nat_dec (no associativity, at level 50).
Infix "==Z" := Z.eq_dec (no associativity, at level 50).

Ltac liapp :=
  repeat match goal with
         | [ |- (?x | ?y) ] =>
           match (eval compute in (Z.rem y x ==Z 0)) with
           | left _ =>
             let q := (eval compute in (Z.div y x))
             in exists q; reflexivity
           | _ => idtac
          end
         | _ => idtac
         end.

Ltac plia := solve [ unfold Ple in *; lia ].

Ltac xomega := unfold Plt, Ple in *; zify; lia.

Ltac crush := simplify; try discriminate; try congruence; try plia; liapp;
              try assumption; try (solve [auto]).

Ltac crush_trans :=
  match goal with
  | [ H : ?g = ?inter |- ?g = _ ] => transitivity inter; crush
  | [ H : ?inter = ?g |- ?g = _ ] => transitivity inter; crush
  | [ H : ?g = ?inter |- _ = ?g ] => transitivity inter; crush
  | [ H : ?inter = ?g |- _ = ?g ] => transitivity inter; crush
  end.

Ltac maybe t := t + idtac.

Global Opaque Nat.div.
Global Opaque Z.mul.

Inductive Ascending : list positive -> Prop :=
  | Ascending_nil : Ascending nil
  | Ascending_single : forall x, Ascending (x::nil)
  | Ascending_cons : forall x y l, (x < y)%positive -> Ascending (y::l) -> Ascending (x::y::l).

Lemma map_fst_split : forall A B (l : list (A * B)), List.map fst l = fst (List.split l).
Proof.
  induction l; crush.
  destruct a; destruct (split l).
  crush.
Qed.

Lemma Ascending_Forall : forall l x, Ascending (x :: l) -> Forall (fun y => x < y)%positive l.
Proof.
  induction l; crush.
  inv H.
  specialize (IHl _ H4).
  apply Forall_cons.
  - crush.
  - apply Forall_impl with (P:=(fun y : positive => (a < y)%positive)); crush.
Qed.

Lemma Ascending_NoDup : forall l, Ascending l -> NoDup l.
Proof.
  induction 1; simplify.
  - constructor.
  - constructor. crush. constructor.
  - constructor; auto.
    intro contra. inv contra; crush.
    auto_apply Ascending_Forall.
    rewrite Forall_forall in *.
    specialize (H2 x ltac:(auto)).
    lia.
Qed.

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

Definition join {A : Type} (a : option (option A)) : option A :=
  match a with
  | None => None
  | Some a' => a'
  end.

Fixpoint map_option {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | nil => nil
  | x::xs => match f x with
           | None => map_option f xs
           | Some x' => x'::map_option f xs
           end
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
