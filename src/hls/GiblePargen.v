(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.common.Monad.
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Gible.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.
Require Import vericert.common.DecEq.
Import NE.NonEmptyNotation.

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

Module OptionExtra := MonadExtra(Option).
Import OptionExtra.
Import OptionExtra.MonadNotation.
#[local] Open Scope monad_scope.

(*|
====================
Gible Par Generation
====================

Abstract Computations
=====================

Define the abstract computation using the [update] function, which will set each
register to its symbolic value.  First we need to define a few helper functions
to correctly translate the predicates.
|*)

Fixpoint list_translation (l : list reg) (f : forest) {struct l}
  : list apred_expr :=
  match l with
  | nil => nil
  | i :: l => (f # (Reg i)) :: (list_translation l f)
  end.

Fixpoint replicate {A} (n: nat) (l: A) :=
  match n with
  | O => nil
  | S n => l :: replicate n l
  end.

Definition merge''' {A: Type} (x y: option (@Predicate.pred_op A)) :=
  match x, y with
  | Some p1, Some p2 => Some (Pand p1 p2)
  | Some p, None | None, Some p => Some p
  | None, None => None
  end.

Definition merge'' {A: Type} x :=
  match x with
  | ((a, e), (b, el)) => (@merge''' A a b, Econs e el)
  end.

Definition map_pred_op {A B P: Type} (pf: option (@Predicate.pred_op P) * (A -> B))
           (pa: option (@Predicate.pred_op P) * A): option (@Predicate.pred_op P) * B :=
  match pa, pf with
  | (p, a), (p', f) => (merge''' p p', f a)
  end.

Definition predicated_prod {A B: Type} (p1: apredicated A) (p2: apredicated B) :=
  NE.map (fun x => match x with ((a, b), (c, d)) => (Pand a c, (b, d)) end)
         (NE.non_empty_prod p1 p2).

Definition predicated_map {A B: Type} (f: A -> B) (p: apredicated A)
  : apredicated B := NE.map (fun x => (fst x, f (snd x))) p.

(*map (fun x => (fst x, Econs (snd x) Enil)) pel*)
Definition merge' (pel: apred_expr) (tpel: apredicated expression_list) :=
  predicated_map (uncurry Econs) (predicated_prod pel tpel).

Fixpoint merge (pel: list apred_expr): apredicated expression_list :=
  match pel with
  | nil => NE.singleton (T, Enil)
  | a :: b => merge' a (merge b)
  end.

Definition map_predicated {A B} (pf: apredicated (A -> B)) (pa: apredicated A)
  : apredicated B :=
  predicated_map (fun x => (fst x) (snd x)) (predicated_prod pf pa).

Definition predicated_apply1 {A B} (pf: apredicated (A -> B)) (pa: A)
  : apredicated B :=
  NE.map (fun x => (fst x, (snd x) pa)) pf.

Definition predicated_apply2 {A B C} (pf: apredicated (A -> B -> C)) (pa: A)
           (pb: B): apredicated C :=
  NE.map (fun x => (fst x, (snd x) pa pb)) pf.

Definition predicated_apply3 {A B C D} (pf: apredicated (A -> B -> C -> D))
           (pa: A) (pb: B) (pc: C): apredicated D :=
  NE.map (fun x => (fst x, (snd x) pa pb pc)) pf.

Definition predicated_from_opt {A: Type} (p: option apred_op) (a: A) :=
  match p with
  | Some p' => NE.singleton (p', a)
  | None => NE.singleton (T, a)
  end.

#[local] Open Scope non_empty_scope.
#[local] Open Scope pred_op.

Fixpoint NEfold_left {A B} (f: A -> B -> A) (l: NE.non_empty B) (a: A) : A :=
  match l with
  | NE.singleton a' => f a a'
  | a' ::| b => NEfold_left f b (f a a')
  end.

Fixpoint NEapp {A} (l m: NE.non_empty A) :=
  match l with
  | NE.singleton a => a ::| m
  | a ::| b => a ::| NEapp b m
  end.

Definition app_predicated' {A: Type} (a b: apredicated A) :=
  let negation := ¬ (NEfold_left (fun a b => a ∨ (fst b)) b ⟂) in
  NEapp (NE.map (fun x => (negation ∧ fst x, snd x)) a) b.

Definition app_predicated {A: Type} (p': apred_op) (a b: apredicated A) :=
  NEapp (NE.map (fun x => (¬ p' ∧ fst x, snd x)) a)
        (NE.map (fun x => (p' ∧ fst x, snd x)) b).

Definition prune_predicated {A: Type} (a: apredicated A) :=
  NE.filter (fun x => match deep_simplify expression_dec (fst x) with ⟂ => false | _ => true end)
            (NE.map (fun x => (deep_simplify expression_dec (fst x), snd x)) a).

Definition pred_ret {A: Type} (a: A) : apredicated A :=
  NE.singleton (T, a).

(*|
Update Function
---------------

The ``update`` function will generate a new forest given an existing forest and
a new instruction, so that it can evaluate a symbolic expression by folding over
a list of instructions.  The main problem is that predicates need to be merged
as well, so that:

1. The predicates are *independent*.
2. The expression assigned to the register should still be correct.

This is done by multiplying the predicates together, and assigning the negation
of the expression to the other predicates.
|*)

Definition upd_pred_forest (p: apred_op) (f: forest) :=
  PTree.map (fun i e =>
               NE.map (fun (x: apred_op * expression) =>
                         let (pred, expr) := x in
                         (Pand p pred, expr)) e) f.

Fixpoint apredicated_to_apred_op (b: bool) (a: apredicated expression): apred_op :=
  match a with
  | NE.singleton (p, e) => Pimplies p (Plit (b, e))
  | (p, e) ::| r =>
      Pand (Pimplies p (Plit (true, e))) (apredicated_to_apred_op b r)
  end.

(* Fixpoint get_pred' (f: forest) (ap: pred_op): option apred_op := *)
(*   match ap with *)
(*   | Ptrue => Some Ptrue *)
(*   | Pfalse => Some Pfalse *)
(*   | Plit (a, b) => *)
(*       match f # (Pred b) with *)
(*       | NE.singleton (Ptrue, p) => Some (Plit (a, p)) *)
(*       | _ => None *)
(*       end *)
(*   | Pand a b => match (get_pred' f a), (get_pred' f b) with *)
(*                | Some a', Some b' => Some (Pand a' b') *)
(*                | _, _ => None *)
(*                end *)
(*   | Por a b => match (get_pred' f a), (get_pred' f b) with *)
(*               | Some a', Some b' => Some (Por a' b') *)
(*               | _, _ => None *)
(*               end *)
(*   end. *)

(* Definition get_pred (f: forest) (ap: option pred_op): option apred_op := *)
(*   get_pred' f (Option.default T ap). *)

Fixpoint get_pred' (f: forest) (ap: pred_op): apred_op :=
  match ap with
  | Ptrue => Ptrue
  | Pfalse => Pfalse
  | Plit (a, b) =>
      apredicated_to_apred_op a (f # (Pred b))
  | Pand a b => Pand (get_pred' f a) (get_pred' f b)
  | Por a b => Por (get_pred' f a) (get_pred' f b)
  end.

Definition get_pred (f: forest) (ap: option pred_op): apred_op :=
  get_pred' f (Option.default Ptrue ap).

#[local] Open Scope monad_scope.

Definition simpl_combine {A: Type} (a b: option (@Predicate.pred_op A)) :=
  Option.map simplify (combine_pred a b).

Definition update (fop : option (apred_op * forest)) (i : instr): option (apred_op * forest) :=
  do (pred, f) <- fop;
  match i with
  | RBnop => fop
  | RBop p op rl r =>
      do pruned <-
           prune_predicated
             (app_predicated (get_pred f p ∧ pred)
                             (f # (Reg r))
                             (map_predicated (pred_ret (Eop op)) (merge (list_translation rl f))));
      Some (pred, f # (Reg r) <- pruned)
  | RBload p chunk addr rl r =>
      do pruned <-
           prune_predicated
             (app_predicated (get_pred f p ∧ pred)
                             (f # (Reg r))
                             (map_predicated
                                (map_predicated (pred_ret (Eload chunk addr))
                                                (merge (list_translation rl f)))
                                (f # Mem)));
      Some (pred, f # (Reg r) <- pruned)
  | RBstore p chunk addr rl r =>
      do pruned <-
           prune_predicated
             (app_predicated (get_pred f p ∧ pred)
                             (f # Mem)
                             (map_predicated
                                (map_predicated
                                   (predicated_apply2 (map_predicated (pred_ret Estore)
                                                                      (f # (Reg r))) chunk addr)
                                   (merge (list_translation rl f))) (f # Mem)));
      Some (pred, f # Mem <- pruned)
  | RBsetpred p' c args p =>
      do pruned <-
           prune_predicated
             (app_predicated (get_pred f p' ∧ pred)
                                    (f # (Pred p))
                                    (map_predicated (pred_ret (Esetpred c))
                                                    (merge (list_translation args f))));
      Some (pred, f # (Pred p) <- pruned)
  | RBexit p c =>
      let new_p := simplify (get_pred' f (negate (Option.default T p)) ∧ pred) in
      do pruned <-
           prune_predicated
             (app_predicated (get_pred f p ∧ pred) (f # Exit) (pred_ret (Eexit c)));
      Some (new_p, f # Exit <- pruned)
  end.

(*|
Implementing which are necessary to show the correctness of the translation
validation by showing that there aren't any more effects in the resultant RTLPar
code than in the RTLBlock code.

Get a sequence from the basic block.
|*)

Definition abstract_sequence (b : list instr) : option forest :=
  Option.map snd (fold_left update b (Some (Ptrue, empty))).

(*|
Check equivalence of control flow instructions.  As none of the basic blocks
should have been moved, none of the labels should be different, meaning the
control-flow instructions should match exactly.
|*)

Definition check_control_flow_instr (c1 c2: cf_instr) : bool :=
  if cf_instr_eq c1 c2 then true else false.

(*|
We define the top-level oracle that will check if two basic blocks are
equivalent after a scheduling transformation.
|*)

Definition empty_trees (bb: SeqBB.t) (bbt: ParBB.t) : bool :=
  match bb with
  | nil =>
    match bbt with
    | nil => true
    | _ => false
    end
  | _ => true
  end.

Definition schedule_oracle (bb: SeqBB.t) (bbt: ParBB.t) : bool :=
  match abstract_sequence bb, abstract_sequence (concat (concat bbt)) with
  | Some bb', Some bbt' =>
      check bb' bbt' && empty_trees bb bbt
  | _, _ => false
  end.

Definition check_scheduled_trees := beq2 schedule_oracle.

Ltac solve_scheduled_trees_correct :=
  intros; unfold check_scheduled_trees in *;
  match goal with
  | [ H: context[beq2 _ _ _], x: positive |- _ ] =>
    rewrite beq2_correct in H; specialize (H x)
  end; repeat destruct_match; crush.

Lemma check_scheduled_trees_correct:
  forall f1 f2 x y1,
    check_scheduled_trees f1 f2 = true ->
    PTree.get x f1 = Some y1 ->
    exists y2, PTree.get x f2 = Some y2 /\ schedule_oracle y1 y2 = true.
Proof. solve_scheduled_trees_correct; eexists; crush. Qed.

Lemma check_scheduled_trees_correct2:
  forall f1 f2 x,
    check_scheduled_trees f1 f2 = true ->
    PTree.get x f1 = None ->
    PTree.get x f2 = None.
Proof. solve_scheduled_trees_correct. Qed.

(*|
Top-level Functions
===================
|*)

Parameter schedule : GibleSeq.function -> GiblePar.function.

Definition transl_function (f: GibleSeq.function)
  : Errors.res GiblePar.function :=
  let tfcode := fn_code (schedule f) in
  if check_scheduled_trees f.(GibleSeq.fn_code) tfcode then
    Errors.OK (mkfunction f.(GibleSeq.fn_sig)
                          f.(GibleSeq.fn_params)
                          f.(GibleSeq.fn_stacksize)
                          tfcode
                          f.(GibleSeq.fn_entrypoint))
  else
    Errors.Error
      (Errors.msg "RTLPargen: Could not prove the blocks equivalent.").

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : GibleSeq.program) : Errors.res GiblePar.program :=
  transform_partial_program transl_fundef p.
