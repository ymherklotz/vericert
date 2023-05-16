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

Require Coq.Program.Basics.

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
Require Import vericert.hls.GiblePargenproofEquiv.

Import NE.NonEmptyNotation.

Import ListNotations.

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
  : list pred_expr :=
  match l with
  | nil => nil
  | i :: l => (f #r (Reg i)) :: (list_translation l f)
  end.

Fixpoint replicate {A} (n: nat) (l: A) :=
  match n with
  | O => nil
  | S n => l :: replicate n l
  end.

Definition predicated_prod {A B: Type} (p1: predicated A) (p2: predicated B) :=
  NE.map (fun x => match x with ((a, b), (c, d)) => (Pand a c, (b, d)) end)
         (NE.non_empty_prod p1 p2).

Definition predicated_map {A B: Type} (f: A -> B) (p: predicated A)
  : predicated B := NE.map (fun x => (fst x, f (snd x))) p.

Lemma NEin_map :
  forall A B p y (f: A -> B) a,
    NE.In (p, y) (predicated_map f a) ->
    exists x, NE.In (p, x) a /\ y = f x.
Proof.
  induction a; intros.
  - inv H. destruct a. econstructor. split; eauto. constructor.
  - inv H. inv H1. inv H. destruct a. cbn in *. econstructor; econstructor; eauto.
    constructor; tauto.
    specialize (IHa H). inv IHa. inv H0.
    econstructor; econstructor; eauto. constructor; tauto.
Qed.

Lemma NEin_map2 :
  forall A B (f: A -> B) a p y,
    NE.In (p, y) a ->
    NE.In (p, f y) (predicated_map f a).
Proof.
  induction a; crush.
  inv H. constructor.
  inv H. inv H1.
  - constructor; auto.
  - constructor; eauto.
Qed.

Definition cons_pred_expr (pel: pred_expr) (tpel: predicated expression_list) :=
  predicated_map (uncurry Econs) (predicated_prod pel tpel).

Fixpoint merge_old (pel: list pred_expr): predicated expression_list :=
  match pel with
  | nil => NE.singleton (T, Enil)
  | a :: b => cons_pred_expr a (merge_old b)
  end.

Definition merge (pel: list pred_expr): predicated expression_list :=
  match NE.of_list pel with
  | Some npel =>
    NE.fold_right cons_pred_expr (NE.singleton (T, Enil)) npel
  | None => NE.singleton (T, Enil)
  end.

Definition seq_app {A B} (pf: predicated (A -> B)) (pa: predicated A)
  : predicated B :=
  predicated_map (fun x => (fst x) (snd x)) (predicated_prod pf pa).

Definition flap {A B} (pf: predicated (A -> B)) (pa: A)
  : predicated B :=
  NE.map (fun x => (fst x, (snd x) pa)) pf.

Definition flap2 {A B C} (pf: predicated (A -> B -> C)) (pa: A)
           (pb: B): predicated C :=
  NE.map (fun x => (fst x, (snd x) pa pb)) pf.

Definition predicated_of_opt {A: Type} (p: option pred_op) (a: A) :=
  match p with
  | Some p' => NE.singleton (p', a)
  | None => NE.singleton (T, a)
  end.

#[local] Open Scope non_empty_scope.
#[local] Open Scope pred_op.

Definition app_predicated' {A: Type} (a b: predicated A) :=
  let negation := ¬ (NE.fold_left (fun a b => a ∨ (fst b)) b ⟂) in
  NE.app (NE.map (fun x => (negation ∧ fst x, snd x)) a) b.

Definition app_predicated {A: Type} (p': pred_op) (a b: predicated A) :=
  NE.app (NE.map (fun x => (¬ p' ∧ fst x, snd x)) a)
        (NE.map (fun x => (p' ∧ fst x, snd x)) b).

Definition prune_predicated {A: Type} (a: predicated A) :=
  NE.filter (fun x => match deep_simplify peq (fst x) with ⟂ => false | _ => true end)
            (NE.map (fun x => (deep_simplify peq (fst x), snd x)) a).

Definition pred_ret {A: Type} (a: A) : predicated A :=
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

Definition upd_pred_forest (p: pred_op) (f: forest): forest :=
  mk_forest (PTree.map (fun i e =>
               NE.map (fun (x: pred_op * expression) =>
                         let (pred, expr) := x in
                         (Pand p pred, expr)) e) f.(forest_regs))
            f.(forest_preds)
            f.(forest_exit).

Fixpoint from_predicated (b: bool) (f: PTree.t pred_pexpr) (a: predicated pred_expression): pred_pexpr :=
  match a with
  | NE.singleton (p, e) => Pimplies (from_pred_op f p) (Plit (b, e))
  | (p, e) ::| r =>
      Pand (Pimplies (from_pred_op f p) (Plit (b, e)))
           (from_predicated b f r)
  end.

#[local] Open Scope monad_scope.

Definition simpl_combine {A: Type} (a b: option (@Predicate.pred_op A)) :=
  Option.map simplify (combine_pred a b).

Definition dfltp {A} (p: option (@Predicate.pred_op A)) := Option.default T p.

Definition assert_ (b: bool): option unit :=
  if b then Some tt else None.

Definition is_initial_pred_and_notin (f: forest) (p: positive) (p_next: pred_op): bool :=
  match f #p p with
  | Plit (true, PEbase p') =>
    if peq p p'
    then negb (predin peq p p_next)
    else false
  | _ => false
  end.

Definition predicated_not_in {A} (p: Gible.predicate) (l: predicated A): bool :=
  NE.fold_right (fun (a: pred_op * A) (b: bool) =>
    b && negb (predin peq p (fst a))
  ) true l.

Definition predicated_not_in_pred_expr (p: Gible.predicate) (tree: RTree.t pred_expr) :=
  PTree.fold (fun b _ a =>
    b && predicated_not_in p a
  ) tree true.

Definition predicated_not_in_pred_eexpr (p: Gible.predicate) (l: pred_eexpr) :=
  predicated_not_in p l.

Definition predicated_not_in_forest (p: Gible.predicate) (f: forest) :=
  predicated_not_in_pred_expr p f.(forest_regs)
  && predicated_not_in p f.(forest_exit).

Definition update (fop : pred_op * forest) (i : instr): option (pred_op * forest) :=
  let (pred, f) := fop in
  match i with
  | RBnop => Some fop
  | RBop p op rl r =>
      do pruned <-
           prune_predicated
             (app_predicated (dfltp p ∧ pred)
                             (f #r (Reg r))
                             (seq_app (pred_ret (Eop op)) (merge (list_translation rl f))));
      Some (pred, f #r (Reg r) <- pruned)
  | RBload  p chunk addr rl r =>
      do pruned <-
           prune_predicated
             (app_predicated (dfltp p ∧ pred)
                             (f #r (Reg r))
                             (seq_app
                                (seq_app (pred_ret (Eload chunk addr))
                                                (merge (list_translation rl f)))
                                (f #r Mem)));
      Some (pred, f #r (Reg r) <- pruned)
  | RBstore p chunk addr rl r =>
      do pruned <-
           prune_predicated
             (app_predicated (dfltp p ∧ pred)
                             (f #r Mem)
                             (seq_app
                                (seq_app
                                   (flap2 (seq_app (pred_ret Estore)
                                                                      (f #r (Reg r))) chunk addr)
                                   (merge (list_translation rl f))) (f #r Mem)));
      Some (pred, f #r Mem <- pruned)
  | RBsetpred p' c args p =>
      let new_pred :=
        (from_pred_op f.(forest_preds) (dfltp p' ∧ pred)
           → from_predicated true f.(forest_preds) (seq_app (pred_ret (PEsetpred c))
                                                  (merge (list_translation args f))))
        ∧ (from_pred_op f.(forest_preds) (¬ (dfltp p') ∨ ¬ pred) → (f #p p))
      in
      do _ <- assert_ (predicated_not_in_forest p f);
      do _ <- assert_ (is_initial_pred_and_notin f p pred);
      Some (pred, f #p p <- new_pred)
  | RBexit p c =>
      let new_p := simplify (negate (dfltp p) ∧ pred) in
      do pruned <-
           prune_predicated
             (app_predicated (dfltp p ∧ pred) (f.(forest_exit)) (pred_ret (EEexit c)));
      Some (new_p, f <-e pruned)
  end.

Definition remember_expr (f : forest) (lst: list pred_expr) (i : instr): list pred_expr :=
  match i with
  | RBnop => lst
  | RBop p op rl r => (f #r (Reg r)) :: lst
  | RBload  p chunk addr rl r => (f #r (Reg r)) :: lst
  | RBstore p chunk addr rl r => (f #r Mem) :: lst
  | RBsetpred p' c args p => lst
  | RBexit p c => lst
  end.

(*Compute match update (T, mk_forest (PTree.empty _) (PTree.empty _) (NE.singleton (T, EEbase)))
  (RBop None Op.Odiv (1::2::nil) 3) with
  | Some x =>
    match update x (RBop None (Op.Ointconst (Int.repr 10)) nil 3) with
    | Some y =>
      RTree.get (Reg 3) (forest_regs (snd y))
    | None => None
    end
  | None => None
  end.*)

(*|
Implementing which are necessary to show the correctness of the translation
validation by showing that there aren't any more effects in the resultant RTLPar
code than in the RTLBlock code.

Get a sequence from the basic block.
|*)

Definition abstract_sequence (b : list instr) : option forest :=
  Option.map snd (mfold_left update b (Some (Ptrue, empty))).

Compute Option.bind (fun x => RTree.get (Reg 3) (forest_regs x))
  (abstract_sequence
    [RBop None Op.Odiv [1;2] 3;
     RBop None (Op.Ointconst (Int.repr 10)) nil 3]).

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
      (Errors.msg "GiblePargen: Could not prove the blocks equivalent.").

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : GibleSeq.program) : Errors.res GiblePar.program :=
  transform_partial_program transl_fundef p.
