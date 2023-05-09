(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021-2023 Yann Herklotz <git@yannherklotz.com>
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

Require Import Coq.Logic.Decidable.
Require Import Coq.Structures.Equalities.

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
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Gible.
Require Import vericert.hls.HashTree.
Require Import vericert.hls.Predicate.
Require Import vericert.common.DecEq.
Require vericert.common.NonEmpty.
Module NE := NonEmpty.
Import NE.NonEmptyNotation.

#[local] Open Scope non_empty_scope.
#[local] Open Scope positive.
#[local] Open Scope pred_op.

(*|
Schedule Oracle
===============

This oracle determines if a schedule was valid by performing symbolic execution
on the input and output and showing that these behave the same.  This acts on
each basic block separately, as the rest of the functions should be equivalent.
|*)

Definition reg := positive.

(*|
Resource
--------

A resource is either a register ``Reg`` or memory ``Mem``.  There used to be two
more, which were predicates ``Pred`` and exits ``Exit``, however, these are not
actively used inside of other expressions, so it was better to factor them out.
They are kept track of in a different forest, because they will be pointing to
different types of operations.  Exits will point to predicated syntactic
control-flow instructions.  Predicates will point to (maybe predicated)
set-predicate operations.
|*)

Variant resource : Set :=
  | Reg : reg -> resource
  | Mem : resource.

(*|
The following defines quite a few equality comparisons automatically, however,
these can be optimised heavily if written manually, as their proofs are not
needed.
|*)

Lemma resource_eq : forall (r1 r2 : resource), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality; apply Pos.eq_dec.
Defined.

(*|
We then create equality lemmas for a resource and a module to index resources
uniquely.  The indexing is done by setting Mem to 1, whereas all other
infinitely many registers will all be shifted right by 1.  This means that they
will never overlap.
|*)

Module R_indexed.
  Definition t := resource.
  Definition index (rs: resource) : positive :=
    match rs with
    | Reg r => (xO r)
    | Mem => 1
    end.

  Lemma index_inj:  forall (x y: t), index x = index y -> x = y.
  Proof. destruct x; destruct y; crush. Qed.

  Definition eq := resource_eq.
End R_indexed.

(*|
We can then create expressions that mimic the expressions defined in RTLBlock
and RTLPar, which use expressions instead of registers as their inputs and
outputs.  This means that we can accumulate all the results of the operations as
general expressions that will be present in those registers.

- Ebase: the starting value of the register.
- Eop: Some arithmetic operation on a number of registers.
- Eload: A load from a memory location into a register.
- Estore: A store from a register to a memory location.

Then, to make recursion over expressions easier, expression_list is also defined
in the datatype, as that enables mutual recursive definitions over the
datatypes.

They used to contain ``Esetpred`` and ``Eexit``, however, it is just simpler to
factor these out because they are not used by other expressions inside of the
tree.
|*)

Inductive expression : Type :=
| Ebase : resource -> expression
| Eop : Op.operation -> expression_list -> expression
| Eload : AST.memory_chunk -> Op.addressing -> expression_list -> expression -> expression
| Estore : expression -> AST.memory_chunk -> Op.addressing -> expression_list -> expression -> expression
with expression_list : Type :=
| Enil : expression_list
| Econs : expression -> expression_list -> expression_list.

Variant exit_expression : Type :=
  | EEbase : exit_expression
  | EEexit : cf_instr -> exit_expression.

Definition pred_op := @Predicate.pred_op positive.
Definition predicate := positive.

Definition predicated A := NE.non_empty (pred_op * A).

Variant pred_expression : Type :=
  | PEbase : positive -> pred_expression
  | PEsetpred : Op.condition -> expression_list -> pred_expression.

Definition pred_expr := predicated expression.
Definition pred_pexpr := @Predicate.pred_op pred_expression.
Definition pred_eexpr := predicated exit_expression.

(*|
Using ``IMap`` we can create a map from resources to any other type, as
resources can be uniquely identified as positive numbers.
|*)

Module RTree := ITree(R_indexed).

Record forest : Type :=
  mk_forest {
    forest_regs : RTree.t pred_expr;
    forest_preds : PTree.t pred_pexpr;
    forest_exit : pred_eexpr
    }.

Parameter print_forest : forest -> unit.

Definition empty : forest :=
  mk_forest (RTree.empty _) (PTree.empty _) (NE.singleton (Ptrue, EEbase)).

Definition get_forest v (f: forest) :=
  match RTree.get v f.(forest_regs) with
  | None => NE.singleton (Ptrue, (Ebase v))
  | Some v' => v'
  end.

Definition set_forest r v (f: forest) :=
  mk_forest (RTree.set r v f.(forest_regs)) f.(forest_preds) f.(forest_exit).

Definition get_forest_p' p (f: PTree.t pred_pexpr) :=
  match PTree.get p f with
  | None => Plit (true, PEbase p)
  | Some v' => v'
  end.

Definition get_forest_p p (f: forest) := get_forest_p' p f.(forest_preds).

Definition set_forest_p p v (f: forest) :=
  mk_forest f.(forest_regs) (PTree.set p v f.(forest_preds)) f.(forest_exit).

Definition set_forest_e e (f: forest) :=
  mk_forest f.(forest_regs) f.(forest_preds) e.

Declare Scope forest.

Notation "a '#r' b" := (get_forest b a) (at level 1) : forest.
Notation "a '#r' b <- c" := (set_forest b c a) (at level 1, b at next level) : forest.
Notation "a '#p' b" := (get_forest_p b a) (at level 1) : forest.
Notation "a '#p' b <- c" := (set_forest_p b c a) (at level 1, b at next level) : forest.
Notation "a '<-e' e" := (set_forest_e e a) (at level 1) : forest.

#[local] Open Scope forest.

Definition maybe {A: Type} (vo: A) (pr: predset) p (v: A) :=
  match p with
  | Some p' => if eval_predf pr p' then v else vo
  | None => v
  end.

Definition get_pr i := match i with mk_instr_state a b c => b end.

Definition get_m i := match i with mk_instr_state a b c => c end.

Definition eval_predf_opt pr p :=
  match p with Some p' => eval_predf pr p' | None => true end.

Lemma get_empty:
  forall r, empty#r r = NE.singleton (Ptrue, Ebase r).
Proof. unfold "#r"; intros. rewrite RTree.gempty. trivial. Qed.

Lemma forest_reg_gso:
  forall (f : forest) w dst dst',
    dst <> dst' ->
    (f #r dst <- w) #r dst' = f #r dst'.
Proof.
  unfold "#r"; intros.
  unfold forest_regs. unfold set_forest.
  rewrite RTree.gso; auto.
Qed.

Lemma forest_reg_pred:
  forall (f : forest) w dst dst',
    (f #r dst <- w) #p dst' = f #p dst'.
Proof. auto. Qed.

Lemma forest_reg_gss:
  forall (f : forest) w dst,
    (f #r dst <- w) #r dst = w.
Proof.
  unfold "#r"; intros.
  unfold forest_regs. unfold set_forest.
  rewrite RTree.gss; auto.
Qed.

Lemma forest_pred_gso:
  forall (f : forest) w dst dst',
    dst <> dst' ->
    (f #p dst <- w) #p dst' = f #p dst'.
Proof.
  unfold "#p"; intros.
  unfold forest_preds, set_forest_p, get_forest_p'.
  rewrite PTree.gso; auto.
Qed.

Lemma forest_pred_reg:
  forall (f : forest) w dst dst',
    (f #p dst <- w) #r dst' = f #r dst'.
Proof. auto. Qed.

Lemma forest_pred_gss:
  forall (f : forest) w dst,
    (f #p dst <- w) #p dst = w.
Proof.
  unfold "#p"; intros.
  unfold forest_preds, set_forest_p, get_forest_p'.
  rewrite PTree.gss; auto.
Qed.

Lemma forest_pred_gss2 :
  forall (f : forest) r p,
    (forest_preds (f #p r <- p)) ! r = Some p.
Proof. intros. unfold set_forest_p. simpl. now rewrite PTree.gss. Qed.

Lemma forest_pred_gso2 :
  forall (f : forest) r w p,
    r <> w ->
    (forest_preds (f #p w <- p)) ! r = (forest_preds f) ! r.
Proof. intros. unfold set_forest_p. simpl. now rewrite PTree.gso by auto. Qed.

(*|
Finally we want to define the semantics of execution for the expressions with
symbolic values, so the result of executing the expressions will be an
expressions.
|*)

Section SEMANTICS.

Context {A : Type}.

Record ctx : Type := mk_ctx {
  ctx_is: instr_state;
  ctx_sp: val;
  ctx_ge: Genv.t A unit;
}.

Definition ctx_rs ctx := is_rs (ctx_is ctx).
Definition ctx_ps ctx := is_ps (ctx_is ctx).
Definition ctx_mem ctx := is_mem (ctx_is ctx).

Inductive sem_value : ctx -> expression -> val -> Prop :=
| Sbase_reg:
    forall r ctx,
    sem_value ctx (Ebase (Reg r)) ((ctx_rs ctx) !! r)
| Sop:
    forall ctx op args v lv,
    sem_val_list ctx args lv ->
    Op.eval_operation (ctx_ge ctx) (ctx_sp ctx) op lv (ctx_mem ctx) = Some v ->
    sem_value ctx (Eop op args) v
| Sload :
    forall ctx mexp addr chunk args a v m' lv,
    sem_mem ctx mexp m' ->
    sem_val_list ctx args lv ->
    Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr lv = Some a ->
    Memory.Mem.loadv chunk m' a = Some v ->
    sem_value ctx (Eload chunk addr args mexp) v
with sem_mem : ctx -> expression -> Memory.mem -> Prop :=
| Sstore :
    forall ctx mexp vexp chunk addr args lv v a m' m'',
    sem_mem ctx mexp m' ->
    sem_value ctx vexp v ->
    sem_val_list ctx args lv ->
    Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr lv = Some a ->
    Memory.Mem.storev chunk m' a v = Some m'' ->
    sem_mem ctx (Estore vexp chunk addr args mexp) m''
| Sbase_mem :
    forall ctx,
    sem_mem ctx (Ebase Mem) (ctx_mem ctx)
with sem_val_list : ctx -> expression_list -> list val -> Prop :=
| Snil :
    forall ctx,
    sem_val_list ctx Enil nil
| Scons :
    forall ctx e v l lv,
    sem_value ctx e v ->
    sem_val_list ctx l lv ->
    sem_val_list ctx (Econs e l) (v :: lv)
.

Variant sem_exit : ctx -> exit_expression -> option cf_instr -> Prop :=
| Sexit :
  forall ctx cf,
    sem_exit ctx (EEexit cf) (Some cf)
| Sbase_exit :
  forall ctx,
    sem_exit ctx EEbase None.

(*|
``sem_pred`` is the semantics for evaluating a single predicate expression to a
boolean value, which will later be used to evaluate predicate expressions to
booleans.
|*)

Variant sem_pred : ctx -> pred_expression -> bool -> Prop :=
| Spred:
    forall ctx args c lv v,
    sem_val_list ctx args lv ->
    Op.eval_condition c lv (ctx_mem ctx) = Some v ->
    sem_pred ctx (PEsetpred c args) v
| Sbase_pred:
    forall ctx p,
      sem_pred ctx (PEbase p) ((ctx_ps ctx) !! p).

(*|
I was trying to avoid such rich semantics for pred_pexpr (by not having the type
in the first place), but I think it is needed to model predicates properly.  The
main problem is that these semantics are quite strict, and they state that one
must be able to execute the left and right hand sides of an ``Pand``, for
example, to be able to show that the ``Pand`` itself has a value.  Otherwise it
is not possible to evaluate the ``Pand``.
|*)

Inductive sem_pexpr (c: ctx) : pred_pexpr -> bool -> Prop :=
| sem_pexpr_Ptrue : sem_pexpr c Ptrue true
| sem_pexpr_Pfalse : sem_pexpr c Pfalse false
| sem_pexpr_Plit : forall p (b: bool) bres,
    sem_pred c p (if b then bres else negb bres) ->
    sem_pexpr c (Plit (b, p)) bres
| sem_pexpr_Pand_false : forall p1 p2,
  sem_pexpr c p1 false \/ sem_pexpr c p2 false ->
  sem_pexpr c (Pand p1 p2) false
| sem_pexpr_Pand_true : forall p1 p2,
  sem_pexpr c p1 true ->
  sem_pexpr c p2 true ->
  sem_pexpr c (Pand p1 p2) true
| sem_pexpr_Por_true : forall p1 p2,
  sem_pexpr c p1 true \/ sem_pexpr c p2 true ->
  sem_pexpr c (Por p1 p2) true
| sem_pexpr_Por_false : forall p1 p2,
  sem_pexpr c p1 false ->
  sem_pexpr c p2 false ->
  sem_pexpr c (Por p1 p2) false.

Lemma sem_pexpr_Pand :
  forall ctx p1 p2 a b,
    sem_pexpr ctx p1 a ->
    sem_pexpr ctx p2 b ->
    sem_pexpr ctx (p1 ∧ p2) (a && b).
Proof.
  intros. destruct a; cbn; try destruct b; solve [constructor; auto].
Qed.

Lemma sem_pexpr_Por :
  forall ctx p1 p2 a b,
    sem_pexpr ctx p1 a ->
    sem_pexpr ctx p2 b ->
    sem_pexpr ctx (p1 ∨ p2) (a || b).
Proof.
  intros. destruct a; cbn; try destruct b; try solve [constructor; auto].
Qed.

(*|
``from_pred_op`` translates a ``pred_op`` into a ``pred_pexpr``.  The main
difference between the two is that ``pred_op`` contains register that predicate
registers that speak about the current state of predicates, whereas
``pred_pexpr`` have been expanded into expressions.
|*)

Fixpoint from_pred_op (f: PTree.t pred_pexpr) (p: pred_op): pred_pexpr :=
  match p with
  | Ptrue => Ptrue
  | Pfalse => Pfalse
  | Plit (b, p') => if b then get_forest_p' p' f else negate (get_forest_p' p' f)
  | Pand a b => Pand (from_pred_op f a) (from_pred_op f b)
  | Por a b => Por (from_pred_op f a) (from_pred_op f b)
  end.

Inductive sem_pred_expr {A B: Type} (f: PTree.t pred_pexpr) (sem: ctx -> A -> B -> Prop):
  ctx -> predicated A -> B -> Prop :=
| sem_pred_expr_cons_true :
  forall ctx e pr p' v,
    sem_pexpr ctx (from_pred_op f pr) true ->
    sem ctx e v ->
    sem_pred_expr f sem ctx ((pr, e) ::| p') v
| sem_pred_expr_cons_false :
  forall ctx e pr p' v,
    sem_pexpr ctx (from_pred_op f pr) false ->
    sem_pred_expr f sem ctx p' v ->
    sem_pred_expr f sem ctx ((pr, e) ::| p') v
| sem_pred_expr_single :
  forall ctx e pr v,
    sem_pexpr ctx (from_pred_op f pr) true ->
    sem ctx e v ->
    sem_pred_expr f sem ctx (NE.singleton (pr, e)) v
.

Definition collapse_pe (p: pred_expr) : option expression := (* unused *)
  match p with
  | NE.singleton (APtrue, p) => Some p
  | _ => None
  end.

Inductive sem_predset : ctx -> forest -> predset -> Prop :=
| Spredset:
  forall ctx f rs',
    (forall x, sem_pexpr ctx (f #p x) (rs' !! x)) ->
    sem_predset ctx f rs'.

Inductive sem_regset : ctx -> forest -> regset -> Prop :=
| Sregset:
  forall ctx f rs',
    (forall x, sem_pred_expr f.(forest_preds) sem_value ctx (f #r (Reg x)) (rs' !! x)) ->
    sem_regset ctx f rs'.

(*|
Talking about the actual generation of the forest, to make this work one has to
be able to make the assumption that ``forall i, eval (f #p i) = eval (f' #p
i)``, which should then allow for the equivalences of registers and expressions.
|*)

Inductive sem : ctx -> forest -> instr_state * option cf_instr -> Prop :=
| Sem:
    forall ctx rs' m' f pr' cf,
    sem_regset ctx f rs' ->
    sem_predset ctx f pr' ->
    sem_pred_expr f.(forest_preds) sem_mem ctx (f #r Mem) m' ->
    sem_pred_expr f.(forest_preds) sem_exit ctx f.(forest_exit) cf ->
    sem ctx f (mk_instr_state rs' pr' m', cf).

End SEMANTICS.
