(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.SetoidDec.

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
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.HashTree.
Require Import vericert.hls.Predicate.

#[local] Open Scope positive.
#[local] Open Scope pred_op.

(*|
Schedule Oracle
===============

This oracle determines if a schedule was valid by performing symbolic execution on the input and
output and showing that these behave the same.  This acts on each basic block separately, as the
rest of the functions should be equivalent.
|*)

Definition reg := positive.

Inductive resource : Set :=
| Reg : reg -> resource
| Pred : reg -> resource
| Mem : resource.

(*|
The following defines quite a few equality comparisons automatically, however, these can be
optimised heavily if written manually, as their proofs are not needed.
|*)

Lemma resource_eq : forall (r1 r2 : resource), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality; apply Pos.eq_dec.
Defined.

Lemma comparison_eq: forall (x y : comparison), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Lemma condition_eq: forall (x y : Op.condition), {x = y} + {x <> y}.
Proof.
  generalize comparison_eq; intro.
  generalize Int.eq_dec; intro.
  generalize Int64.eq_dec; intro.
  decide equality.
Defined.

Lemma addressing_eq : forall (x y : Op.addressing), {x = y} + {x <> y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize AST.ident_eq; intro.
  generalize Z.eq_dec; intro.
  generalize Ptrofs.eq_dec; intro.
  decide equality.
Defined.

Lemma typ_eq : forall (x y : AST.typ), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Lemma operation_eq: forall (x y : Op.operation), {x = y} + {x <> y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Int64.eq_dec; intro.
  generalize Float.eq_dec; intro.
  generalize Float32.eq_dec; intro.
  generalize AST.ident_eq; intro.
  generalize condition_eq; intro.
  generalize addressing_eq; intro.
  generalize typ_eq; intro.
  decide equality.
Defined.

Lemma memory_chunk_eq : forall (x y : AST.memory_chunk), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Lemma list_typ_eq: forall (x y : list AST.typ), {x = y} + {x <> y}.
Proof.
  generalize typ_eq; intro.
  decide equality.
Defined.

Lemma option_typ_eq : forall (x y : option AST.typ), {x = y} + {x <> y}.
Proof.
  generalize typ_eq; intro.
  decide equality.
Defined.

Lemma signature_eq: forall (x y : AST.signature), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Defined.

Lemma list_operation_eq : forall (x y : list Op.operation), {x = y} + {x <> y}.
Proof.
  generalize operation_eq; intro.
  decide equality.
Defined.

Lemma list_reg_eq : forall (x y : list reg), {x = y} + {x <> y}.
Proof.
  generalize Pos.eq_dec; intros.
  decide equality.
Defined.

Lemma sig_eq : forall (x y : AST.signature), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Defined.

Lemma instr_eq: forall (x y : instr), {x = y} + {x <> y}.
Proof.
  generalize Pos.eq_dec; intro.
  generalize typ_eq; intro.
  generalize Int.eq_dec; intro.
  generalize memory_chunk_eq; intro.
  generalize addressing_eq; intro.
  generalize operation_eq; intro.
  generalize condition_eq; intro.
  generalize signature_eq; intro.
  generalize list_operation_eq; intro.
  generalize list_reg_eq; intro.
  generalize AST.ident_eq; intro.
  repeat decide equality.
Defined.

Lemma cf_instr_eq: forall (x y : cf_instr), {x = y} + {x <> y}.
Proof.
  generalize Pos.eq_dec; intro.
  generalize typ_eq; intro.
  generalize Int.eq_dec; intro.
  generalize Int64.eq_dec; intro.
  generalize Float.eq_dec; intro.
  generalize Float32.eq_dec; intro.
  generalize Ptrofs.eq_dec; intro.
  generalize memory_chunk_eq; intro.
  generalize addressing_eq; intro.
  generalize operation_eq; intro.
  generalize condition_eq; intro.
  generalize signature_eq; intro.
  generalize list_operation_eq; intro.
  generalize list_reg_eq; intro.
  generalize AST.ident_eq; intro.
  repeat decide equality.
Defined.

(*|
We then create equality lemmas for a resource and a module to index resources uniquely.  The
indexing is done by setting Mem to 1, whereas all other infinitely many registers will all be
shifted right by 1.  This means that they will never overlap.
|*)

Module R_indexed.
  Definition t := resource.
  Definition index (rs: resource) : positive :=
    match rs with
    | Reg r => xO (xO r)
    | Pred r => xI (xI r)
    | Mem => 1%positive
    end.

  Lemma index_inj:  forall (x y: t), index x = index y -> x = y.
  Proof. destruct x; destruct y; crush. Qed.

  Definition eq := resource_eq.
End R_indexed.

(*|
We can then create expressions that mimic the expressions defined in RTLBlock and RTLPar, which use
expressions instead of registers as their inputs and outputs.  This means that we can accumulate all
the results of the operations as general expressions that will be present in those registers.

- Ebase: the starting value of the register.
- Eop: Some arithmetic operation on a number of registers.
- Eload: A load from a memory location into a register.
- Estore: A store from a register to a memory location.

Then, to make recursion over expressions easier, expression_list is also defined in the datatype, as
that enables mutual recursive definitions over the datatypes.
|*)

Definition unsat p := forall a, sat_predicate p a = false.
Definition sat p := exists a, sat_predicate p a = true.

Inductive expression : Type :=
| Ebase : resource -> expression
| Eop : Op.operation -> expression_list -> expression
| Eload : AST.memory_chunk -> Op.addressing -> expression_list -> expression -> expression
| Estore : expression -> AST.memory_chunk -> Op.addressing -> expression_list -> expression -> expression
| Esetpred : Op.condition -> expression_list -> expression
with expression_list : Type :=
| Enil : expression_list
| Econs : expression -> expression_list -> expression_list
.

(*Inductive pred_expr : Type :=
| PEsingleton : option pred_op -> expression -> pred_expr
| PEcons : option pred_op -> expression -> pred_expr -> pred_expr.*)

Module NonEmpty.

Inductive non_empty (A: Type) :=
| singleton : A -> non_empty A
| cons : A -> non_empty A -> non_empty A
.

Arguments singleton [A].
Arguments cons [A].

Declare Scope non_empty_scope.
Delimit Scope non_empty_scope with non_empty.

Module NonEmptyNotation.
Infix "::|" := cons (at level 60, right associativity) : non_empty_scope.
End NonEmptyNotation.
Import NonEmptyNotation.

#[local] Open Scope non_empty_scope.

Fixpoint map {A B} (f: A -> B) (l: non_empty A): non_empty B :=
  match l with
  | singleton a => singleton (f a)
  | a ::| b => f a ::| map f b
  end.

Fixpoint to_list {A} (l: non_empty A): list A :=
  match l with
  | singleton a => a::nil
  | a ::| b => a :: to_list b
  end.

Fixpoint app {A} (l1 l2: non_empty A) :=
  match l1 with
  | singleton a => a ::| l2
  | a ::| b => a ::| app b l2
  end.

Fixpoint non_empty_prod {A B} (l: non_empty A) (l': non_empty B) :=
  match l with
  | singleton a => map (fun x => (a, x)) l'
  | a ::| b => app (map (fun x => (a, x)) l') (non_empty_prod b l')
  end.

Fixpoint of_list {A} (l: list A): option (non_empty A) :=
  match l with
  | a::b =>
    match of_list b with
    | Some b' => Some (a ::| b')
    | _ => None
    end
  | nil => None
  end.

Inductive In {A: Type} (x: A) : non_empty A -> Prop :=
| In_cons : forall a b, x = a \/ In x b -> In x (a ::| b)
| In_single : In x (singleton x).

End NonEmpty.

Module NE := NonEmpty.
Import NE.NonEmptyNotation.

#[local] Open Scope non_empty_scope.

Definition predicated A := NE.non_empty (pred_op * A).

Definition pred_expr := predicated expression.

(*|
Using IMap we can create a map from resources to any other type, as resources can be uniquely
identified as positive numbers.
|*)

Module Rtree := ITree(R_indexed).

Definition forest : Type := Rtree.t pred_expr.

Definition get_forest v (f: forest) :=
  match Rtree.get v f with
  | None => NE.singleton (T, (Ebase v))
  | Some v' => v'
  end.

Declare Scope forest.

Notation "a # b" := (get_forest b a) (at level 1) : forest.
Notation "a # b <- c" := (Rtree.set b c a) (at level 1, b at next level) : forest.

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

(*|
Finally we want to define the semantics of execution for the expressions with symbolic values, so
the result of executing the expressions will be an expressions.
|*)

Section SEMANTICS.

Context {A : Type}.

Record ctx : Type := mk_ctx {
  ctx_rs: regset;
  ctx_ps: predset;
  ctx_mem: mem;
  ctx_sp: val;
  ctx_ge: Genv.t A unit;
}.

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
with sem_pred : ctx -> expression -> bool -> Prop :=
| Spred:
    forall ctx args c lv v,
    sem_val_list ctx args lv ->
    Op.eval_condition c lv (ctx_mem ctx) = Some v ->
    sem_pred ctx (Esetpred c args) v
| Sbase_pred:
    forall ctx p,
    sem_pred ctx (Ebase (Pred p)) ((ctx_ps ctx) !! p)
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

Inductive sem_pred_expr {B: Type} (sem: ctx -> expression -> B -> Prop):
  ctx -> pred_expr -> B -> Prop :=
| sem_pred_expr_cons_true :
  forall ctx e pr p' v,
    eval_predf (ctx_ps ctx) pr = true ->
    sem ctx e v ->
    sem_pred_expr sem ctx ((pr, e) ::| p') v
| sem_pred_expr_cons_false :
  forall ctx e pr p' v,
    eval_predf (ctx_ps ctx) pr = false ->
    sem_pred_expr sem ctx p' v ->
    sem_pred_expr sem ctx ((pr, e) ::| p') v
| sem_pred_expr_single :
  forall ctx e pr v,
    eval_predf (ctx_ps ctx) pr = true ->
    sem_pred_expr sem ctx (NE.singleton (pr, e)) v
.

Definition collapse_pe (p: pred_expr) : option expression :=
  match p with
  | NE.singleton (T, p) => Some p
  | _ => None
  end.

Inductive sem_predset : ctx -> forest -> predset -> Prop :=
| Spredset:
    forall ctx f rs',
    (forall pe x,
      collapse_pe (f # (Pred x)) = Some pe ->
      sem_pred ctx pe (rs' !! x)) ->
    sem_predset ctx f rs'.

Inductive sem_regset : ctx -> forest -> regset -> Prop :=
| Sregset:
    forall ctx f rs',
    (forall x, sem_pred_expr sem_value ctx (f # (Reg x)) (rs' !! x)) ->
    sem_regset ctx f rs'.

Inductive sem : ctx -> forest -> instr_state -> Prop :=
| Sem:
    forall ctx rs' m' f pr',
    sem_regset ctx f rs' ->
    sem_predset ctx f pr' ->
    sem_pred_expr sem_mem ctx (f # Mem) m' ->
    sem ctx f (mk_instr_state rs' pr' m').

End SEMANTICS.

Fixpoint beq_expression (e1 e2: expression) {struct e1}: bool :=
  match e1, e2 with
  | Ebase r1, Ebase r2 => if resource_eq r1 r2 then true else false
  | Eop op1 el1, Eop op2 el2 =>
    if operation_eq op1 op2 then
    beq_expression_list el1 el2 else false
  | Eload chk1 addr1 el1 e1, Eload chk2 addr2 el2 e2 =>
    if memory_chunk_eq chk1 chk2
    then if addressing_eq addr1 addr2
         then if beq_expression_list el1 el2
              then beq_expression e1 e2 else false else false else false
  | Estore e1 chk1 addr1 el1 m1, Estore e2 chk2 addr2 el2 m2 =>
    if memory_chunk_eq chk1 chk2
    then if addressing_eq addr1 addr2
         then if beq_expression_list el1 el2
              then if beq_expression m1 m2
                   then beq_expression e1 e2 else false else false else false else false
  | Esetpred c1 el1, Esetpred c2 el2 =>
    if condition_eq c1 c2
    then beq_expression_list el1 el2 else false
  | _, _ => false
  end
with beq_expression_list (el1 el2: expression_list) {struct el1} : bool :=
  match el1, el2 with
  | Enil, Enil => true
  | Econs e1 t1, Econs e2 t2 => beq_expression e1 e2 && beq_expression_list t1 t2
  | _, _ => false
  end
.

Scheme expression_ind2 := Induction for expression Sort Prop
  with expression_list_ind2 := Induction for expression_list Sort Prop.

Lemma beq_expression_correct:
  forall e1 e2, beq_expression e1 e2 = true -> e1 = e2.
Proof.
  intro e1;
  apply expression_ind2 with
      (P := fun (e1 : expression) =>
            forall e2, beq_expression e1 e2 = true -> e1 = e2)
      (P0 := fun (e1 : expression_list) =>
             forall e2, beq_expression_list e1 e2 = true -> e1 = e2); simplify;
  try solve [repeat match goal with
                    | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
                    | [ H : context[if ?x then _ else _] |- _ ] => destruct x eqn:?
                    end; subst; f_equal; crush; eauto using Peqb_true_eq].
Qed.

Lemma beq_expression_refl: forall e, beq_expression e e = true.
Proof.
  intros.
  induction e using expression_ind2 with (P0 := fun el => beq_expression_list el el = true);
  crush; repeat (destruct_match; crush); [].
  crush. rewrite IHe. rewrite IHe0. auto.
Qed.

Lemma beq_expression_list_refl: forall e, beq_expression_list e e = true.
Proof. induction e; auto. simplify. rewrite beq_expression_refl. auto. Qed.

Lemma beq_expression_correct2:
  forall e1 e2, beq_expression e1 e2 = false -> e1 <> e2.
Proof.
  induction e1 using expression_ind2
    with (P0 := fun el1 => forall el2, beq_expression_list el1 el2 = false -> el1 <> el2).
  - intros. simplify. repeat (destruct_match; crush).
  - intros. simplify. repeat (destruct_match; crush). subst. apply IHe1 in H.
    unfold not in *. intros. apply H. inv H0. auto.
  - intros. simplify. repeat (destruct_match; crush); subst.
    unfold not in *; intros. inv H0. rewrite beq_expression_refl in H.
    discriminate.
    unfold not in *; intros. inv H. rewrite beq_expression_list_refl in Heqb. discriminate.
  - simplify. repeat (destruct_match; crush); subst;
    unfold not in *; intros.
    inv H0. rewrite beq_expression_refl in H; crush.
    inv H. rewrite beq_expression_refl in Heqb0; crush.
    inv H. rewrite beq_expression_list_refl in Heqb; crush.
  - simplify. repeat (destruct_match; crush); subst.
    unfold not in *; intros. inv H0. rewrite beq_expression_list_refl in H; crush.
  - simplify. repeat (destruct_match; crush); subst.
  - simplify. repeat (destruct_match; crush); subst.
    apply andb_false_iff in H. inv H. unfold not in *; intros.
    inv H. rewrite beq_expression_refl in H0; discriminate.
    unfold not in *; intros. inv H. rewrite beq_expression_list_refl in H0; discriminate.
Qed.

Lemma expression_dec: forall e1 e2: expression, {e1 = e2} + {e1 <> e2}.
Proof.
  intros.
  destruct (beq_expression e1 e2) eqn:?. apply beq_expression_correct in Heqb. auto.
  apply beq_expression_correct2 in Heqb. auto.
Defined.

Module HashExpr <: Hashable.
  Definition t := expression.
  Definition eq_dec := expression_dec.
End HashExpr.

Module HT := HashTree(HashExpr).
Import HT.

Definition combine_option {A} (a b: option A) : option A :=
  match a, b with
  | Some a', _ => Some a'
  | _, Some b' => Some b'
  | _, _ => None
  end.

Fixpoint norm_expression (max: predicate) (pe: pred_expr) (h: hash_tree)
  : (PTree.t pred_op) * hash_tree :=
  match pe with
  | NE.singleton (p, e) =>
    let (p', h') := hash_value max e h in
    (PTree.set p' p (PTree.empty _), h')
  | (p, e) ::| pr =>
    let (p', h') := hash_value max e h in
    let (p'', h'') := norm_expression max pr h' in
    match p'' ! p' with
    | Some pr_op =>
      (PTree.set p' (pr_op ∨ p) p'', h'')
    | None =>
      (PTree.set p' p p'', h'')
    end
  end.

Definition mk_pred_stmnt' pr_op e p_e := (¬ p_e ∨ Pvar (true, e)) ∧ pr_op.

Definition mk_pred_stmnt t := PTree.fold mk_pred_stmnt' t T.

Definition mk_pred_stmnt_l (t: list (predicate * pred_op)) := fold_left (fun x => uncurry (mk_pred_stmnt' x)) t T.

Definition encode_expression max pe h :=
  let (tree, h) := norm_expression max pe h in
  (mk_pred_stmnt tree, h).

(*Fixpoint encode_expression_ne (max: predicate) (pe: pred_expr_ne) (h: hash_tree)
  : (PTree.t pred_op) * hash_tree :=
  match pe with
  | NE.singleton (p, e) =>
    let (p', h') := hash_value max e h in
    (Por (Pnot p) (Pvar p'), h')
  | (p, e) ::| pr =>
    let (p', h') := hash_value max e h in
    let (p'', h'') := encode_expression_ne max pr h' in
    (Pand (Por (Pnot p) (Pvar p')) p'', h'')
  end.*)

Fixpoint max_predicate (p: pred_op) : positive :=
  match p with
  | Pvar (b, p) => p
  | Ptrue => 1
  | Pfalse => 1
  | Pand a b => Pos.max (max_predicate a) (max_predicate b)
  | Por a b => Pos.max (max_predicate a) (max_predicate b)
  end.

Fixpoint max_pred_expr (pe: pred_expr) : positive :=
  match pe with
  | NE.singleton (p, e) => max_predicate p
  | (p, e) ::| pe' => Pos.max (max_predicate p) (max_pred_expr pe')
  end.

Definition empty : forest := Rtree.empty _.

Definition ge_preserved {A B C D: Type} (ge: Genv.t A B) (tge: Genv.t C D) : Prop :=
  (forall sp op vl m, Op.eval_operation ge sp op vl m =
                      Op.eval_operation tge sp op vl m)
  /\ (forall sp addr vl, Op.eval_addressing ge sp addr vl =
                         Op.eval_addressing tge sp addr vl).

Lemma ge_preserved_same:
  forall A B ge, @ge_preserved A B A B ge ge.
Proof. unfold ge_preserved; auto. Qed.
#[local] Hint Resolve ge_preserved_same : core.

Inductive similar {A B} : @ctx A -> @ctx B -> Prop :=
| similar_intro :
    forall rs ps mem sp ge tge,
    ge_preserved ge tge ->
    similar (mk_ctx rs ps mem sp ge) (mk_ctx rs ps mem sp tge).

Lemma unsat_correct1 :
  forall a b c,
    unsat (Pand a b) ->
    sat_predicate a c = true ->
    sat_predicate b c = false.
Proof.
  unfold unsat in *. intros.
  simplify. specialize (H c).
  apply andb_false_iff in H. inv H. rewrite H0 in H1. discriminate.
  auto.
Qed.

Lemma unsat_correct2 :
  forall a b c,
    unsat (Pand a b) ->
    sat_predicate b c = true ->
    sat_predicate a c = false.
Proof.
  unfold unsat in *. intros.
  simplify. specialize (H c).
  apply andb_false_iff in H. inv H. auto. rewrite H0 in H1. discriminate.
Qed.

Lemma unsat_not a: unsat (a ∧ (¬ a)).
Proof.
  unfold unsat; simplify.
  rewrite negate_correct.
  auto with bool.
Qed.

Lemma unsat_commut a b: unsat (a ∧ b) -> unsat (b ∧ a).
Proof. unfold unsat; simplify; eauto with bool. Qed.

Lemma sat_dec a: {sat a} + {unsat a}.
Proof.
  unfold sat, unsat.
  destruct (sat_pred a).
  intros. left. destruct s.
  exists (Sat.interp_alist x). auto.
  intros. tauto.
Qed.

Definition sat_equiv p1 p2 := forall c, sat_predicate p1 c = sat_predicate p2 c.

Lemma equiv_symm : forall a b, sat_equiv a b -> sat_equiv b a.
Proof. crush. Qed.

Lemma equiv_trans : forall a b c, sat_equiv a b -> sat_equiv b c -> sat_equiv a c.
Proof. crush. Qed.

Lemma equiv_refl : forall a, sat_equiv a a.
Proof. crush. Qed.

Instance Equivalence_SAT : Equivalence sat_equiv :=
  { Equivalence_Reflexive := equiv_refl ;
    Equivalence_Symmetric := equiv_symm ;
    Equivalence_Transitive := equiv_trans ;
  }.

Instance Setoid_SAT : Setoid pred_op :=
  { equiv := sat_equiv; }.

Lemma sat_imp_equiv :
  forall a b,
    unsat (a ∧ ¬ b ∨ ¬ a ∧ b) -> sat_equiv a b.
Proof.
  unfold unsat, sat_equiv. intros. specialize (H c); simplify.
  rewrite negate_correct in *.
  destruct (sat_predicate b c) eqn:X;
  destruct (sat_predicate a c) eqn:X2;
  crush.
Qed.

Lemma sat_predicate_and :
  forall a b c,
    sat_predicate (a ∧ b) c = sat_predicate a c && sat_predicate b c.
Proof. crush. Qed.

Lemma sat_predicate_or :
  forall a b c,
    sat_predicate (a ∨ b) c = sat_predicate a c || sat_predicate b c.
Proof. crush. Qed.

Lemma sat_equiv2 :
  forall a b,
    equiv a b -> unsat (a ∧ ¬ b ∨ ¬ a ∧ b).
Proof.
  unfold unsat, equiv; simplify.
  repeat rewrite negate_correct.
  repeat rewrite H.
  rewrite andb_negb_r.
  rewrite andb_negb_l. auto.
Qed.

Lemma sat_equiv3 :
  forall a b,
    unsat (a ∧ ¬ b ∨ b ∧ ¬ a) -> sat_equiv a b.
Proof.
  unfold unsat, sat_equiv. intros. specialize (H c); simplify.
  rewrite negate_correct in *.
  destruct (sat_predicate b c) eqn:X;
  destruct (sat_predicate a c) eqn:X2;
  crush.
Qed.

Lemma sat_equiv4 :
  forall a b,
    a == b -> unsat (a ∧ ¬ b ∨ b ∧ ¬ a).
Proof.
  unfold unsat, equiv; simplify.
  repeat rewrite negate_correct.
  repeat rewrite H.
  rewrite andb_negb_r. auto.
Qed.

Definition equiv_check p1 p2 :=
  match sat_pred_simple (p1 ∧ ¬ p2 ∨ p2 ∧ ¬ p1) with
  | None => true
  | _ => false
  end.

Lemma equiv_check_correct :
  forall p1 p2, equiv_check p1 p2 = true -> equiv p1 p2.
Proof.
  unfold equiv_check. unfold sat_pred_simple. intros.
  destruct_match; try discriminate; [].
  destruct_match. destruct_match. discriminate.
  eapply sat_equiv3; eauto.
Qed.

Lemma equiv_check_correct2 :
  forall p1 p2, equiv p1 p2 -> equiv_check p1 p2 = true.
Proof.
  unfold equiv_check, equiv, sat_pred_simple. intros.
  destruct_match; auto. destruct_match; try discriminate. destruct_match.
  simplify.
  apply sat_equiv4 in H. unfold unsat in H. simplify.
  clear Heqs. rewrite H in e. discriminate.
Qed.

Lemma equiv_check_dec :
  forall p1 p2, equiv_check p1 p2 = true <-> equiv p1 p2.
Proof.
  intros; split; eauto using equiv_check_correct, equiv_check_correct2.
Qed.

Definition beq_pred_expr (bound: nat) (pe1 pe2: pred_expr) : bool :=
  match pe1, pe2 with
  (*| PEsingleton None e1, PEsingleton None e2 => beq_expression e1 e2
  | PEsingleton (Some p1) e1, PEsingleton (Some p2) e2 =>
    if beq_expression e1 e2
    then match sat_pred_simple bound (Por (Pand p1 (Pnot p2)) (Pand p2 (Pnot p1))) with
         | Some None => true
         | _ => false
         end
    else false
  | PEsingleton (Some p) e1, PEsingleton None e2
  | PEsingleton None e1, PEsingleton (Some p) e2 =>
    if beq_expression e1 e2
    then match sat_pred_simple bound (Pnot p) with
         | Some None => true
         | _ => false
         end
    else false*)
  | pe1, pe2 =>
    let max := Pos.max (max_pred_expr pe1) (max_pred_expr pe2) in
    let (p1, h) := encode_expression max pe1 (PTree.empty _) in
    let (p2, h') := encode_expression max pe2 h in
    equiv_check p1 p2
  end.

Definition check := Rtree.beq (beq_pred_expr 10000).

Compute (check (empty # (Reg 2) <-
                ((((Pand (Pvar (true, 4)) (¬ (Pvar (true, 4))))), (Ebase (Reg 9))) ::|
                                                                      (NE.singleton (((Pvar (true, 2))), (Ebase (Reg 3))))))
               (empty # (Reg 2) <- (NE.singleton (((Por (Pvar (true, 2)) (Pand (Pvar (true, 3)) (¬ (Pvar (true, 3)))))),
                                                  (Ebase (Reg 3)))))).

Lemma inj_asgn_eg :
  forall a b,
    (a =? b)%nat = (a =? a)%nat -> a = b.
Proof.
  intros. destruct (Nat.eq_dec a b); subst.
  auto. apply Nat.eqb_neq in n.
  rewrite n in H. rewrite Nat.eqb_refl in H. discriminate.
Qed.

Lemma inj_asgn :
  forall a b, (forall (f: nat -> bool), f a = f b) -> a = b.
Proof. intros. apply inj_asgn_eg. eauto. Qed.

Lemma inj_asgn_false:
  forall n1 n2 , ~ (forall c: nat -> bool, c n1 = negb (c n2)).
Proof.
  unfold not; intros. specialize (H (fun x => true)).
  simplify. discriminate.
Qed.

Lemma negb_inj:
  forall a b,
    negb a = negb b -> a = b.
Proof. destruct a, b; crush. Qed.

Lemma sat_predicate_Pvar_inj :
  forall p1 p2,
    equiv (Pvar p1) (Pvar p2) -> p1 = p2.
Proof.
  unfold equiv. simplify. destruct p1, p2.
  destruct b, b0. assert (p = p0).
  { apply Pos2Nat.inj. eapply inj_asgn. eauto. } solve [subst; auto].
  exfalso; eapply inj_asgn_false; eauto.
  exfalso; eapply inj_asgn_false; eauto.
  assert (p = p0). apply Pos2Nat.inj. eapply inj_asgn. intros. specialize (H f).
  apply negb_inj in H. auto. rewrite H0; auto.
Qed.

Definition ind_preds t :=
  forall e1 e2 p1 p2 c,
    e1 <> e2 ->
    t ! e1 = Some p1 ->
    t ! e2 = Some p2 ->
    sat_predicate p1 c = true ->
    sat_predicate p2 c = false.

Definition ind_preds_l t :=
  forall (e1: predicate) e2 p1 p2 c,
    e1 <> e2 ->
    In (e1, p1) t ->
    In (e2, p2) t ->
    sat_predicate p1 c = true ->
    sat_predicate p2 c = false.

Lemma pred_equivalence_Some :
  forall (ta tb: PTree.t pred_op) e pe pe',
    ta ! e = Some pe ->
    tb ! e = Some pe' ->
    equiv (mk_pred_stmnt ta) (mk_pred_stmnt tb) ->
    equiv pe pe'.
Proof.
  intros * SMEA SMEB EQ.

Lemma pred_equivalence_None :
  forall (ta tb: PTree.t pred_op) e pe,
    equiv (mk_pred_stmnt ta) (mk_pred_stmnt tb) ->
    ta ! e = Some pe ->
    tb ! e = None ->
    equiv pe ⟂.
Admitted.

Lemma pred_equivalence :
  forall (ta tb: PTree.t pred_op) e pe,
    equiv (mk_pred_stmnt ta) (mk_pred_stmnt tb) ->
    ta ! e = Some pe ->
    equiv pe ⟂ \/ (exists pe', tb ! e = Some pe' /\ equiv pe pe').
Proof.
  intros * EQ SME. destruct (tb ! e) eqn:HTB.
  { right. econstructor. split; eauto. eapply pred_equivalence_Some; eauto. }
  { left. eapply pred_equivalence_None; eauto. }
Qed.

Section CORRECT.

  Definition fd := @fundef RTLBlock.bb.
  Definition tfd := @fundef RTLPar.bb.

  Context (ictx: @ctx fd) (octx: @ctx tfd) (HSIM: similar ictx octx).

  Lemma sem_value_mem_det:
    forall e v v' m m',
      (sem_value ictx e v -> sem_value octx e v' -> v = v')
      /\ (sem_mem ictx e m -> sem_mem octx e m' -> m = m').
  Proof using HSIM.
    induction e using expression_ind2
      with (P0 := fun p => forall v v',
                    sem_val_list ictx p v -> sem_val_list octx p v' -> v = v');
    inv HSIM; repeat progress simplify;
    try solve [match goal with
               | H: sem_value _ _ _, H2: sem_value _ _ _ |- _ => inv H; inv H2; auto
               | H: sem_mem _ _ _, H2: sem_mem _ _ _ |- _ => inv H; inv H2; auto
               | H: sem_val_list _ _ _, H2: sem_val_list _ _ _ |- _ => inv H; inv H2; auto
               end].
    - repeat match goal with
             | H: sem_value _ _ _ |- _ => inv H
             | H: sem_val_list {| ctx_ge := ge; |} ?e ?l1,
               H2: sem_val_list {| ctx_ge := tge |} ?e ?l2,
               IH: forall _ _, sem_val_list _ _ _ -> sem_val_list _ _ _ -> _ = _ |- _ =>
               assert (X: l1 = l2) by (apply IH; auto)
             | H: ge_preserved _ _ |- _ => inv H
             end; crush.
    - inv H1. inv H0. simplify.
      assert (lv0 = lv). apply IHe; eauto. subst.
      inv H. rewrite H1 in H13.
      assert (a0 = a1) by crush. subst.
      assert (m'1 = m'0). apply IHe0; eauto. subst.
      crush.
    - inv H0. inv H1. simplify.
      assert (lv = lv0). { apply IHe2; eauto. } subst.
      assert (a1 = a0). { inv H.  rewrite H1 in H12. crush. } subst.
      assert (v0 = v1). { apply IHe1; auto. } subst.
      assert (m'0 = m'1). { apply IHe3; auto. } subst.
      crush.
    - inv H0. inv H1. f_equal. apply IHe; auto.
      apply IHe0; auto.
  Qed.

  Lemma sem_value_det:
    forall e v v',
      sem_value ictx e v -> sem_value octx e v' -> v = v'.
  Proof using HSIM.
    intros. eapply sem_value_mem_det; eauto; apply Mem.empty.
  Qed.

  Lemma sem_mem_det:
    forall e v v',
      sem_mem ictx e v -> sem_mem octx e v' -> v = v'.
  Proof using HSIM.
    intros. eapply sem_value_mem_det; eauto; apply (Vint (Int.repr 0%Z)).
  Qed.

  Lemma sem_val_list_det:
    forall e l l',
      sem_val_list ictx e l -> sem_val_list octx e l' -> l = l'.
  Proof using HSIM.
    induction e; simplify.
    - inv H; inv H0; auto.
    - inv H; inv H0. f_equal. eapply sem_value_det; eauto; try apply Mem.empty.
      apply IHe; eauto.
  Qed.

  Lemma sem_pred_det:
    forall e v v',
      sem_pred ictx e v -> sem_pred octx e v' -> v = v'.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_det; pose proof sem_val_list_det; inv HSIM; simplify.
    inv H2; inv H3; auto. assert (lv = lv0) by (eapply H0; eauto). crush.
  Qed.

  #[local] Opaque PTree.set.

  Lemma check_correct_sem_value:
    forall x x' v v' n,
      beq_pred_expr n x x' = true ->
      sem_pred_expr sem_value ictx x v ->
      sem_pred_expr sem_value octx x' v' ->
      v = v'.
  Proof.
    unfold beq_pred_expr. intros. repeat (destruct_match; try discriminate; []); subst.
    unfold sat_pred_simple in *.
    repeat destruct_match; try discriminate; []; subst.
    assert (X: unsat (Por (Pand p (Pnot p0)) (Pand p0 (Pnot p)))) by eauto.
    pose proof (sat_equiv2 _ _ X).
    destruct x, x'; simplify.
    repeat destruct_match; try discriminate; []. inv Heqp0. inv H0. inv H1.
    inv Heqp

    apply sat_predicate_Pvar_inj in H2; subst.

    assert (e0 = e1) by (eapply hash_present_eq; eauto); subst.
    eauto using sem_value_det.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma check_correct: forall (fa fb : forest) ctx ctx' i,
    similar ctx ctx' ->
    check fa fb = true ->
    @sem fd ctx fa i -> @sem tfd ctx' fb i.
  Proof.
    intros.
    inv H. inv H1. inv H.
  (*unfold check, get_forest; intros;
  pose proof beq_expression_correct;
  match goal with
    [ Hbeq : context[Rtree.beq], y : Rtree.elt |- _ ] =>
    apply (Rtree.beq_sound beq_expression fa fb) with (x := y) in Hbeq
  end;
  repeat destruct_match; crush.
Qed.*)
  Abort.

End CORRECT.

Lemma get_empty:
  forall r, empty#r = Psingle (Ebase r).
Proof.
  intros; unfold get_forest;
  destruct_match; auto; [ ];
  match goal with
    [ H : context[Rtree.get _ empty] |- _ ] => rewrite Rtree.gempty in H
  end; discriminate.
Qed.

Fixpoint beq2 {A B : Type} (beqA : A -> B -> bool) (m1 : PTree.t A) (m2 : PTree.t B) {struct m1} : bool :=
  match m1, m2 with
  | PTree.Leaf, _ => PTree.bempty m2
  | _, PTree.Leaf => PTree.bempty m1
  | PTree.Node l1 o1 r1, PTree.Node l2 o2 r2 =>
    match o1, o2 with
    | None, None => true
    | Some y1, Some y2 => beqA y1 y2
    | _, _ => false
    end
    && beq2 beqA l1 l2 && beq2 beqA r1 r2
  end.

Lemma beq2_correct:
  forall A B beqA m1 m2,
    @beq2 A B beqA m1 m2 = true <->
    (forall (x: PTree.elt),
        match PTree.get x m1, PTree.get x m2 with
        | None, None => True
        | Some y1, Some y2 => beqA y1 y2 = true
        | _, _ => False
        end).
Proof.
  induction m1; intros.
  - simpl. rewrite PTree.bempty_correct. split; intros.
    rewrite PTree.gleaf. rewrite H. auto.
    generalize (H x). rewrite PTree.gleaf. destruct (PTree.get x m2); tauto.
  - destruct m2.
    + unfold beq2. rewrite PTree.bempty_correct. split; intros.
      rewrite H. rewrite PTree.gleaf. auto.
      generalize (H x). rewrite PTree.gleaf.
      destruct (PTree.get x (PTree.Node m1_1 o m1_2)); tauto.
    + simpl. split; intros.
      * destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0).
        rewrite IHm1_1 in H3. rewrite IHm1_2 in H1.
        destruct x; simpl. apply H1. apply H3.
        destruct o; destruct o0; auto || congruence.
      * apply andb_true_intro. split. apply andb_true_intro. split.
        generalize (H xH); simpl. destruct o; destruct o0; tauto.
        apply IHm1_1. intros; apply (H (xO x)).
        apply IHm1_2. intros; apply (H (xI x)).
Qed.

Lemma map1:
  forall w dst dst',
  dst <> dst' ->
  (empty # dst <- w) # dst' = Psingle (Ebase dst').
Proof. intros; unfold get_forest; rewrite Rtree.gso; auto; apply get_empty. Qed.

Lemma genmap1:
  forall (f : forest) w dst dst',
  dst <> dst' ->
  (f # dst <- w) # dst' = f # dst'.
Proof. intros; unfold get_forest; rewrite Rtree.gso; auto. Qed.

Lemma map2:
  forall (v : pred_expr) x rs,
  (rs # x <- v) # x = v.
Proof. intros; unfold get_forest; rewrite Rtree.gss; trivial. Qed.

Lemma tri1:
  forall x y,
  Reg x <> Reg y -> x <> y.
Proof. crush. Qed.
