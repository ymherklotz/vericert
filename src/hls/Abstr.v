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

Require Import Coq.Logic.Decidable.

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

(** ** Schedule Oracle

This oracle determines if a schedule was valid by performing symbolic execution on the input and
output and showing that these behave the same.  This acts on each basic block separately, as the
rest of the functions should be equivalent.  *)

Definition reg := positive.

Inductive resource : Set :=
| Reg : reg -> resource
| Pred : reg -> resource
| Mem : resource.

(** The following defines quite a few equality comparisons automatically, however, these can be
optimised heavily if written manually, as their proofs are not needed.  *)

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

(** We then create equality lemmas for a resource and a module to index resources uniquely.  The
indexing is done by setting Mem to 1, whereas all other infinitely many registers will all be
shifted right by 1.  This means that they will never overlap.  *)

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

(** We can then create expressions that mimic the expressions defined in RTLBlock and RTLPar, which use
expressions instead of registers as their inputs and outputs.  This means that we can accumulate all
the results of the operations as general expressions that will be present in those registers.

- Ebase: the starting value of the register.
- Eop: Some arithmetic operation on a number of registers.
- Eload: A load from a memory location into a register.
- Estore: A store from a register to a memory location.

Then, to make recursion over expressions easier, expression_list is also defined in the datatype, as
that enables mutual recursive definitions over the datatypes.  *)

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

Fixpoint replace {A} (f: A -> A -> bool) (a b: A) (l: non_empty A) :=
  match l with
  | a' ::| l' => if f a a' then b ::| replace f a b l' else a' ::| replace f a b l'
  | singleton a' => if f a a' then singleton b else singleton a'
  end.

Inductive In {A: Type} (x: A) : non_empty A -> Prop :=
| In_cons : forall a b, x = a \/ In x b -> In x (a ::| b)
| In_single : In x (singleton x).

Lemma in_dec:
  forall A (a: A) (l: non_empty A),
    (forall a b: A, {a = b} + {a <> b}) ->
    {In a l} + {~ In a l}.
Proof.
  induction l; intros.
  { specialize (X a a0). inv X.
    left. constructor.
    right. unfold not. intros. apply H. inv H0. auto. }
  { pose proof X as X2.
    specialize (X a a0). inv X.
    left. constructor; tauto.
    apply IHl in X2. inv X2.
    left. constructor; tauto.
    right. unfold not in *; intros. apply H0. inv H1. now inv H3. }
Qed.

End NonEmpty.

Module NE := NonEmpty.
Import NE.NonEmptyNotation.

#[local] Open Scope non_empty_scope.

Definition predicated A := NE.non_empty (pred_op * A).

Definition pred_expr := predicated expression.

(** Using IMap we can create a map from resources to any other type, as resources can be uniquely
identified as positive numbers.  *)

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

(** Finally we want to define the semantics of execution for the expressions with symbolic values,
so the result of executing the expressions will be an expressions.  *)

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
    sem ctx e v ->
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
    (forall x, sem_pred_expr sem_pred ctx (f # (Pred x)) (rs' !! x)) ->
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
    unfold not in *; intros. inv H0. rewrite beq_expression_refl in H. discriminate.
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

Definition pred_expr_item_eq (pe1 pe2: pred_op * expression) : bool :=
  @equiv_dec _ SATSetoid _ (fst pe1) (fst pe2) && beq_expression (snd pe1) (snd pe2).

Lemma pred_expr_dec: forall (pe1 pe2: pred_op * expression),
    {pred_expr_item_eq pe1 pe2 = true} + {pred_expr_item_eq pe1 pe2 = false}.
Proof.
  intros; destruct (pred_expr_item_eq pe1 pe2) eqn:?; unfold not; [tauto | now right].
Qed.

Lemma pred_expr_dec2: forall (pe1 pe2: pred_op * expression),
    {pred_expr_item_eq pe1 pe2 = true} + {~ pred_expr_item_eq pe1 pe2 = true}.
Proof.
  intros; destruct (pred_expr_item_eq pe1 pe2) eqn:?; unfold not; [tauto | now right].
Qed.

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

Definition mk_pred_stmnt' e p_e := ¬ p_e ∨ Plit (true, e).

Definition mk_pred_stmnt t := PTree.fold (fun x a b => mk_pred_stmnt' a b ∧ x) t T.

Definition mk_pred_stmnt_l (t: list (predicate * pred_op)) := fold_left (fun x a => uncurry mk_pred_stmnt' a ∧ x) t T.

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

Inductive match_states : instr_state -> instr_state -> Prop :=
| match_states_intro:
  forall ps ps' rs rs' m m',
    (forall x, rs !! x = rs' !! x) ->
    (forall x, ps !! x = ps' !! x) ->
    m = m' ->
    match_states (mk_instr_state rs ps  m) (mk_instr_state rs' ps' m').

Lemma match_states_refl x : match_states x x.
Proof. destruct x; constructor; crush. Qed.

Lemma match_states_commut x y : match_states x y -> match_states y x.
Proof. inversion 1; constructor; crush. Qed.

Lemma match_states_trans x y z :
  match_states x y -> match_states y z -> match_states x z.
Proof. repeat inversion 1; constructor; crush. Qed.

#[global]
Instance match_states_Equivalence : Equivalence match_states :=
  { Equivalence_Reflexive := match_states_refl ;
    Equivalence_Symmetric := match_states_commut ;
    Equivalence_Transitive := match_states_trans ; }.

Inductive similar {A B} : @ctx A -> @ctx B -> Prop :=
| similar_intro :
    forall ist ist' sp ge tge,
    ge_preserved ge tge ->
    match_states ist ist' ->
    similar (mk_ctx ist sp ge) (mk_ctx ist' sp tge).

Definition beq_pred_expr_once (pe1 pe2: pred_expr) : bool :=
  match pe1, pe2 with
  (* PEsingleton None e1, PEsingleton None e2 => beq_expression e1 e2
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

Definition tree_equiv_check_el (np2: PTree.t pred_op) (n: positive) (p: pred_op): bool :=
  match np2 ! n with
  | Some p' => equiv_check p p'
  | None => equiv_check p ⟂
  end.

Definition tree_equiv_check_None_el (np2: PTree.t pred_op) (n: positive) (p: pred_op): bool :=
  match np2 ! n with
  | Some p' => true
  | None => equiv_check p ⟂
  end.

Variant sem_pred_tree {A B: Type} (sem: ctx -> expression -> B -> Prop):
    @ctx A -> PTree.t expression -> PTree.t pred_op -> B -> Prop :=
| sem_pred_tree_intro :
    forall ctx expr e pr v et pt,
      eval_predf (ctx_ps ctx) pr = true ->
      sem ctx expr v ->
      pt ! e = Some pr ->
      et ! e = Some expr ->
      sem_pred_tree sem ctx et pt v.

Variant predicated_mutexcl {A: Type} : predicated A -> Prop :=
| predicated_mutexcl_intros : forall pe,
    (forall x y, NE.In x pe -> NE.In y pe -> x <> y -> fst x ⇒ ¬ fst y) ->
    predicated_mutexcl pe.

Lemma hash_value_in :
  forall max e et h h0,
    hash_value max e et = (h, h0) ->
    h0 ! h = Some e.
Proof.
  intros. unfold hash_value in *. destruct_match;
  match goal with
  | H: (_, _) = (_, _) |- _ => inv H
  end.
  - now apply find_tree_Some in Heqo.
  - apply PTree.gss.
Qed.

Lemma norm_expr_constant :
  forall x m h t h' e p,
    norm_expression m x h = (t, h') ->
    h ! e = Some p ->
    h' ! e = Some p.
Proof. Admitted.

Lemma predicated_cons :
  forall A (a:pred_op * A) x,
    predicated_mutexcl (a ::| x) ->
    predicated_mutexcl x.
Proof.
  intros.
  inv H. constructor; intros.
  apply H0; auto; constructor; tauto.
Qed.

Lemma norm_expr_mutexcl :
  forall m pe h t h' e e' p p',
    norm_expression m pe h = (t, h') ->
    predicated_mutexcl pe ->
    t ! e = Some p ->
    t ! e' = Some p' ->
    e <> e' ->
    p ⇒ ¬ p'.
Proof. Abort.

Lemma norm_expression_sem_pred :
  forall A B sem ctx pe v,
    sem_pred_expr sem ctx pe v ->
    forall pt et et' max,
      predicated_mutexcl pe ->
      max_pred_expr pe <= max ->
      norm_expression max pe et = (pt, et') ->
      @sem_pred_tree A B sem ctx et' pt v.
Proof.
  induction 1; crush; repeat (destruct_match; []); try destruct_match;
  match goal with
  | H: (_, _) = (_, _) |- _ => inv H
  end.
  { econstructor. 3: { apply PTree.gss. }
    2: { eassumption. }
    { unfold eval_predf in *. simplify.  rewrite H. auto with bool. }
    { apply hash_value_in in Heqp. eapply norm_expr_constant in Heqp0; eauto. }
  }
  { econstructor; eauto. apply PTree.gss.
    apply hash_value_in in Heqp.
    eapply norm_expr_constant in Heqp0; eauto.
  }
  { assert (sem_pred_tree sem0 ctx0 et' t v).
    eapply IHsem_pred_expr.
    eapply predicated_cons; eauto.
    instantiate (1 := max). lia.
    eassumption.
    inv H3.
    destruct (Pos.eq_dec e0 h); subst. rewrite H6 in Heqo. simplify.
    econstructor; try apply PTree.gss; eauto.
    unfold eval_predf in *. simplify. auto with bool.
    econstructor; eauto. now rewrite PTree.gso.
  }
  { assert (X: sem_pred_tree sem0 ctx0 et' t v).
    eapply IHsem_pred_expr.
    eapply predicated_cons; eauto.
    instantiate (1 := max). lia.
    eassumption.
    inv X.
    destruct (Pos.eq_dec e0 h); crush.
    econstructor; eauto. now rewrite PTree.gso.
  }
  { econstructor; eauto. apply PTree.gss.
    eapply hash_value_in; eassumption.
  }
Qed.

Lemma norm_expression_sem_pred2 :
  forall A B sem ctx v pt et et',
    @sem_pred_tree A B sem ctx et' pt v ->
    forall pe,
      predicated_mutexcl pe ->
      norm_expression (max_pred_expr pe) pe et = (pt, et') ->
      sem_pred_expr sem ctx pe v.
Proof. Admitted.

Definition beq_pred_expr (pe1 pe2: pred_expr) : bool :=
  let max := Pos.max (max_pred_expr pe1) (max_pred_expr pe2) in
  let (np1, h) := norm_expression max pe1 (PTree.empty _) in
  let (np2, h') := norm_expression max pe2 h in
  forall_ptree (tree_equiv_check_el np2) np1
  && forall_ptree (tree_equiv_check_None_el np1) np2.

Definition check := Rtree.beq beq_pred_expr.

Compute (check (empty # (Reg 2) <-
                ((((Pand (Plit (true, 4)) (¬ (Plit (true, 4))))), (Ebase (Reg 9))) ::|
                                                                      (NE.singleton (((Plit (true, 2))), (Ebase (Reg 3))))))
               (empty # (Reg 2) <- (NE.singleton (((Por (Plit (true, 2)) (Pand (Plit (true, 3)) (¬ (Plit (true, 3)))))),
                                                  (Ebase (Reg 3)))))).

Lemma inj_asgn_eg : forall a b, (a =? b)%nat = (a =? a)%nat -> a = b.
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

Lemma sat_predicate_Plit_inj :
  forall p1 p2,
    Plit p1 == Plit p2 -> p1 = p2.
Proof.
  simplify. destruct p1, p2.
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

(*Lemma pred_equivalence_Some' :
  forall ta tb e pe pe',
    list_norepet (map fst ta) ->
    list_norepet (map fst tb) ->
    In (e, pe) ta ->
    In (e, pe') tb ->
    fold_right (fun p a => mk_pred_stmnt' (fst p) (snd p) ∧ a) T ta ==
    fold_right (fun p a => mk_pred_stmnt' (fst p) (snd p) ∧ a) T tb ->
    pe == pe'.
Proof.
  induction ta as [|hd tl Hta]; try solve [crush].
  - intros * NRP1 NRP2 IN1 IN2 FOLD. inv NRP1. inv IN1.
    simpl in FOLD.

Lemma pred_equivalence_Some :
  forall (ta tb: PTree.t pred_op) e pe pe',
    ta ! e = Some pe ->
    tb ! e = Some pe' ->
    mk_pred_stmnt ta == mk_pred_stmnt tb ->
    pe == pe'.
Proof.
  intros * SMEA SMEB EQ. unfold mk_pred_stmnt in *.
  repeat rewrite PTree.fold_spec in EQ.

Lemma pred_equivalence_None :
  forall (ta tb: PTree.t pred_op) e pe,
    (mk_pred_stmnt ta) == (mk_pred_stmnt tb) ->
    ta ! e = Some pe ->
    tb ! e = None ->
    equiv pe ⟂.
Abort.

Lemma pred_equivalence :
  forall (ta tb: PTree.t pred_op) e pe,
    equiv (mk_pred_stmnt ta) (mk_pred_stmnt tb) ->
    ta ! e = Some pe ->
    equiv pe ⟂ \/ (exists pe', tb ! e = Some pe' /\ equiv pe pe').
Proof.
  intros * EQ SME. destruct (tb ! e) eqn:HTB.
  { right. econstructor. split; eauto. eapply pred_equivalence_Some; eauto. }
  { left. eapply pred_equivalence_None; eauto. }
Qed.*)

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
    inv HSIM; match goal with H: context [match_states] |- _ => inv H end; repeat progress simplify;
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
             | |- context [ctx_rs] => unfold ctx_rs; cbn
             | H: context [ctx_mem] |- _ => unfold ctx_mem in H; cbn
             end; crush.
    - repeat match goal with H: sem_value _ _ _ |- _ => inv H end; simplify;
      assert (lv0 = lv) by (apply IHe; eauto); subst;
      match goal with H: ge_preserved _ _ |- _ => inv H end;
      match goal with H: context [Op.eval_addressing _ _ _ _ = Op.eval_addressing _ _ _ _] |- _
                      => rewrite H in * end;
      assert (a0 = a1) by crush;
      assert (m'2 = m'1) by (apply IHe0; eauto); crush.
    - inv H0; inv H3. simplify.
      assert (lv = lv0) by ( apply IHe2; eauto). subst.
      assert (a1 = a0). { inv H. rewrite H3 in *. crush. }
      assert (v0 = v1). { apply IHe1; auto. }
      assert (m'1 = m'2). { apply IHe3; auto. } crush.
    - inv H0. inv H3. f_equal. apply IHe; auto.
      apply IHe0; auto.
  Qed.

  Lemma sem_value_mem_corr:
    forall e v m,
      (sem_value ictx e v -> sem_value octx e v)
      /\ (sem_mem ictx e m -> sem_mem octx e m).
  Proof using HSIM.
    induction e using expression_ind2
      with (P0 := fun p => forall v,
                    sem_val_list ictx p v -> sem_val_list octx p v);
    inv HSIM; match goal with H: context [match_states] |- _ => inv H end; repeat progress simplify.
    - inv H0. unfold ctx_rs, ctx_ps, ctx_mem in *; cbn. rewrite H1. constructor.
    - inv H0. unfold ctx_rs, ctx_ps, ctx_mem in *; cbn. constructor.
    - inv H0. apply IHe in H6. econstructor; try eassumption.
      unfold ctx_rs, ctx_ps, ctx_mem in *; cbn in *. inv H. crush.
    - inv H0.
    - inv H0. eapply IHe in H10. eapply IHe0 in H8; auto.
      econstructor; try eassumption.
      unfold ctx_rs, ctx_ps, ctx_mem in *; cbn in *. inv H; crush.
    - inv H0.
    - inv H0.
    - inv H0. eapply IHe1 in H11; auto. eapply IHe2 in H12; auto. eapply IHe3 in H9; auto.
      econstructor; try eassumption.
      unfold ctx_rs, ctx_ps, ctx_mem in *; cbn in *. inv H; crush.
    - inv H0.
    - inv H0.
    - inv H0. econstructor.
    - inv H0. eapply IHe in H6; auto. eapply IHe0 in H8.
      econstructor; eassumption.
  Qed.

  Lemma sem_value_det:
    forall e v v',
      sem_value ictx e v -> sem_value octx e v' -> v = v'.
  Proof using HSIM.
    intros. eapply sem_value_mem_det; eauto; apply Mem.empty.
  Qed.

  Lemma sem_value_corr:
    forall e v,
      sem_value ictx e v -> sem_value octx e v.
  Proof using HSIM.
    intros. eapply sem_value_mem_corr; eauto; apply Mem.empty.
  Qed.

  Lemma sem_mem_det:
    forall e v v',
      sem_mem ictx e v -> sem_mem octx e v' -> v = v'.
  Proof using HSIM.
    intros. eapply sem_value_mem_det; eauto; apply (Vint (Int.repr 0%Z)).
  Qed.

  Lemma sem_mem_corr:
    forall e v,
      sem_mem ictx e v -> sem_mem octx e v.
  Proof using HSIM.
    intros. eapply sem_value_mem_corr; eauto; apply (Vint (Int.repr 0%Z)).
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

  Lemma sem_val_list_corr:
    forall e l,
      sem_val_list ictx e l -> sem_val_list octx e l.
  Proof using HSIM.
    induction e; simplify.
    - inv H; constructor.
    - inv H. apply sem_value_corr in H3; auto; try apply Mem.empty;
      apply IHe in H5; constructor; assumption.
  Qed.

  Lemma sem_pred_det:
    forall e v v',
      sem_pred ictx e v -> sem_pred octx e v' -> v = v'.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_det; pose proof sem_val_list_det; inv HSIM;
      match goal with H: match_states _ _ |- _ => inv H end; simplify.
    inv H2; inv H5; auto. assert (lv = lv0) by (eapply H0; eauto). subst. unfold ctx_mem in *.
    crush.
  Qed.

  Lemma sem_pred_corr:
    forall e v,
      sem_pred ictx e v -> sem_pred octx e v.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_corr; pose proof sem_val_list_corr; inv HSIM;
      match goal with H: match_states _ _ |- _ => inv H end; simplify.
    inv H2; auto. apply H0 in H5. econstructor; eauto.
    unfold ctx_ps; cbn. rewrite H4. constructor.
  Qed.

  #[local] Opaque PTree.set.

  Lemma exists_norm_expr :
    forall x pe expr m t h h',
      NE.In (pe, expr) x ->
      norm_expression m x h = (t, h') ->
      exists e pe', t ! e = Some pe' /\ pe ⇒ pe' /\ h' ! e = Some expr.
  Proof. Admitted.

(*  Lemma exists_norm_expr3 :
    forall e x pe expr m t h h',
      t ! e = None ->
      norm_expression m x h = (t, h') ->
      ~ NE.In (pe, expr) x.
  Proof.
    Abort.*)

  Lemma norm_expr_implies :
    forall x m h t h' e expr p,
      norm_expression m x h = (t, h') ->
      h' ! e = Some expr ->
      t ! e = Some p ->
      exists p', NE.In (p', expr) x /\ p' ⇒ p.
  Proof. Admitted.

  Lemma norm_expr_In :
    forall A B sem ctx x pe expr v,
      @sem_pred_expr A B sem ctx x v ->
      NE.In (pe, expr) x ->
      eval_predf (ctx_ps ctx) pe = true ->
      sem ctx expr v.
  Proof. Admitted.

  Lemma norm_expr_forall_impl :
    forall m x h t h' e1 e2 p1 p2,
      predicated_mutexcl x ->
      norm_expression m x h = (t, h') ->
      t ! e1 = Some p1 -> t ! e2 = Some p2 -> e1 <> e2 ->
      p1 ⇒ ¬ p2.
    Admitted.

    Lemma norm_expr_replace :
    forall A B sem ctx x pe expr v,
      @sem_pred_expr A B sem ctx x v ->
      eval_predf (ctx_ps ctx) pe = false ->
      @sem_pred_expr A B sem ctx (NE.replace pred_expr_item_eq (pe, expr) (⟂, expr) x) v.
  Proof using.
    induction x; simplify; destruct_match; auto; destruct a;
      unfold pred_expr_item_eq in Heqb; simplify;
      try (destruct (equiv_dec pe p) eqn:?; [|discriminate]; []).
      - rewrite e0 in H0; inv H; crush.
      - apply beq_expression_correct in H2; subst;
          pose proof H0; rewrite e0 in H2;
            apply sem_pred_expr_cons_false; auto; inv H; crush.
      - inv H; constructor; auto; now apply sem_pred_expr_cons_false.
  Qed.

  Section SEM_PRED.

    Context (B: Type).
    Context (isem: @ctx fd -> expression -> B -> Prop).
    Context (osem: @ctx tfd -> expression -> B -> Prop).
    Context (SEMSIM: forall e v v', isem ictx e v -> osem octx e v' -> v = v').

    Ltac simplify' l := intros; unfold_constants; cbn -[l] in *;
                        repeat (nicify_hypotheses; nicify_goals; kill_bools; substpp);
                        cbn -[l] in *.

    Lemma check_correct_sem_value:
      forall x x' v v' t t' h h',
        beq_pred_expr x x' = true ->
        predicated_mutexcl x -> predicated_mutexcl x' ->
        norm_expression (Pos.max (max_pred_expr x) (max_pred_expr x')) x (PTree.empty _) = (t, h) ->
        norm_expression (Pos.max (max_pred_expr x) (max_pred_expr x')) x' h = (t', h') ->
        sem_pred_tree isem ictx h t v ->
        sem_pred_tree osem octx h' t' v' ->
        v = v'.
    Proof using HSIM SEMSIM.
      intros. inv H4. inv H5.
      destruct (Pos.eq_dec e e0); subst.
      { eapply norm_expr_constant in H3; [|eassumption].
        assert (expr = expr0) by (setoid_rewrite H3 in H12; crush); subst.
        eapply SEMSIM; eauto. }
      { destruct (t ! e0) eqn:?.
        { assert (p == pr0).
          { unfold beq_pred_expr in H. repeat (destruct_match; []). inv H2.
            rewrite Heqp1 in H3. inv H3.
            simplify.
            eapply forall_ptree_true in H2. 2: { eapply Heqo. }
            unfold tree_equiv_check_el in H2. rewrite H11 in H2.
            now apply equiv_check_correct in H2. }
          pose proof H0. eapply norm_expr_forall_impl in H0; [| | | |eassumption]; try eassumption.
          unfold "⇒" in H0. unfold eval_predf in *. apply H0 in H6.
          rewrite negate_correct in H6. apply negb_true_iff in H6.
          inv HSIM. match goal with H: match_states _ _ |- _ => inv H end.
          unfold ctx_ps, ctx_mem, ctx_rs in *. simplify.
          pose proof eval_predf_pr_equiv pr0 ps ps' H17. unfold eval_predf in *.
          rewrite H5 in H6. crush.
        }
        { unfold beq_pred_expr in H. repeat (destruct_match; []). inv H2.
          rewrite Heqp0 in H3. inv H3. simplify.
          eapply forall_ptree_true in H3. 2: { eapply H11. }
          unfold tree_equiv_check_None_el in H3.
          rewrite Heqo in H3. apply equiv_check_correct in H3. rewrite H3 in H4.
          unfold eval_predf in H4. crush. } }
    Qed.

    Lemma check_correct_sem_value2:
      forall x x' v v',
        beq_pred_expr x x' = true ->
        predicated_mutexcl x ->
        predicated_mutexcl x' ->
        sem_pred_expr isem ictx x v ->
        sem_pred_expr osem octx x' v' ->
        v = v'.
    Proof.
      intros. pose proof H.
      unfold beq_pred_expr in H. intros. repeat (destruct_match; try discriminate; []).
      eapply check_correct_sem_value; try eassumption.
      eapply norm_expression_sem_pred; eauto. lia.
      eapply norm_expression_sem_pred; eauto. lia.
    Qed.

    Lemma check_correct_sem_value3:
      forall x x' v v',
        beq_pred_expr x x' = true ->
        sem_pred_expr isem ictx x v ->
        sem_pred_expr osem octx x' v' ->
        v = v'.
    Proof.
      induction x.
      - intros * BEQ SEM1 SEM2.
        unfold beq_pred_expr in *. intros. repeat (destruct_match; try discriminate; []); subst.
        rename Heqp into HNORM1.
        rename Heqp0 into HNORM2.
        inv SEM1. rename H0 into HEVAL. rename H2 into ISEM.
        pose HNORM1 as X.
        eapply exists_norm_expr in X; [|constructor].
        simplify' norm_expression.
        rename H0 into HT1.
        rename H1 into HH1.
        rename H into HFORALL1.
        rename H2 into HFORALL2.
        destruct (t0 ! x) eqn:DSTR.
(*        { eapply forall_ptree_true in HT1; eauto. unfold tree_equiv_check_el in *. rewrite DSTR in HT1.
          apply equiv_check_dec in HT1.
          eapply exists_norm_expr2 in DSTR; try solve [eapply norm_expr_constant; eassumption | eassumption].
          eapply norm_expr_In in DSTR; try eassumption. eauto.
          inv HSIM; simplify. now setoid_rewrite <- HT1.
        }
        {
          eapply forall_ptree_true in HT1; [|eassumption].
          unfold tree_equiv_check_el in *. rewrite DSTR in HT1. apply equiv_check_dec in HT1.
          now setoid_rewrite HT1 in HEVAL.
        }
      - intros. unfold beq_pred_expr in H. intros. repeat (destruct_match; try discriminate; []); subst.
        destruct a.
        inv H0.
        { pose Heqp as X. eapply exists_norm_expr in X; [|constructor; tauto]. simplify' norm_expression.
          eapply forall_ptree_true in H0; [|eassumption].
          destruct (t0 ! x0) eqn:DSTR.
          {
            unfold tree_equiv_check_el in H0. rewrite DSTR in H0. apply equiv_check_dec in H0.
            eapply exists_norm_expr2 in DSTR; try solve [eapply norm_expr_constant; eassumption | eassumption].
            eapply norm_expr_In in DSTR; try eassumption; eauto.
            rewrite <- H0. inv HSIM; eauto.
          }
          {
            unfold tree_equiv_check_el in *. rewrite DSTR in H0. apply equiv_check_dec in H0.
            now rewrite H0 in H7.
          }
        }
        { (* This is the inductive argument, which says that if the element is in the list, then
        taking it out will result in two equivalent lists, otherwise just taking the current element
        results in equivalent lists. *)
          simplify' norm_expression. eapply exists_norm_expr in Heqp; [|constructor]; eauto.
          simplify' norm_expression.
          eapply forall_ptree_true in H0; [|eassumption].
          unfold tree_equiv_check_el in H0.
          destruct (t0 ! x0) eqn:DSTR.
          {
            apply equiv_check_dec in H0.
            eapply exists_norm_expr2 in DSTR; try solve [eapply norm_expr_constant; eassumption | eassumption].
          }
        }
    Admitted.*) Abort.

  End SEM_PRED.

  Section SEM_PRED_CORR.

    Context (B: Type).
    Context (isem: @ctx fd -> expression -> B -> Prop).
    Context (osem: @ctx tfd -> expression -> B -> Prop).
    Context (SEMCORR: forall e v, isem ictx e v -> osem octx e v).

    Lemma sem_pred_tree_corr:
      forall x x' v t t' h h',
             beq_pred_expr x x' = true ->
             predicated_mutexcl x -> predicated_mutexcl x' ->
             norm_expression (Pos.max (max_pred_expr x) (max_pred_expr x')) x (PTree.empty _) = (t, h) ->
             norm_expression (Pos.max (max_pred_expr x) (max_pred_expr x')) x' h = (t', h') ->
             sem_pred_tree isem ictx h t v ->
             sem_pred_tree osem octx h' t' v.
    Proof using SEMCORR. Admitted.

  End SEM_PRED_CORR.

  Lemma check_correct: forall (fa fb : forest) i i',
      check fa fb = true ->
      sem ictx fa i ->
      sem octx fb i' ->
      match_states i i'.
  Proof using HSIM.
    intros.
    unfold check, get_forest in *; intros;
      pose proof beq_expression_correct.
    pose proof (Rtree.beq_sound beq_pred_expr fa fb H).
    inv H0; inv H1.
    constructor; simplify.
    { admit. }
    { inv H0; inv H4.
      repeat match goal with
             | H: forall _ : reg, _ |- _ => specialize (H x)
             | H: forall _ : Rtree.elt, _ |- _ => specialize (H (Reg x))
             end.
      repeat (destruct_match; try contradiction).
      unfold "#" in *. rewrite Heqo in H0.
      rewrite Heqo0 in H1. admit.
      unfold "#" in H1. rewrite Heqo0 in H1.
      unfold "#" in H0. rewrite Heqo in H0. admit.
    }
Admitted.

  Lemma check_correct2:
    forall (fa fb : forest) i,
      check fa fb = true ->
      sem ictx fa i ->
      exists i', sem octx fb i' /\ match_states i i'.
  Proof. Admitted.

End CORRECT.

Lemma get_empty:
  forall r, empty#r = NE.singleton (T, Ebase r).
Proof.
  intros; unfold get_forest;
  destruct_match; auto; [ ];
  match goal with
    [ H : context[Rtree.get _ empty] |- _ ] => rewrite Rtree.gempty in H
  end; discriminate.
Qed.

Section BOOLEAN_EQUALITY.

  Context {A B: Type}.
  Context (beqA: A -> B -> bool).

  Fixpoint beq2' (m1: PTree.tree' A) (m2: PTree.tree' B) {struct m1} : bool :=
    match m1, m2 with
    | PTree.Node001 r1, PTree.Node001 r2 => beq2' r1 r2
    | PTree.Node010 x1, PTree.Node010 x2 => beqA x1 x2
    | PTree.Node011 x1 r1, PTree.Node011 x2 r2 => beqA x1 x2 && beq2' r1 r2
    | PTree.Node100 l1, PTree.Node100 l2 => beq2' l1 l2
    | PTree.Node101 l1 r1, PTree.Node101 l2 r2 => beq2' l1 l2 && beq2' r1 r2
    | PTree.Node110 l1 x1, PTree.Node110 l2 x2 => beqA x1 x2 && beq2' l1 l2
    | PTree.Node111 l1 x1 r1, PTree.Node111 l2 x2 r2  => beqA x1 x2 && beq2' l1 l2 && beq2' r1 r2
    | _, _ => false
    end.

  Definition beq2 (m1: PTree.t A) (m2 : PTree.t B) : bool :=
    match m1, m2 with
    | PTree.Empty, PTree.Empty => true
    | PTree.Nodes m1', PTree.Nodes m2' => beq2' m1' m2'
    | _, _ => false
    end.

  Let beq2_optA (o1: option A) (o2: option B) : bool :=
    match o1, o2 with
    | None, None => true
    | Some a1, Some a2 => beqA a1 a2
    | _, _ => false
    end.

  Lemma beq_correct_bool:
    forall m1 m2,
      beq2 m1 m2 = true <-> (forall x, beq2_optA (m1 ! x) (m2 ! x) = true).
  Proof.
    Local Transparent PTree.Node.
    assert (beq_NN: forall l1 o1 r1 l2 o2 r2,
               PTree.not_trivially_empty l1 o1 r1 ->
               PTree.not_trivially_empty l2 o2 r2 ->
               beq2 (PTree.Node l1 o1 r1) (PTree.Node l2 o2 r2) =
                 beq2 l1 l2 && beq2_optA o1 o2 && beq2 r1 r2).
    { intros.
      destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction;
        simpl; rewrite ? andb_true_r, ? andb_false_r; auto.
      rewrite andb_comm; auto.
      f_equal; rewrite andb_comm; auto. }
    induction m1 using PTree.tree_ind; [|induction m2 using PTree.tree_ind].
    - intros. simpl; split; intros.
      + destruct m2; try discriminate. simpl; auto.
      + replace m2 with (@PTree.Empty B); auto. apply PTree.extensionality; intros x.
        specialize (H x). destruct (m2 ! x); simpl; easy.
    - split; intros.
      + destruct (PTree.Node l o r); try discriminate. simpl; auto.
      + replace (PTree.Node l o r) with (@PTree.Empty A); auto. apply PTree.extensionality; intros x.
        specialize (H0 x). destruct ((PTree.Node l o r) ! x); simpl in *; easy.
    - rewrite beq_NN by auto. split; intros.
      + InvBooleans. rewrite ! PTree.gNode. destruct x.
        * apply IHm0; auto.
        * apply IHm1; auto.
        * auto.
      + apply andb_true_intro; split; [apply andb_true_intro; split|].
        * apply IHm1. intros. specialize (H1 (xO x)); rewrite ! PTree.gNode in H1; auto.
        * specialize (H1 xH); rewrite ! PTree.gNode in H1; auto.
        * apply IHm0. intros. specialize (H1 (xI x)); rewrite ! PTree.gNode in H1; auto.
  Qed.

  Theorem beq2_correct:
    forall m1 m2,
      beq2 m1 m2 = true <->
        (forall (x: PTree.elt),
            match m1 ! x, m2 ! x with
            | None, None => True
            | Some y1, Some y2 => beqA y1 y2 = true
            | _, _ => False
            end).
  Proof.
    intros. rewrite beq_correct_bool. unfold beq2_optA. split; intros.
    - specialize (H x). destruct (m1 ! x), (m2 ! x); intuition congruence.
    - specialize (H x). destruct (m1 ! x), (m2 ! x); intuition auto.
  Qed.

End BOOLEAN_EQUALITY.

Lemma map1:
  forall w dst dst',
  dst <> dst' ->
  (empty # dst <- w) # dst' = NE.singleton (T, Ebase dst').
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
