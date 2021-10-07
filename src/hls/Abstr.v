(*
 * Vericert: Verified high-level synthesis.
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

#[local] Open Scope positive.

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

End NonEmpty.

Module NE := NonEmpty.
Import NE.NonEmptyNotation.

#[local] Open Scope non_empty_scope.

Definition predicated_ne A := NE.non_empty (pred_op * A).

Inductive predicated A :=
| Psingle : A -> predicated A
| Plist : predicated_ne A -> predicated A.

Arguments Psingle [A].
Arguments Plist [A].

Definition pred_expr_ne := predicated_ne expression.
Definition pred_expr := predicated expression.

Inductive predicated_wf A : predicated A -> Prop :=
| Psingle_wf :
  forall a, predicated_wf A (Psingle a)
| Plist_wf :
  forall a b l,
    In a (map fst (NE.to_list l)) ->
    In b (map fst (NE.to_list l)) ->
    a <> b ->
    unsat (Pand a b) ->
    predicated_wf A (Plist l)
.

(*|
Using IMap we can create a map from resources to any other type, as resources can be uniquely
identified as positive numbers.
|*)

Module Rtree := ITree(R_indexed).

Definition forest : Type := Rtree.t pred_expr.

Definition get_forest v (f: forest) :=
  match Rtree.get v f with
  | None => Psingle (Ebase v)
  | Some v' => v'
  end.

Notation "a # b" := (get_forest b a) (at level 1).
Notation "a # b <- c" := (Rtree.set b c a) (at level 1, b at next level).

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
| sem_pred_expr_base :
  forall ctx e v,
    sem ctx e v ->
    sem_pred_expr sem ctx (Psingle e) v
| sem_pred_expr_cons_true :
  forall ctx e pr p' v,
    eval_predf (ctx_ps ctx) pr = true ->
    sem ctx e v ->
    sem_pred_expr sem ctx (Plist ((pr, e) ::| p')) v
| sem_pred_expr_cons_false :
  forall ctx e pr p' v,
    eval_predf (ctx_ps ctx) pr = false ->
    sem_pred_expr sem ctx (Plist p') v ->
    sem_pred_expr sem ctx (Plist ((pr, e) ::| p')) v
| sem_pred_expr_single :
  forall ctx e pr v,
    eval_predf (ctx_ps ctx) pr = true ->
    sem_pred_expr sem ctx (Plist (NE.singleton (pr, e))) v
.

Definition collapse_pe (p: pred_expr) : option expression :=
  match p with
  | Psingle p => Some p
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
  with expression_list_ind2 := Induction for expression_list Sort Prop
.

Lemma beq_expression_correct:
  forall e1 e2, beq_expression e1 e2 = true -> e1 = e2.
Proof.
  intro e1;
  apply expression_ind2 with
      (P := fun (e1 : expression) =>
            forall e2, beq_expression e1 e2 = true -> e1 = e2)
      (P0 := fun (e1 : expression_list) =>
             forall e2, beq_expression_list e1 e2 = true -> e1 = e2);
  try solve [repeat match goal with
                    | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
                    | [ H : context[if ?x then _ else _] |- _ ] => destruct x eqn:?
                    end; subst; f_equal; crush; eauto using Peqb_true_eq].
  destruct e2; try discriminate. eauto.
Abort.

Definition hash_tree := PTree.t expression.

Definition find_tree (el: expression) (h: hash_tree) : option positive :=
  match filter (fun x => beq_expression el (snd x)) (PTree.elements h) with
  | (p, _) :: nil => Some p
  | _ => None
  end.

Definition combine_option {A} (a b: option A) : option A :=
  match a, b with
  | Some a', _ => Some a'
  | _, Some b' => Some b'
  | _, _ => None
  end.

Definition max_key {A} (t: PTree.t A) :=
  fold_right Pos.max 1%positive (map fst (PTree.elements t)).

Definition hash_expr (max: predicate) (e: expression) (h: hash_tree): predicate * hash_tree :=
  match find_tree e h with
  | Some p => (p, h)
  | None =>
    let nkey := Pos.max max (max_key h) + 1 in
    (nkey, PTree.set nkey e h)
  end.

Fixpoint encode_expression_ne (max: predicate) (pe: pred_expr_ne) (h: hash_tree): pred_op * hash_tree :=
  match pe with
  | NE.singleton (p, e) =>
    let (p', h') := hash_expr max e h in
    (Por (Pnot p) (Pvar p'), h')
  | (p, e) ::| pr =>
    let (p', h') := hash_expr max e h in
    let (p'', h'') := encode_expression_ne max pr h' in
    (Pand (Por (Pnot p) (Pvar p')) p'', h'')
  end.

Fixpoint encode_expression (max: predicate) (pe: pred_expr) (h: hash_tree): pred_op * hash_tree :=
  match pe with
  | Psingle e =>
    let (p, h') := hash_expr max e h in (Pvar p, h')
  | Plist l => encode_expression_ne max l h
  end.

Fixpoint max_predicate (p: pred_op) : positive :=
  match p with
  | Pvar p => p
  | Pand a b => Pos.max (max_predicate a) (max_predicate b)
  | Por a b => Pos.max (max_predicate a) (max_predicate b)
  | Pnot a => max_predicate a
  end.

Fixpoint max_pred_expr_ne (pe: pred_expr_ne) : positive :=
  match pe with
  | NE.singleton (p, e) => max_predicate p
  | (p, e) ::| pe' => Pos.max (max_predicate p) (max_pred_expr_ne pe')
  end.

Fixpoint max_pred_expr (pe: pred_expr) : positive :=
  match pe with
  | Psingle _ => 1
  | Plist l => max_pred_expr_ne l
  end.

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
    match sat_pred_simple bound (Por (Pand p1 (Pnot p2)) (Pand p2 (Pnot p1))) with
    | Some None => true
    | _ => false
    end
  end.

Definition empty : forest := Rtree.empty _.

Definition check := Rtree.beq (beq_pred_expr 10000).

Compute (check (empty # (Reg 2) <-
                (Plist ((((Pand (Pvar 4) (Pnot (Pvar 4)))), (Ebase (Reg 9))) ::|
                        (NE.singleton (((Pvar 2)), (Ebase (Reg 3)))))))
               (empty # (Reg 2) <- (Plist (NE.singleton (((Por (Pvar 2) (Pand (Pvar 3) (Pnot (Pvar 3))))),
                                                (Ebase (Reg 3))))))).

Lemma check_correct: forall (fa fb : forest),
  check fa fb = true -> (forall x, fa # x = fb # x).
Proof.
  (*unfold check, get_forest; intros;
  pose proof beq_expression_correct;
  match goal with
    [ Hbeq : context[Rtree.beq], y : Rtree.elt |- _ ] =>
    apply (Rtree.beq_sound beq_expression fa fb) with (x := y) in Hbeq
  end;
  repeat destruct_match; crush.
Qed.*)
  Abort.

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

Lemma unsat_not a: unsat (Pand a (Pnot a)).
Proof. unfold unsat; simplify; auto with bool. Qed.

Lemma unsat_commut a b: unsat (Pand a b) -> unsat (Pand b a).
Proof. unfold unsat; simplify; eauto with bool. Qed.

Lemma sat_dec a n b: sat_pred n a = Some b -> {sat a} + {unsat a}.
Proof.
  unfold sat, unsat. destruct b.
  intros. left. destruct s.
  exists (Sat.interp_alist x). auto.
  intros. tauto.
Qed.

Lemma sat_equiv :
  forall a b,
  unsat (Por (Pand a (Pnot b)) (Pand (Pnot a) b)) ->
  forall c, sat_predicate a c = sat_predicate b c.
Proof.
  unfold unsat. intros. specialize (H c); simplify.
  destruct (sat_predicate b c) eqn:X;
  destruct (sat_predicate a c) eqn:X2;
  crush.
Qed.
