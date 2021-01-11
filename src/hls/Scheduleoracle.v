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

Require Import Globalenvs Values Integers Floats.
Require RTLBlock RTLPar Op Memory AST Registers.
Require Import Vericertlib.

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
| Mem : resource.

(*|
The following defines quite a few equality comparisons automatically, however, these can be
optimised heavily if written manually, as their proofs are not needed.
|*)

Lemma resource_eq : forall (r1 r2 : resource), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality. apply Pos.eq_dec.
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

Lemma instruction_eq: forall (x y : RTLBlock.instruction), {x = y} + {x <> y}.
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
  decide equality.
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
    | Reg r => xO r
    | Mem => 1%positive
    end.

  Lemma index_inj:  forall (x y: t), index x = index y -> x = y.
  Proof.
    destruct x; destruct y; intro; try (simpl in H; congruence).
  Qed.

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

Inductive expression : Set :=
| Ebase : resource -> expression
| Eop : Op.operation -> expression_list -> expression
| Eload : AST.memory_chunk -> Op.addressing -> expression_list -> expression -> expression
| Estore : expression -> AST.memory_chunk -> Op.addressing -> expression_list -> expression -> expression
with expression_list : Set :=
| Enil : expression_list
| Econs : expression -> expression_list -> expression_list.

(*|
Using IMap we can create a map from resources to any other type, as resources can be uniquely
identified as positive numbers.
|*)

Module Rmap := Maps.IMap(R_indexed).

Definition forest : Type := Rmap.t expression.

Definition regset := Registers.Regmap.t val.

Notation "a # b" := (Rmap.get b a) (at level 1).
Notation "a # b <- c" := (Rmap.set b c a) (at level 1, b at next level).

Record sem_state := mk_sem_state {
                    sem_state_stackp : val;
                    sem_state_regset : regset;
                    sem_state_memory : Memory.mem
                    }.

(*|
Finally we want to define the semantics of execution for the expressions with symbolic values, so
the result of executing the expressions will be an expressions.
|*)

Section SEMANTICS.

Context (A : Set) (genv : Genv.t A unit).

Inductive sem_value :
      val -> sem_state -> expression -> val -> Prop :=
  | Sbase_reg:
          forall parent st r,
          sem_value parent st (Ebase (Reg r)) (Registers.Regmap.get r (sem_state_regset st))
  | Sop:
          forall parent st op args v lv,
          sem_val_list parent st args lv ->
          Op.eval_operation genv (sem_state_stackp st) op lv (sem_state_memory st) = Some v ->
          sem_value parent st (Eop op args) v
  | Sload :
          forall parent st mem_exp addr chunk args a v m' lv ,
          sem_mem parent st mem_exp m' ->
          sem_val_list parent st args lv ->
          Op.eval_addressing genv (sem_state_stackp st) addr lv = Some a ->
          Memory.Mem.loadv chunk m' a = Some v ->
          sem_value parent st (Eload chunk addr args mem_exp) v
with sem_mem :
           val -> sem_state -> expression -> Memory.mem -> Prop :=
  | Sstore :
          forall parent st mem_exp val_exp m'' addr v a m' chunk args lv,
          sem_mem parent st mem_exp m' ->
          sem_value parent st val_exp v ->
          sem_val_list parent st args lv ->
          Op.eval_addressing genv (sem_state_stackp st) addr lv = Some a ->
          Memory.Mem.storev chunk m' a v = Some m'' ->
          sem_mem parent st (Estore mem_exp chunk addr args val_exp) m''
    | Sbase_mem :
            forall parent st m,
            sem_mem parent st (Ebase Mem) m
with sem_val_list :
           val -> sem_state -> expression_list -> list val -> Prop :=
    | Snil :
            forall parent st,
            sem_val_list parent st Enil nil
    | Scons :
            forall parent st e v l lv,
            sem_value parent st e v ->
            sem_val_list parent st l lv ->
            sem_val_list parent st (Econs e l) (v :: lv).

Inductive sem_regset :
   val -> sem_state -> forest -> regset -> Prop :=
  | Sregset:
        forall parent st f rs',
        (forall x, sem_value parent st (f # (Reg x)) (Registers.Regmap.get x rs')) ->
        sem_regset parent st f rs'.

Inductive sem :
   val -> sem_state -> forest -> sem_state -> Prop :=
  | Sem:
        forall st rs' fr' m' f parent,
        sem_regset parent st f rs' ->
        sem_mem parent st (f # Mem) m' ->
        sem parent st fr' (mk_sem_state (sem_state_stackp st) rs' m').


End SEMANTICS.

Fixpoint beq_expression (e1 e2: expression) {struct e1}: bool :=
  match e1, e2 with
  | Ebase r1, Ebase r2 => if resource_eq r1 r2 then true else false
  | Eop op1 el1, Eop op2 el2 =>
      if operation_eq op1 op2 then beq_expression_list el1 el2 else false
  | Eload chk1 addr1 el1 e1, Eload chk2 addr2 el2 e2 =>
      if memory_chunk_eq chk1 chk2
      then if addressing_eq addr1 addr2
      then if beq_expression_list el1 el2
      then beq_expression e1 e2 else false else false else false
  | Estore m1 chk1 addr1 el1 e1, Estore m2 chk2 addr2 el2 e2=>
      if memory_chunk_eq chk1 chk2
      then if addressing_eq addr1 addr2
      then if beq_expression_list el1 el2
      then if beq_expression m1 m2
      then beq_expression e1 e2 else false else false else false else false
  | _, _ => false
  end
with beq_expression_list (el1 el2: expression_list) {struct el1} : bool :=
  match el1, el2 with
  | Enil, Enil => true
  | Econs e1 t1, Econs e2 t2 => beq_expression e1 e2 && beq_expression_list t1 t2
  | _, _ => false
  end.

Scheme expression_ind2:= Induction for expression Sort Prop
  with expression_list_ind2:= Induction for expression_list Sort Prop.

Lemma beq_expression_correct:
  forall e1 e2, beq_expression e1 e2 = true -> e1 = e2.
Proof.
  intro e1.
  apply expression_ind2 with
      (P := fun (e1: expression) => forall e2, beq_expression e1 e2 = true -> e1 = e2)
      (P0 := fun (e1: expression_list) => forall e2, beq_expression_list e1 e2 = true -> e1 = e2).
  (* Ebase *)
  intros r e2.
  destruct e2; simpl; try congruence.
  case (resource_eq r r0); congruence.

  (* Eop *)
   intros o e HR e2. destruct e2; simpl; try congruence.
   case (operation_eq o o0); intros. generalize (HR _ H).
   congruence. congruence.

   (* Eload *)
   intros m a e HR e3 HR3. destruct e2 ; simpl ; try congruence.
   case (memory_chunk_eq m m0).
   case (addressing_eq a a0).
   caseEq (beq_expression_list e e0).
   caseEq (beq_expression e3 e2).
   intros.
   generalize (HR e0 H0). generalize (HR3 e2 H). intros.
   subst. trivial.
   intros; discriminate.
   intros; discriminate.
   intros; discriminate.
   intros; discriminate.

   (* Estore *)
   intros e3 HR2 m a e HR e4 HR4 e2.
   destruct e2; simpl; try congruence.
   case (memory_chunk_eq m m0). case (addressing_eq a a0).
   (*case (beq_expression_list e e0). case (beq_expression e3 e2). *)
   intros.
   caseEq (beq_expression_list e e0). intro. rewrite H0 in H.
   caseEq (beq_expression e3 e2_1). intro. rewrite H1 in H.
   generalize (HR2 e2_1 H1). intro. generalize (HR e0 H0).
   generalize (HR4 e2_2 H).
   congruence.
   intro. rewrite H1 in H. discriminate.
   intro. rewrite H0 in H. discriminate.
   intros; congruence.
   intros; congruence.

   (* Enil *)
   intro e2.
   unfold beq_expression_list.
   case e2; intros; try congruence; trivial.

   (* Econs *)
   intros e HR1 e0 HR2 e2.
   destruct e2; simpl; try congruence.
   caseEq (beq_expression e e2); caseEq (beq_expression_list e0 e3); simpl; try congruence.
   intros. clear H1. generalize (HR1 e2 H0). generalize (HR2 e3 H).
   congruence.
Qed.

(*|
We define the top-level oracle that will check if two basic blocks are equivalent after a scheduling
transformation.
|*)

Definition schedule_oracle (p : RTLBlock.bblock) (pt : RTLPar.bblock) : bool :=
  true.
