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
Require compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLBlockInstr.

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
    | Reg r => xO r
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

Module Rtree := ITree(R_indexed).

Definition forest : Type := Rtree.t expression.

Definition regset := Registers.Regmap.t val.

Definition get_forest v f :=
  match Rtree.get v f with
  | None => Ebase v
  | Some v' => v'
  end.

Notation "a # b" := (get_forest b a) (at level 1).
Notation "a # b <- c" := (Rtree.set b c a) (at level 1, b at next level).

Record sem_state := mk_sem_state {
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
          forall sp st r,
          sem_value sp st (Ebase (Reg r)) (Registers.Regmap.get r (sem_state_regset st))
  | Sop:
          forall st op args v lv sp,
          sem_val_list sp st args lv ->
          Op.eval_operation genv sp op lv (sem_state_memory st) = Some v ->
          sem_value sp st (Eop op args) v
  | Sload :
          forall st mem_exp addr chunk args a v m' lv sp,
          sem_mem sp st mem_exp m' ->
          sem_val_list sp st args lv ->
          Op.eval_addressing genv sp addr lv = Some a ->
          Memory.Mem.loadv chunk m' a = Some v ->
          sem_value sp st (Eload chunk addr args mem_exp) v
with sem_mem :
          val -> sem_state -> expression -> Memory.mem -> Prop :=
  | Sstore :
          forall st mem_exp val_exp m'' addr v a m' chunk args lv sp,
          sem_mem sp st mem_exp m' ->
          sem_value sp st val_exp v ->
          sem_val_list sp st args lv ->
          Op.eval_addressing genv sp addr lv = Some a ->
          Memory.Mem.storev chunk m' a v = Some m'' ->
          sem_mem sp st (Estore mem_exp chunk addr args val_exp) m''
    | Sbase_mem :
            forall st m sp,
            sem_mem sp st (Ebase Mem) m
with sem_val_list :
          val -> sem_state -> expression_list -> list val -> Prop :=
    | Snil :
            forall st sp,
            sem_val_list sp st Enil nil
    | Scons :
            forall st e v l lv sp,
            sem_value sp st e v ->
            sem_val_list sp st l lv ->
            sem_val_list sp st (Econs e l) (v :: lv).

Inductive sem_regset :
  val -> sem_state -> forest -> regset -> Prop :=
  | Sregset:
        forall st f rs' sp,
        (forall x, sem_value sp st (f # (Reg x)) (Registers.Regmap.get x rs')) ->
        sem_regset sp st f rs'.

Inductive sem :
  val -> sem_state -> forest -> sem_state -> Prop :=
  | Sem:
        forall st rs' m' f sp,
        sem_regset sp st f rs' ->
        sem_mem sp st (f # Mem) m' ->
        sem sp st f (mk_sem_state rs' m').

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
    repeat match goal with
           | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
           | [ H : context[if ?x then _ else _] |- _ ] => destruct x eqn:?
           end; subst; f_equal; crush.
Qed.

Definition empty : forest := Rtree.empty _.

(*|
This function checks if all the elements in [fa] are in [fb], but not the other way round.
|*)

Definition check := Rtree.beq beq_expression.

Lemma check_correct: forall (fa fb : forest) (x : resource),
  check fa fb = true -> (forall x, fa # x = fb # x).
Proof.
  unfold check, get_forest; intros;
  pose proof beq_expression_correct;
  match goal with
    [ Hbeq : context[Rtree.beq], y : Rtree.elt |- _ ] =>
    apply (Rtree.beq_sound beq_expression fa fb) with (x := y) in Hbeq
  end;
  repeat destruct_match; crush.
Qed.

Lemma get_empty:
  forall r, empty#r = Ebase r.
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

Lemma map0:
  forall r,
  empty # r = Ebase r.
Proof. intros; eapply get_empty. Qed.

Lemma map1:
  forall w dst dst',
  dst <> dst' ->
  (empty # dst <- w) # dst' = Ebase dst'.
Proof. intros; unfold get_forest; rewrite Rtree.gso; auto; apply map0. Qed.

Lemma genmap1:
  forall (f : forest) w dst dst',
  dst <> dst' ->
  (f # dst <- w) # dst' = f # dst'.
Proof. intros; unfold get_forest; rewrite Rtree.gso; auto. Qed.

Lemma map2:
  forall (v : expression) x rs,
  (rs # x <- v) # x = v.
Proof. intros; unfold get_forest; rewrite Rtree.gss; trivial. Qed.

Lemma tri1:
  forall x y,
  Reg x <> Reg y -> x <> y.
Proof. crush. Qed.

Definition ge_preserved {A B C D: Type} (ge: Genv.t A B) (tge: Genv.t C D) : Prop :=
  (forall sp op vl, Op.eval_operation ge sp op vl =
                    Op.eval_operation tge sp op vl)
  /\ (forall sp addr vl, Op.eval_addressing ge sp addr vl =
                         Op.eval_addressing tge sp addr vl).

Lemma ge_preserved_same:
  forall A B ge, @ge_preserved A B A B ge ge.
Proof. unfold ge_preserved; auto. Qed.
Hint Resolve ge_preserved_same : rtlpar.

Inductive sem_state_ld : sem_state -> sem_state -> Prop :=
| sem_state_ld_intro:
  forall rs rs' m m',
    regs_lessdef rs rs' ->
    m = m' ->
    sem_state_ld (mk_sem_state rs m) (mk_sem_state rs' m').

Lemma sems_det:
  forall A ge tge sp st f,
  ge_preserved ge tge ->
  forall v v' mv mv',
  (sem_value A ge sp st f v /\ sem_value A tge sp st f v' -> v = v') /\
  (sem_mem A ge sp st f mv /\ sem_mem A tge sp st f mv' -> mv = mv').
Proof. Admitted.

Lemma sem_value_det:
  forall A ge tge sp st f v v',
  ge_preserved ge tge ->
  sem_value A ge sp st f v ->
  sem_value A tge sp st f v' ->
  v = v'.
Proof.
  intros;
  generalize (sems_det A ge tge sp st f H v v'
                      st.(sem_state_memory) st.(sem_state_memory));
  crush.
Qed.
Hint Resolve sem_value_det : rtlpar.

Lemma sem_value_det':
  forall FF ge sp s f v v',
  sem_value FF ge sp s f v ->
  sem_value FF ge sp s f v' ->
  v = v'.
Proof.
  simplify; eauto with rtlpar.
Qed.

Lemma sem_mem_det:
  forall A ge tge sp st f m m',
  ge_preserved ge tge ->
  sem_mem A ge sp st f m ->
  sem_mem A tge sp st f m' ->
  m = m'.
Proof.
  intros;
  generalize (sems_det A ge tge sp st f H sp sp m m');
  crush.
Qed.
Hint Resolve sem_mem_det : rtlpar.

Lemma sem_mem_det':
  forall FF ge sp s f m m',
    sem_mem FF ge sp s f m ->
    sem_mem FF ge sp s f m' ->
    m = m'.
Proof.
  simplify; eauto with rtlpar.
Qed.

Hint Resolve Val.lessdef_same : rtlpar.

Lemma sem_regset_det:
  forall FF ge tge sp st f v v',
    ge_preserved ge tge ->
    sem_regset FF ge sp st f v ->
    sem_regset FF tge sp st f v' ->
    regs_lessdef v v'.
Proof.
  intros; unfold regs_lessdef.
  inv H0; inv H1;
  eauto with rtlpar.
Qed.
Hint Resolve sem_regset_det : rtlpar.

Lemma sem_det:
  forall FF ge tge sp st f st' st'',
    ge_preserved ge tge ->
    sem FF ge sp st f st' ->
    sem FF tge sp st f st'' ->
    sem_state_ld st' st''.
Proof.
  intros.
  destruct st; destruct st'; destruct st''.
  inv H0; inv H1.
  constructor; eauto with rtlpar.
Qed.
Hint Resolve sem_det : rtlpar.

Lemma sem_det':
  forall FF ge sp st f st' st'',
    sem FF ge sp st f st' ->
    sem FF ge sp st f st'' ->
    sem_state_ld st' st''.
Proof. eauto with rtlpar. Qed.

(*|
Update functions.
|*)

Fixpoint list_translation (l : list reg) (f : forest) {struct l} : expression_list :=
  match l with
  | nil => Enil
  | i :: l => Econs (f # (Reg i)) (list_translation l f)
  end.

Definition update (f : forest) (i : instr) : forest :=
  match i with
  | RBnop => f
  | RBop p op rl r =>
    f # (Reg r) <- (Eop op (list_translation rl f))
  | RBload p chunk addr rl r =>
    f # (Reg r) <- (Eload chunk addr (list_translation rl f) (f # Mem))
  | RBstore p chunk addr rl r =>
    f # Mem <- (Estore (f # Mem) chunk addr (list_translation rl f) (f # (Reg r)))
  | RBsetpred c addr p => f
  end.

(*|
Implementing which are necessary to show the correctness of the translation validation by showing
that there aren't any more effects in the resultant RTLPar code than in the RTLBlock code.

Get a sequence from the basic block.
|*)

Fixpoint abstract_sequence (f : forest) (b : list instr) : forest :=
  match b with
  | nil => f
  | i :: l => update (abstract_sequence f l) i
  end.

Fixpoint abstract_sequence_par (f : forest) (b : list (list instr)) : forest :=
  match b with
  | nil => f
  | i :: l => abstract_sequence (abstract_sequence_par f l) i
  end.

(*|
Check equivalence of control flow instructions.  As none of the basic blocks should have been moved,
none of the labels should be different, meaning the control-flow instructions should match exactly.
|*)

Definition check_control_flow_instr (c1 c2: cf_instr) : bool :=
  if cf_instr_eq c1 c2 then true else false.

(*|
We define the top-level oracle that will check if two basic blocks are equivalent after a scheduling
transformation.
|*)

Definition empty_trees (bb: RTLBlock.bb) (bbt: RTLPar.bb) : bool :=
  match bb with
  | nil =>
    match bbt with
    | nil => true
    | _ => false
    end
  | _ => true
  end.

Definition schedule_oracle (bb: RTLBlock.bblock) (bbt: RTLPar.bblock) : bool :=
  check (abstract_sequence empty (bb_body bb))
        (abstract_sequence_par empty (bb_body bbt)) &&
  check_control_flow_instr (bb_exit bb) (bb_exit bbt) &&
  empty_trees (bb_body bb) (bb_body bbt).

Definition check_scheduled_trees := beq2 schedule_oracle.

Ltac solve_scheduled_trees_correct :=
  intros; unfold check_scheduled_trees in *;
  match goal with
  | [ H: context[beq2 _ _ _], x: positive |- _ ] =>
    rewrite beq2_correct in H; specialize (H x)
  end; repeat destruct_match; crush.

Lemma check_scheduled_trees_correct:
  forall f1 f2,
    check_scheduled_trees f1 f2 = true ->
    (forall x y1,
        PTree.get x f1 = Some y1 ->
        exists y2, PTree.get x f2 = Some y2 /\ schedule_oracle y1 y2 = true).
Proof. solve_scheduled_trees_correct; eexists; crush. Qed.

Lemma check_scheduled_trees_correct2:
  forall f1 f2,
    check_scheduled_trees f1 f2 = true ->
    (forall x,
        PTree.get x f1 = None ->
        PTree.get x f2 = None).
Proof. solve_scheduled_trees_correct. Qed.

(*|
Abstract computations
=====================
|*)

Lemma abstract_execution_correct:
  forall bb bb' cfi ge tge sp rs m rs' m',
    ge_preserved ge tge ->
    schedule_oracle (mk_bblock bb cfi) (mk_bblock bb' cfi) = true ->
    RTLBlock.step_instr_list ge sp (InstrState rs m) bb (InstrState rs' m') ->
    exists rs'', RTLPar.step_instr_block tge sp (InstrState rs m) bb' (InstrState rs'' m')
                 /\ regs_lessdef rs' rs''.
Proof. Admitted.

(*|
Top-level functions
===================
|*)

Parameter schedule : RTLBlock.function -> RTLPar.function.

Definition transl_function (f: RTLBlock.function) : Errors.res RTLPar.function :=
  let tfcode := fn_code (schedule f) in
  if check_scheduled_trees f.(fn_code) tfcode then
    Errors.OK (mkfunction f.(fn_sig)
                          f.(fn_params)
                          f.(fn_stacksize)
                          tfcode
                          f.(fn_entrypoint))
  else
    Errors.Error (Errors.msg "RTLPargen: Could not prove the blocks equivalent.").

Definition transl_function_temp (f: RTLBlock.function) : Errors.res RTLPar.function :=
  let tfcode := fn_code (schedule f) in
    Errors.OK (mkfunction f.(fn_sig)
                          f.(fn_params)
                          f.(fn_stacksize)
                          tfcode
                          f.(fn_entrypoint)).

Definition transl_fundef := transf_partial_fundef transl_function_temp.

Definition transl_program (p : RTLBlock.program) : Errors.res RTLPar.program :=
  transform_partial_program transl_fundef p.
