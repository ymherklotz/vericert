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
| Eop : Op.operation -> expression_list -> expression -> expression
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

(*|
Finally we want to define the semantics of execution for the expressions with symbolic values, so
the result of executing the expressions will be an expressions.
|*)

Section SEMANTICS.

Context {A : Type} (genv : Genv.t A unit).

Inductive sem_value :
      val -> instr_state -> expression -> val -> Prop :=
  | Sbase_reg:
          forall sp rs r m,
          sem_value sp (InstrState rs m) (Ebase (Reg r)) (rs !! r)
  | Sop:
          forall rs m op args v lv sp m' mem_exp,
          sem_mem sp (InstrState rs m) mem_exp m' ->
          sem_val_list sp (InstrState rs m) args lv ->
          Op.eval_operation genv sp op lv m' = Some v ->
          sem_value sp (InstrState rs m) (Eop op args mem_exp) v
  | Sload :
          forall st mem_exp addr chunk args a v m' lv sp,
          sem_mem sp st mem_exp m' ->
          sem_val_list sp st args lv ->
          Op.eval_addressing genv sp addr lv = Some a ->
          Memory.Mem.loadv chunk m' a = Some v ->
          sem_value sp st (Eload chunk addr args mem_exp) v
with sem_mem :
          val -> instr_state -> expression -> Memory.mem -> Prop :=
  | Sstore :
          forall st mem_exp val_exp m'' addr v a m' chunk args lv sp,
          sem_mem sp st mem_exp m' ->
          sem_value sp st val_exp v ->
          sem_val_list sp st args lv ->
          Op.eval_addressing genv sp addr lv = Some a ->
          Memory.Mem.storev chunk m' a v = Some m'' ->
          sem_mem sp st (Estore mem_exp chunk addr args val_exp) m''
    | Sbase_mem :
            forall rs m sp,
            sem_mem sp (InstrState rs m) (Ebase Mem) m
with sem_val_list :
          val -> instr_state -> expression_list -> list val -> Prop :=
    | Snil :
            forall st sp,
            sem_val_list sp st Enil nil
    | Scons :
            forall st e v l lv sp,
            sem_value sp st e v ->
            sem_val_list sp st l lv ->
            sem_val_list sp st (Econs e l) (v :: lv).

Inductive sem_regset :
  val -> instr_state -> forest -> regset -> Prop :=
  | Sregset:
        forall st f sp rs',
        (forall x, sem_value sp st (f # (Reg x)) (Registers.Regmap.get x rs')) ->
        sem_regset sp st f rs'.

Inductive sem :
  val -> instr_state -> forest -> instr_state -> Prop :=
  | Sem:
        forall st rs' m' f sp,
        sem_regset sp st f rs' ->
        sem_mem sp st (f # Mem) m' ->
        sem sp st f (InstrState rs' m').

End SEMANTICS.

Fixpoint beq_expression (e1 e2: expression) {struct e1}: bool :=
  match e1, e2 with
  | Ebase r1, Ebase r2 => if resource_eq r1 r2 then true else false
  | Eop op1 el1 exp1, Eop op2 el2 exp2 =>
      if operation_eq op1 op2 then
      if beq_expression exp1 exp2 then
      beq_expression_list el1 el2 else false else false
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

Lemma check_correct: forall (fa fb : forest),
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
  (forall sp op vl m, Op.eval_operation ge sp op vl m =
                      Op.eval_operation tge sp op vl m)
  /\ (forall sp addr vl, Op.eval_addressing ge sp addr vl =
                         Op.eval_addressing tge sp addr vl).

Lemma ge_preserved_same:
  forall A B ge, @ge_preserved A B A B ge ge.
Proof. unfold ge_preserved; auto. Qed.
Hint Resolve ge_preserved_same : rtlpar.

Ltac rtlpar_crush := crush; eauto with rtlpar.

Inductive match_states : instr_state -> instr_state -> Prop :=
| match_states_intro:
  forall rs rs' m m',
    (forall x, rs !! x = rs' !! x) ->
    m = m' ->
    match_states (InstrState rs m) (InstrState rs' m').

Lemma sems_det:
  forall A ge tge sp st f,
  ge_preserved ge tge ->
  forall v v' mv mv',
  (@sem_value A ge sp st f v /\ @sem_value A tge sp st f v' -> v = v') /\
  (@sem_mem A ge sp st f mv /\ @sem_mem A tge sp st f mv' -> mv = mv').
Proof. Admitted.

Lemma sem_value_det:
  forall A ge tge sp st f v v',
  ge_preserved ge tge ->
  @sem_value A ge sp st f v ->
  @sem_value A tge sp st f v' ->
  v = v'.
Proof.
  intros. destruct st.
  generalize (sems_det A ge tge sp (InstrState rs m) f H v v'
                      m m);
  crush.
Qed.
Hint Resolve sem_value_det : rtlpar.

Lemma sem_value_det':
  forall FF ge sp s f v v',
  @sem_value FF ge sp s f v ->
  @sem_value FF ge sp s f v' ->
  v = v'.
Proof.
  simplify; eauto with rtlpar.
Qed.

Lemma sem_mem_det:
  forall A ge tge sp st f m m',
  ge_preserved ge tge ->
  @sem_mem A ge sp st f m ->
  @sem_mem A tge sp st f m' ->
  m = m'.
Proof.
  intros. destruct st.
  generalize (sems_det A ge tge sp (InstrState rs m0) f H sp sp m m');
  crush.
Qed.
Hint Resolve sem_mem_det : rtlpar.

Lemma sem_mem_det':
  forall FF ge sp s f m m',
    @sem_mem FF ge sp s f m ->
    @sem_mem FF ge sp s f m' ->
    m = m'.
Proof.
  simplify; eauto with rtlpar.
Qed.

Hint Resolve Val.lessdef_same : rtlpar.

Lemma sem_regset_det:
  forall FF ge tge sp st f v v',
    ge_preserved ge tge ->
    @sem_regset FF ge sp st f v ->
    @sem_regset FF tge sp st f v' ->
    (forall x, v !! x = v' !! x).
Proof.
  intros; unfold regs_lessdef.
  inv H0; inv H1;
  eauto with rtlpar.
Qed.
Hint Resolve sem_regset_det : rtlpar.

Lemma sem_det:
  forall FF ge tge sp st f st' st'',
    ge_preserved ge tge ->
    @sem FF ge sp st f st' ->
    @sem FF tge sp st f st'' ->
    match_states st' st''.
Proof.
  intros.
  destruct st; destruct st'; destruct st''.
  inv H0; inv H1.
  constructor; eauto with rtlpar.
Qed.
Hint Resolve sem_det : rtlpar.

Lemma sem_det':
  forall FF ge sp st f st' st'',
    @sem FF ge sp st f st' ->
    @sem FF ge sp st f st'' ->
    match_states st' st''.
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
    f # (Reg r) <- (Eop op (list_translation rl f) (f # Mem))
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
  | i :: l => abstract_sequence (update f i) l
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
        (abstract_sequence empty (concat (concat (bb_body bbt)))) &&
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

Definition is_regs i := match i with InstrState rs _ => rs end.
Definition is_mem i := match i with InstrState _ m => m end.

Inductive state_lessdef : instr_state -> instr_state -> Prop :=
  state_lessdef_intro :
    forall rs1 rs2 m1,
    (forall x, rs1 !! x = rs2 !! x) ->
    state_lessdef (InstrState rs1 m1) (InstrState rs2 m1).

(*|
RTLBlock to abstract translation
--------------------------------

Correctness of translation from RTLBlock to the abstract interpretation language.
|*)

Lemma match_states_refl x : match_states x x.
Proof. destruct x; constructor; crush. Qed.

Lemma match_states_commut x y : match_states x y -> match_states y x.
Proof. inversion 1; constructor; crush. Qed.

Lemma match_states_trans x y z :
  match_states x y -> match_states y z -> match_states x z.
Proof. repeat inversion 1; constructor; crush. Qed.

Ltac inv_simp :=
  repeat match goal with
  | H: exists _, _ |- _ => inv H
  end; simplify.

Lemma abstract_interp_empty A ge sp st : @sem A ge sp st empty st.
Proof. destruct st; repeat constructor. Qed.

Lemma abstract_interp_empty3 :
  forall A ge sp st st',
    @sem A ge sp st empty st' ->
    match_states st st'.
Proof.
  inversion 1; subst; simplify.
  destruct st. inv H1. simplify.
  constructor. unfold regs_lessdef.
  intros. inv H0. specialize (H1 x). inv H1; auto.
  auto.
Qed.

Definition check_dest i r' :=
  match i with
  | RBop p op rl r => (r =? r')%positive
  | RBload p chunk addr rl r => (r =? r')%positive
  | _ => false
  end.

Lemma check_dest_dec i r : {check_dest i r = true} + {check_dest i r = false}.
Proof. destruct (check_dest i r); tauto. Qed.

Fixpoint check_dest_l l r :=
  match l with
  | nil => false
  | a :: b => check_dest a r || check_dest_l b r
  end.

Lemma check_dest_l_forall :
  forall l r,
  check_dest_l l r = false ->
  Forall (fun x => check_dest x r = false) l.
Proof. induction l; crush. Qed.

Lemma check_dest_l_ex :
  forall l r,
  check_dest_l l r = true ->
  exists a, In a l /\ check_dest a r = true.
Proof.
  induction l; crush.
  destruct (check_dest a r) eqn:?; try solve [econstructor; crush].
  simplify.
  exploit IHl. apply H. inv_simp. econstructor. simplify. right. eassumption.
  auto.
Qed.

Lemma check_dest_l_dec i r : {check_dest_l i r = true} + {check_dest_l i r = false}.
Proof. destruct (check_dest_l i r); tauto. Qed.

Lemma check_dest_l_dec2 l r :
  {Forall (fun x => check_dest x r = false) l}
  + {exists a, In a l /\ check_dest a r = true}.
Proof.
  destruct (check_dest_l_dec l r); [right | left];
  auto using check_dest_l_ex, check_dest_l_forall.
Qed.

Lemma check_dest_l_forall2 :
  forall l r,
  Forall (fun x => check_dest x r = false) l ->
  check_dest_l l r = false.
Proof.
  induction l; crush.
  inv H. apply orb_false_intro; crush.
Qed.

Lemma check_dest_l_ex2 :
  forall l r,
  (exists a, In a l /\ check_dest a r = true) ->
  check_dest_l l r = true.
Proof.
  induction l; crush.
  specialize (IHl r). inv H.
  apply orb_true_intro; crush.
  apply orb_true_intro; crush.
  right. apply IHl. exists x. auto.
Qed.

Lemma check_dest_update :
  forall f i r,
  check_dest i r = false ->
  (update f i) # (Reg r) = f # (Reg r).
Proof.
  destruct i; crush; try apply Pos.eqb_neq in H; apply genmap1; crush.
Qed.

Lemma check_dest_update2 :
  forall f r rl op p,
  (update f (RBop p op rl r)) # (Reg r) = Eop op (list_translation rl f) (f # Mem).
Proof. crush; rewrite map2; auto. Qed.

Lemma check_dest_update3 :
  forall f r rl p addr chunk,
  (update f (RBload p chunk addr rl r)) # (Reg r) = Eload chunk addr (list_translation rl f) (f # Mem).
Proof. crush; rewrite map2; auto. Qed.

Lemma abstr_comp :
  forall l i f x x0,
  abstract_sequence f (l ++ i :: nil) = x ->
  abstract_sequence f l = x0 ->
  x = update x0 i.
Proof. induction l; intros; crush; eapply IHl; eauto. Qed.

Lemma abstract_seq :
  forall l f i,
    abstract_sequence f (l ++ i :: nil) = update (abstract_sequence f l) i.
Proof. induction l; crush. Qed.

Lemma check_list_l_false :
  forall l x r,
  check_dest_l (l ++ x :: nil) r = false ->
  check_dest_l l r = false /\ check_dest x r = false.
Proof.
  simplify.
  apply check_dest_l_forall in H. apply Forall_app in H.
  simplify. apply check_dest_l_forall2; auto.
  apply check_dest_l_forall in H. apply Forall_app in H.
  simplify. inv H1. auto.
Qed.

Lemma check_list_l_true :
  forall l x r,
  check_dest_l (l ++ x :: nil) r = true ->
  check_dest_l l r = true \/ check_dest x r = true.
Proof.
  simplify.
  apply check_dest_l_ex in H; inv_simp.
  apply in_app_or in H. inv H. left.
  apply check_dest_l_ex2. exists x0. auto.
  inv H0; auto.
Qed.

Lemma abstract_sequence_update :
  forall l r f,
  check_dest_l l r = false ->
  (abstract_sequence f l) # (Reg r) = f # (Reg r).
Proof.
  induction l using rev_ind; crush.
  rewrite abstract_seq. rewrite check_dest_update. apply IHl.
  apply check_list_l_false in H. tauto.
  apply check_list_l_false in H. tauto.
Qed.

Lemma rtlblock_trans_correct' :
  forall bb ge sp st x st'',
  RTLBlock.step_instr_list ge sp st (bb ++ x :: nil) st'' ->
  exists st', RTLBlock.step_instr_list ge sp st bb st'
              /\ step_instr ge sp st' x st''.
Proof.
  induction bb.
  crush. exists st.
  split. constructor. inv H. inv H6. auto.
  crush. inv H. exploit IHbb. eassumption. inv_simp.
  econstructor. split.
  econstructor; eauto. eauto.
Qed.

Lemma sem_update_RBnop :
  forall A ge sp st f st',
  @sem A ge sp st f st' -> sem ge sp st (update f RBnop) st'.
Proof. crush. Qed.

Lemma gen_list_base:
  forall FF ge sp l rs exps st1,
  (forall x, @sem_value FF ge sp st1 (exps # (Reg x)) (rs !! x)) ->
  sem_val_list ge sp st1 (list_translation l exps) rs ## l.
Proof.
  induction l.
  intros. simpl. constructor.
  intros. simpl. eapply Scons; eauto.
Qed.

Lemma abstract_seq_correct_aux:
  forall FF ge sp i st1 st2 st3 f,
    @step_instr FF ge sp st3 i st2 ->
    sem ge sp st1 f st3 ->
    sem ge sp st1 (update f i) st2.
Proof.
  intros; inv H; simplify.
  { simplify; eauto. } (*apply match_states_refl. }*)
  { inv H0. inv H6. destruct st1. econstructor. simplify.
    constructor. intros.
    destruct (resource_eq (Reg res) (Reg x)). inv e.
    rewrite map2. econstructor. eassumption. apply gen_list_base; eauto.
    rewrite Regmap.gss. eauto.
    assert (res <> x). { unfold not in *. intros. apply n. rewrite H0. auto. }
    rewrite Regmap.gso by auto.
    rewrite genmap1 by auto. auto.

    rewrite genmap1; crush. }
  { inv H0. inv H7. constructor. constructor. intros.
    destruct (Pos.eq_dec dst x); subst.
    rewrite map2. econstructor; eauto.
    apply gen_list_base. auto. rewrite Regmap.gss. auto.
    rewrite genmap1. rewrite Regmap.gso by auto. auto.
    unfold not in *; intros. inv H0. auto.
    rewrite genmap1; crush.
  }
  { inv H0. inv H7. constructor. constructor; intros.
    rewrite genmap1; crush.
    rewrite map2. econstructor; eauto.
    apply gen_list_base; auto.
  }
Qed.

Lemma regmap_list_equiv :
  forall A (rs1: Regmap.t A) rs2,
    (forall x, rs1 !! x = rs2 !! x) ->
    forall rl, rs1##rl = rs2##rl.
Proof. induction rl; crush. Qed.

Lemma sem_update_Op :
  forall A ge sp st f st' r l o0 o m rs v,
  @sem A ge sp st f st' ->
  Op.eval_operation ge sp o0 rs ## l m = Some v ->
  match_states st' (InstrState rs m) ->
  exists tst,
  sem ge sp st (update f (RBop o o0 l r)) tst /\ match_states (InstrState (Regmap.set r v rs) m) tst.
Proof.
  intros. inv H1. simplify.
  destruct st.
  econstructor. simplify.
  { constructor.
    { constructor. intros. destruct (Pos.eq_dec x r); subst.
      { pose proof (H5 r). rewrite map2. pose proof H. inv H. econstructor; eauto.
        { inv H9. eapply gen_list_base; eauto. }
        { instantiate (1 := (Regmap.set r v rs0)). rewrite Regmap.gss. erewrite regmap_list_equiv; eauto. } }
      { rewrite Regmap.gso by auto. rewrite genmap1; crush. inv H. inv H7; eauto. } }
    { inv H. rewrite genmap1; crush. eauto. } }
  { constructor; eauto. intros.
    destruct (Pos.eq_dec r x);
    subst; [repeat rewrite Regmap.gss | repeat rewrite Regmap.gso]; auto. }
Qed.

Lemma sem_update_load :
  forall A ge sp st f st' r o m a l m0 rs v a0,
  @sem A ge sp st f st' ->
  Op.eval_addressing ge sp a rs ## l = Some a0 ->
  Mem.loadv m m0 a0 = Some v ->
  match_states st' (InstrState rs m0) ->
  exists tst : instr_state,
    sem ge sp st (update f (RBload o m a l r)) tst
    /\ match_states (InstrState (Regmap.set r v rs) m0) tst.
Proof.
  intros. inv H2. pose proof H. inv H. inv H9.
  destruct st.
  econstructor; simplify.
  { constructor.
    { constructor. intros.
      destruct (Pos.eq_dec x r); subst.
      { rewrite map2. econstructor; eauto. eapply gen_list_base. intros.
        rewrite <- H6. eauto.
        instantiate (1 := (Regmap.set r v rs0)). rewrite Regmap.gss. auto. }
      { rewrite Regmap.gso by auto. rewrite genmap1; crush. } }
    { rewrite genmap1; crush. eauto. } }
  { constructor; auto; intros. destruct (Pos.eq_dec r x);
    subst; [repeat rewrite Regmap.gss | repeat rewrite Regmap.gso]; auto. }
Qed.

Lemma sem_update_store :
  forall A ge sp a0 m a l r o f st m' rs m0 st',
  @sem A ge sp st f st' ->
  Op.eval_addressing ge sp a rs ## l = Some a0 ->
  Mem.storev m m0 a0 rs !! r = Some m' ->
  match_states st' (InstrState rs m0) ->
  exists tst, sem ge sp st (update f (RBstore o m a l r)) tst
              /\ match_states (InstrState rs m') tst.
Proof.
  intros. inv H2. pose proof H. inv H. inv H9.
  destruct st.
  econstructor; simplify.
  { econstructor.
    { econstructor; intros. rewrite genmap1; crush. }
    { rewrite map2. econstructor; eauto. eapply gen_list_base. intros. rewrite <- H6.
      eauto. specialize (H6 r). rewrite H6. eauto. } }
  { econstructor; eauto. }
Qed.

Lemma sem_update :
  forall A ge sp st x st' st'' st''' f,
  sem ge sp st f st' ->
  match_states st' st''' ->
  @step_instr A ge sp st''' x st'' ->
  exists tst, sem ge sp st (update f x) tst /\ match_states st'' tst.
Proof.
  intros. destruct x; inv H1.
  { econstructor. split.
    apply sem_update_RBnop. eassumption.
    apply match_states_commut. auto. }
  { eapply sem_update_Op; eauto. }
  { eapply sem_update_load; eauto. }
  { eapply sem_update_store; eauto. }
Qed.

Lemma rtlblock_trans_correct :
  forall bb ge sp st st',
    RTLBlock.step_instr_list ge sp st bb st' ->
    forall tst,
      match_states st tst ->
      exists tst', sem ge sp tst (abstract_sequence empty bb) tst'
                   /\ match_states st' tst'.
Proof.
  induction bb using rev_ind; simplify.
  { econstructor. simplify. apply abstract_interp_empty.
    inv H. auto. }
  { apply rtlblock_trans_correct' in H. inv_simp.
    rewrite abstract_seq.
    exploit IHbb; try eassumption; []; inv_simp.
    exploit sem_update. apply H1. apply match_states_commut; eassumption.
    eauto. inv_simp. econstructor. split. apply H3.
    auto. }
Qed.

Lemma rtlpar_trans_correct :
  forall ge sp bb sem_st' sem_st,
  sem ge sp sem_st (abstract_sequence empty (concat (concat bb))) sem_st' ->
  exists st', RTLPar.step_instr_block ge sp sem_st bb st'
              /\ match_states sem_st' st'.
Proof. Admitted.

Lemma abstr_sem_val_mem :
  forall A B ge tge st tst sp a,
    ge_preserved ge tge ->
    forall v m,
    (@sem_mem A ge sp st a m /\ match_states st tst -> @sem_mem B tge sp tst a m) /\
    (@sem_value A ge sp st a v /\ match_states st tst -> @sem_value B tge sp tst a v).
Proof.
  intros * H.
  apply expression_ind2 with

    (P := fun (e1: expression) =>
    forall v m,
    (@sem_mem A ge sp st e1 m /\ match_states st tst -> @sem_mem B tge sp tst e1 m) /\
    (@sem_value A ge sp st e1 v /\ match_states st tst -> @sem_value B tge sp tst e1 v))

    (P0 := fun (e1: expression_list) =>
    forall lv, @sem_val_list A ge sp st e1 lv /\ match_states st tst -> @sem_val_list B tge sp tst e1 lv);
  simplify; intros; simplify.
  { inv H1. inv H2. constructor. }
  { inv H2. inv H1. rewrite H0. constructor. }
  { inv H3. }
  { inv H3. inv H4. econstructor. apply H1; auto. simplify. eauto. constructor. auto. auto.
    apply H0; simplify; eauto. constructor; eauto.
    unfold ge_preserved in *. simplify. rewrite <- H2. auto.
  }
  { inv H3. }
  { inv H3. inv H4. econstructor. apply H1; eauto; simplify; eauto. constructor; eauto.
    apply H0; simplify; eauto. constructor; eauto.
    inv H. rewrite <- H4. eauto.
    auto.
  }
  { inv H4. inv H5. econstructor. apply H0; eauto. simplify; eauto. constructor; eauto.
    apply H2; eauto. simplify; eauto. constructor; eauto.
    apply H1; eauto. simplify; eauto. constructor; eauto.
    inv H. rewrite <- H5. eauto. auto.
  }
  { inv H4. }
  { inv H1. constructor. }
  { inv H3. constructor; auto. apply H0; eauto. apply Mem.empty. }
Qed.

Lemma abstr_sem_value :
  forall a A B ge tge sp st tst v,
    @sem_value A ge sp st a v ->
    ge_preserved ge tge ->
    match_states st tst ->
    @sem_value B tge sp tst a v.
Proof. intros; eapply abstr_sem_val_mem; eauto; apply Mem.empty. Qed.

Lemma abstr_sem_mem :
  forall a A B ge tge sp st tst v,
    @sem_mem A ge sp st a v ->
    ge_preserved ge tge ->
    match_states st tst ->
    @sem_mem B tge sp tst a v.
Proof. intros; eapply abstr_sem_val_mem; eauto. Qed.

Lemma abstr_sem_regset :
  forall a a' A B ge tge sp st tst rs,
    @sem_regset A ge sp st a rs ->
    ge_preserved ge tge ->
    (forall x, a # x = a' # x) ->
    match_states st tst ->
    exists rs', @sem_regset B tge sp tst a' rs' /\ (forall x, rs !! x = rs' !! x).
Proof.
  inversion 1; intros.
  inv H7.
  econstructor. simplify. econstructor. intros.
  eapply abstr_sem_value; eauto. rewrite <- H6.
  eapply H0. constructor; eauto.
  auto.
Qed.

Lemma abstr_sem :
  forall a a' A B ge tge sp st tst st',
    @sem A ge sp st a st' ->
    ge_preserved ge tge ->
    (forall x, a # x = a' # x) ->
    match_states st tst ->
    exists tst', @sem B tge sp tst a' tst' /\ match_states st' tst'.
Proof.
  inversion 1; subst; intros.
  inversion H4; subst.
  exploit abstr_sem_regset; eauto; inv_simp.
  do 3 econstructor; eauto.
  rewrite <- H3.
  eapply abstr_sem_mem; eauto.
Qed.

Lemma abstract_execution_correct':
  forall A B ge tge sp st' a a' st tst,
  @sem A ge sp st a st' ->
  ge_preserved ge tge ->
  check a a' = true ->
  match_states st tst ->
  exists tst', @sem B tge sp tst a' tst' /\ match_states st' tst'.
Proof.
  intros;
  pose proof (check_correct a a' H1);
  eapply abstr_sem; eauto.
Qed.

Lemma states_match :
  forall st1 st2 st3 st4,
  match_states st1 st2 ->
  match_states st2 st3 ->
  match_states st3 st4 ->
  match_states st1 st4.
Proof.
  intros * H1 H2 H3; destruct st1; destruct st2; destruct st3; destruct st4.
  inv H1. inv H2. inv H3; constructor.
  unfold regs_lessdef in *. intros.
  repeat match goal with
         | H: forall _, _, r : positive |- _ => specialize (H r)
         end.
  congruence.
  auto.
Qed.

Lemma step_instr_block_same :
  forall ge sp st st',
  step_instr_block ge sp st nil st' ->
  st = st'.
Proof. inversion 1; auto. Qed.

Lemma step_instr_seq_same :
  forall ge sp st st',
  step_instr_seq ge sp st nil st' ->
  st = st'.
Proof. inversion 1; auto. Qed.

Lemma match_states_list :
  forall A (rs: Regmap.t A) rs',
  (forall r, rs !! r = rs' !! r) ->
  forall l, rs ## l = rs' ## l.
Proof. induction l; crush. Qed.

Lemma PTree_matches :
  forall A (v: A) res rs rs',
  (forall r, rs !! r = rs' !! r) ->
  forall x, (Regmap.set res v rs) !! x = (Regmap.set res v rs') !! x.
Proof.
  intros; destruct (Pos.eq_dec x res); subst;
  [ repeat rewrite Regmap.gss by auto
  | repeat rewrite Regmap.gso by auto ]; auto.
Qed.

Lemma step_instr_matches :
  forall A a ge sp st st',
  @step_instr A ge sp st a st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr ge sp tst a tst'
                           /\ match_states st' tst'.
Proof.
  induction 1; simplify;
  match goal with H: match_states _ _ |- _ => inv H end;
  repeat econstructor; try erewrite match_states_list;
  try apply PTree_matches; eauto;
  match goal with
    H: forall _, _ |- context[Mem.storev] => erewrite <- H; eauto
  end.
Qed.

Lemma step_instr_list_matches :
  forall a ge sp st st',
  step_instr_list ge sp st a st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr_list ge sp tst a tst'
                           /\ match_states st' tst'.
Proof.
  induction a; intros; inv H;
  try (exploit step_instr_matches; eauto; []; inv_simp;
       exploit IHa; eauto; []; inv_simp); repeat econstructor; eauto.
Qed.

Lemma step_instr_seq_matches :
  forall a ge sp st st',
  step_instr_seq ge sp st a st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr_seq ge sp tst a tst'
                           /\ match_states st' tst'.
Proof.
  induction a; intros; inv H;
  try (exploit step_instr_list_matches; eauto; []; inv_simp;
       exploit IHa; eauto; []; inv_simp); repeat econstructor; eauto.
Qed.

Lemma step_instr_block_matches :
  forall bb ge sp st st',
  step_instr_block ge sp st bb st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr_block ge sp tst bb tst'
                           /\ match_states st' tst'.
Proof.
  induction bb; intros; inv H;
  try (exploit step_instr_seq_matches; eauto; []; inv_simp;
       exploit IHbb; eauto; []; inv_simp); repeat econstructor; eauto.
Qed.

Lemma abstract_execution_correct:
  forall bb bb' cfi ge tge sp st st' tst,
    RTLBlock.step_instr_list ge sp st bb st' ->
    ge_preserved ge tge ->
    schedule_oracle (mk_bblock bb cfi) (mk_bblock bb' cfi) = true ->
    match_states st tst ->
    exists tst', RTLPar.step_instr_block tge sp tst bb' tst'
                 /\ match_states st' tst'.
Proof.
  intros.
  unfold schedule_oracle in *. simplify.
  exploit rtlblock_trans_correct; try eassumption; []; inv_simp.
  exploit abstract_execution_correct';
  try solve [eassumption | apply state_lessdef_match_sem; eassumption].
  apply match_states_commut. eauto. inv_simp.
  exploit rtlpar_trans_correct; try eassumption; []; inv_simp.
  exploit step_instr_block_matches; eauto; inv_simp.
  repeat match goal with | H: match_states _ _ |- _ => inv H end.
  do 2 econstructor; eauto.
  econstructor; congruence.
Qed.

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
