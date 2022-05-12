(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

================
RTLBlockgenproof
================

.. coq:: none
|*)

Require compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Maps.
Require Import compcert.backend.Registers.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLBlockgen.

#[local] Open Scope positive.

(*|
Defining a find block specification
===================================

Basically, it should be able to find the location of the block without using the
``find_block`` function, so that this is more useful for the proofs.  There are
various different types of options that could come up though:

1. The instruction is a standard instruction present inside of a basic block.
2. The instruction is a standard instruction which ends with a ``goto``.
3. The instruction is a control-flow instruction.

For case number 1, there should exist a value in the list of instructions, such
that the instructions match exactly, and the indices match as well.  In the
original code, this instruction must have been going from the current node to
the node - 1.

For case number 2, there should be an instruction at the right index again,
however, this time there will also be a ``goto`` instruction in the control-flow
part of the basic block.

For case number 3, there should be a ``nop`` instruction in the basic block, and
then the equivalent control-flow instruction ending the basic block.

In the end though, it seems like two cases are actually enough, as the last two
cases are similar enough that they can be merged into one.
|*)

Definition all_max {A} (c: PTree.t A) p: Prop :=
  Forall (fun x => x <= p) (map fst (PTree.elements c)).

Definition find_block_spec (c: code) (n1 n2: node): Prop :=
  forall x, all_max c x -> find_block x (map fst (PTree.elements c)) n1 = n2.

Definition offset (pc pc': positive): nat := Pos.to_nat pc' - Pos.to_nat pc.

Definition find_instr_spec (c: code) (n: node) (i: RTL.instruction)
           (n': node) (i': instr) :=
  find_block_spec c n n' /\
  exists il, c ! n' = Some il
        /\ nth_error il.(bb_body) (offset n n') = Some i'.

(*|
.. index::
   pair: semantics; transl_code_spec

Translation Specification
-------------------------

This specification should describe the translation that the unverified
transformation performs.  This should be proven from the validation of the
transformation.

This also specifies ``x'`` relative to x given the code.
|*)

Variant transl_code_spec (c: RTL.code) (tc: code) (x x': node) (i: RTL.instruction) (i': instr): Prop :=
| transl_code_standard_bb :
    c ! x = Some i ->
    Is_true (check_instr x i i') ->
    transl_code_spec c tc x x' i i'
| transl_code_standard_cf :
  forall il,
    c ! x = Some i ->
    tc ! x' = Some il ->
    Is_true (check_cf_instr_body i i') ->
    Is_true (check_cf_instr i il.(bb_exit)) ->
    transl_code_spec c tc x x' i i'
.

Section CORRECTNESS.

  Context (prog : RTL.program).
  Context (tprog : RTLBlock.program).

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

(*|
Matches the basic block that should be present in the state.  This simulates the
small step execution of the basic block from the big step semantics that are
currently present.

Why does it not need to find the pc' value using ``find_block``?

It doesn't have to find the value because it's given as an input, and the
finding is actually done at that higher level already.
|*)

(*  Variant match_bblock (tc: code) (pc pc': node): list instr -> Prop :=
    | match_bblock_intro :
      forall bb cf,
        tc ! pc' = Some (mk_bblock bb cf) ->
        match_bblock tc pc pc' (list_drop (offset pc pc') bb).*)

  Definition imm_succ (pc pc': node) : Prop := pc' = Pos.pred pc.

  Definition valid_succ (tc: code) (pc: node) : Prop := exists b, tc ! pc = Some b.

  Inductive match_block (c: RTL.code) (tc: code) (pc: node): bb -> cf_instr -> Prop :=
  (*
   * Basic Block Instructions
   *)
  | match_block_nop b cf pc':
    c ! pc = Some (RTL.Inop pc') ->
    match_block c tc pc' b cf ->
    match_block c tc pc (RBnop :: b) cf
  | match_block_op cf b op args dst pc':
    c ! pc = Some (RTL.Iop op args dst pc') ->
    match_block c tc pc' b cf ->
    match_block c tc pc (RBop None op args dst :: b) cf
  | match_block_load cf b chunk addr args dst pc':
    c ! pc = Some (RTL.Iload chunk addr args dst pc') ->
    match_block c tc pc' b cf ->
    match_block c tc pc (RBload None chunk addr args dst :: b) cf
  | match_block_store cf b chunk addr args src pc':
    c ! pc = Some (RTL.Istore chunk addr args src pc') ->
    match_block c tc pc' b cf ->
    match_block c tc pc (RBstore None chunk addr args src :: b) cf
  (*
   * Control flow instructions using goto
   *)
  | match_block_goto pc':
    c ! pc = Some (RTL.Inop pc') ->
    valid_succ tc pc' ->
    match_block c tc pc (RBnop :: nil) (RBgoto pc')
  | match_block_op_cf pc' op args dst:
    c ! pc = Some (RTL.Iop op args dst pc') ->
    valid_succ tc pc' ->
    match_block c tc pc (RBop None op args dst :: nil) (RBgoto pc')
  | match_block_load_cf pc' chunk addr args dst:
    c ! pc = Some (RTL.Iload chunk addr args dst pc') ->
    valid_succ tc pc' ->
    match_block c tc pc (RBload None chunk addr args dst :: nil) (RBgoto pc')
  | match_block_store_cf pc' chunk addr args src:
    c ! pc = Some (RTL.Istore chunk addr args src pc') ->
    valid_succ tc pc' ->
    match_block c tc pc (RBstore None chunk addr args src :: nil) (RBgoto pc')
  (*
   * Standard control flow instructions
   *)
  | match_block_call sig ident args dst pc' :
    c ! pc = Some (RTL.Icall sig ident args dst pc') ->
    valid_succ tc pc' ->
    match_block c tc pc (RBnop :: nil) (RBcall sig ident args dst pc')
  | match_block_tailcall sig ident args :
    c ! pc = Some (RTL.Itailcall sig ident args) ->
    match_block c tc pc (RBnop :: nil) (RBtailcall sig ident args)
  | match_block_builtin ident args dst pc' :
    c ! pc = Some (RTL.Ibuiltin ident args dst pc') ->
    valid_succ tc pc' ->
    match_block c tc pc (RBnop :: nil) (RBbuiltin ident args dst pc')
  | match_block_cond cond args pct pcf :
    c ! pc = Some (RTL.Icond cond args pct pcf) ->
    valid_succ tc pct ->
    valid_succ tc pcf ->
    match_block c tc pc (RBnop :: nil) (RBcond cond args pct pcf)
  | match_block_jumptable r ns :
    c ! pc = Some (RTL.Ijumptable r ns) ->
    Forall (valid_succ tc) ns ->
    match_block c tc pc (RBnop :: nil) (RBjumptable r ns)
  | match_block_return r :
    c ! pc = Some (RTL.Ireturn r) ->
    match_block c tc pc (RBnop :: nil) (RBreturn r)
  .

(*|
Match the code
~~~~~~~~~~~~~~

The ``match_code`` predicate asserts that for any node in the original
control-flow graph, there is now a basic block in the new control- and data-flow
graph that contains the same instruction, but also that the whole basic block
matches some sequence of instructions starting at the node that corresponds to
the basic block.
|*)

  Definition match_code (c: RTL.code) (tc: code) : Prop :=
    forall pc b, tc ! pc = Some b -> match_block c tc pc b.(bb_body) b.(bb_exit).

  Variant match_stackframe : RTL.stackframe -> stackframe -> Prop :=
    | match_stackframe_init :
      forall res f tf sp pc rs
        (TF: transl_function f = OK tf)
        (VALID: valid_succ tf.(fn_code) pc),
        match_stackframe (RTL.Stackframe res f sp pc rs)
                         (Stackframe res tf sp pc rs (PMap.init false)).

  Definition sem_extrap f pc sp in_s in_s' block :=
    forall out_s block2,
      step_instr_list tge sp in_s block out_s ->
      f.(fn_code) ! pc = Some block2 ->
      step_instr_list tge sp in_s' block2.(bb_body) out_s.

  Lemma match_block_exists_instr :
    forall c tc pc a b,
      match_block c tc pc a b ->
      exists i, c ! pc = Some i.
  Proof. inversion 1; eexists; eauto. Qed.

  Lemma match_block_not_nil :
    forall c tc pc a b,
      match_block c tc pc a b -> a <> nil.
  Proof. inversion 1; crush. Qed.

(*|
Matching states
~~~~~~~~~~~~~~~

Initially, the idea was to define the ``match_states`` predicate normally to
defines how to find the correct ``bb`` that should be executed, as well as the
value of ``pc``.  However, this does not quite work when proving the equivalence
of the translation from ``RTL`` to ``RTLBlock``, because one cannot match one
transition to a transition in RTLBlock.  The alternative to this is to include a
proof inside of the ``match_states`` that shows that the execution from the
``pc`` of the start of the basic block to the current point is the same as the
whole execution (in one big step) of the basic block.
|*)

  Variant match_states : option bb -> RTL.state -> RTLBlock.state -> Prop :=
    | match_state :
      forall stk stk' f tf sp pc rs m pc0 b rs0 m0
        (TF: transl_function f = OK tf)
        (* TODO: I can remove the following [match_code]. *)
        (CODE: match_code f.(RTL.fn_code) tf.(fn_code))
        (BLOCK: exists b',
            tf.(fn_code) ! pc0 = Some b'
            /\ match_block f.(RTL.fn_code) tf.(fn_code) pc b b'.(bb_exit))
        (STK: Forall2 match_stackframe stk stk')
        (STARSIMU: star RTL.step ge (RTL.State stk f sp pc0 rs0 m0)
                                  E0 (RTL.State stk f sp pc rs m))
        (BB: sem_extrap tf pc0 sp (mk_instr_state rs (PMap.init false) m)
                        (mk_instr_state rs0 (PMap.init false) m0) b),
        match_states (Some b) (RTL.State stk f sp pc rs m)
                     (State stk' tf sp pc0 rs0 (PMap.init false) m0)
    | match_callstate :
      forall cs cs' f tf args m
        (TF: transl_fundef f = OK tf)
        (STK: Forall2 match_stackframe cs cs'),
        match_states None (RTL.Callstate cs f args m) (Callstate cs' tf args m)
    | match_returnstate :
      forall cs cs' v m
        (STK: Forall2 match_stackframe cs cs'),
        match_states None (RTL.Returnstate cs v m) (Returnstate cs' v m)
  .

  Definition match_prog (p: RTL.program) (tp: RTLBlock.program) :=
    Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  Context (TRANSL : match_prog prog tprog).

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof using TRANSL. intros; eapply (Genv.senv_transf_partial TRANSL). Qed.
  #[local] Hint Resolve senv_preserved : rtlbg.

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
  Proof (Genv.find_funct_ptr_transf_partial TRANSL).

  Lemma sig_transl_function:
    forall (f: RTL.fundef) (tf: RTLBlock.fundef),
      transl_fundef f = OK tf ->
      RTLBlock.funsig tf = RTL.funsig f.
  Proof using.
    unfold transl_fundef. unfold transf_partial_fundef.
    intros. destruct_match. unfold bind in *. destruct_match; try discriminate.
    inv H. unfold transl_function in Heqr.
    repeat (destruct_match; try discriminate). inv Heqr. auto.
    inv H; auto.
  Qed.

  Definition measure (b: option bb): nat :=
    match b with
    | None => 0
    | Some b' => 1 + length b'
    end.

  Lemma transl_initial_states :
    forall s1, RTL.initial_state prog s1 ->
      exists s2, RTLBlock.initial_state tprog s2 /\ match_states None s1 s2.
  Proof using TRANSL.
    induction 1.
    exploit function_ptr_translated; eauto. intros [tf [A B]].
    do 2 econstructor. simplify. econstructor.
    apply (Genv.init_mem_transf_partial TRANSL); eauto.
    replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
    symmetry; eapply Linking.match_program_main; eauto. eauto.
    erewrite sig_transl_function; eauto. constructor. auto. auto.
  Qed.

  Lemma transl_final_states :
    forall s1 s2 r b,
      match_states b s1 s2 ->
      RTL.final_state s1 r ->
      RTLBlock.final_state s2 r.
  Proof using.
    inversion 2; crush. subst. inv H. inv STK. econstructor.
  Qed.

  Lemma hd_nth_equiv:
    forall A n (l: list A), hd_error (list_drop n l) = nth_error l n.
  Proof. induction n; destruct l; crush. Qed.

  Lemma hd_error_Some_exists:
    forall A (l: list A) n, hd_error l = Some n -> l = n :: tl l.
  Proof. induction l; crush. Qed.

  Definition imm_succ_dec pc pc' : {imm_succ pc pc'} + {~ imm_succ pc pc'}.
  Proof.
    unfold imm_succ. pose proof peq.
    decide equality.
  Defined.

  Lemma imm_succ_refl pc : imm_succ pc (Pos.pred pc).
  Proof. unfold imm_succ; auto. Qed.

  Lemma imm_succ_refl2 pc : imm_succ (Pos.succ pc) pc.
  Proof. unfold imm_succ; auto using Pos.pred_succ. Qed.

  Lemma sim_star :
    forall s1 b t s,
      (exists b' s2,
        star step tge s1 t s2 /\ ltof _ measure b' b
        /\ match_states b' s s2) ->
      exists b' s2,
        (plus step tge s1 t s2 \/
           star step tge s1 t s2 /\ ltof _ measure b' b) /\
          match_states b' s s2.
  Proof. intros; simplify. do 3 econstructor; eauto. Qed.

  Lemma sim_plus :
    forall s1 b t s,
      (exists b' s2, plus step tge s1 t s2 /\ match_states b' s s2) ->
      exists b' s2,
        (plus step tge s1 t s2 \/
           star step tge s1 t s2 /\ ltof _ measure b' b) /\
          match_states b' s s2.
  Proof. intros; simplify. do 3 econstructor; eauto. Qed.

  Lemma transl_Inop_correct:
    forall s f sp pc rs m pc',
      (RTL.fn_code f) ! pc = Some (RTL.Inop pc') ->
      forall b s2, match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2'
           \/ star step tge s2 E0 s2' /\ ltof _ measure b' b)
          /\ match_states b' (RTL.State s f sp pc' rs m) s2'.
  Proof.
    intros * H.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify.
    { apply sim_star.
      do 3 econstructor. eapply star_refl. constructor.
      instantiate (1 := Some b); unfold ltof; auto.

      constructor; try eassumption. econstructor; eauto.
      eapply star_right; eauto.
      eapply RTL.exec_Inop; eauto. auto.

      unfold sem_extrap in *. intros.
      eapply BB. econstructor; eauto.
      econstructor; eauto. auto.
    }
    { apply sim_plus.
      inv H0. simplify.
      unfold valid_succ in *; simplify.
      do 3 econstructor. apply plus_one. econstructor.
      eassumption. eapply BB; [| eassumption ].
      econstructor; econstructor; eauto.
      setoid_rewrite <- H1. econstructor.

      econstructor; try eassumption. eauto.
      eapply star_refl.
      unfold sem_extrap. intros. setoid_rewrite H7 in H0.
      crush.
    }
  Qed.

  Lemma eval_op_eq:
    forall (sp0 : Values.val) (op : Op.operation) (vl : list Values.val) m,
      Op.eval_operation ge sp0 op vl m = Op.eval_operation tge sp0 op vl m.
  Proof using TRANSL.
    intros.
    destruct op; auto; unfold Op.eval_operation, Genv.symbol_address, Op.eval_addressing32;
    [| destruct a; unfold Genv.symbol_address ];
    try rewrite symbols_preserved; auto.
  Qed.

  Lemma eval_addressing_eq:
    forall sp addr vl,
      Op.eval_addressing ge sp addr vl = Op.eval_addressing tge sp addr vl.
  Proof using TRANSL.
    intros.
    destruct addr;
      unfold Op.eval_addressing, Op.eval_addressing32;
      unfold Genv.symbol_address;
      try rewrite symbols_preserved; auto.
  Qed.

  Lemma transl_Iop_correct_nj:
    forall s f sp pc rs m op args res pc' v stk' tf pc1 rs1 m1 b x,
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res pc') ->
      Op.eval_operation ge sp op rs ## args m = Some v ->
      transl_function f = OK tf ->
      (forall pc0 b0,
          (fn_code tf) ! pc0 = Some b0 -> match_block (RTL.fn_code f) (fn_code tf) pc0 (bb_body b0) (bb_exit b0)) ->
      Forall2 match_stackframe s stk' ->
      star RTL.step ge (RTL.State s f sp pc1 rs1 m1) E0 (RTL.State s f sp pc rs m) ->
      sem_extrap tf pc1 sp {| is_rs := rs; is_ps := PMap.init false; is_mem := m |}
                 {| is_rs := rs1; is_ps := PMap.init false; is_mem := m1 |} (RBop None op args res :: b) ->
      (fn_code tf) ! pc1 = Some x ->
      match_block (RTL.fn_code f) (fn_code tf) pc' b (bb_exit x) ->
      exists b' s2',
        star step tge (State stk' tf sp pc1 rs1 (PMap.init false) m1) E0 s2'
        /\ ltof _ measure b' (Some (RBop None op args res :: b))
        /\ match_states b' (RTL.State s f sp pc' rs # res <- v m) s2'.
  Proof.
    intros * IOP EVAL TR MATCHB STK STAR BB INCODE MATCHB2.
    do 3 econstructor. eapply star_refl. constructor.
    instantiate (1 := Some b); unfold ltof; auto.

    constructor; try eassumption. econstructor; eauto.
    eapply star_right; eauto.
    eapply RTL.exec_Iop; eauto. auto.

    unfold sem_extrap in *. intros.
    eapply BB. econstructor; eauto.
    econstructor; eauto.
    rewrite <- eval_op_eq; eassumption.
    constructor. auto.
  Qed.

  Lemma transl_Iop_correct_j:
    forall s f sp pc rs m op args res pc' v stk' tf pc1 rs1 m1 x,
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res pc') ->
      Op.eval_operation ge sp op rs ## args m = Some v ->
      transl_function f = OK tf ->
      (forall (pc0 : positive) (b : RTLBlockInstr.bblock),
          (fn_code tf) ! pc0 = Some b -> match_block (RTL.fn_code f) (fn_code tf) pc0 (bb_body b) (bb_exit b)) ->
      Forall2 match_stackframe s stk' ->
      star RTL.step ge (RTL.State s f sp pc1 rs1 m1) E0 (RTL.State s f sp pc rs m) ->
      sem_extrap tf pc1 sp {| is_rs := rs; is_ps := PMap.init false; is_mem := m |}
                 {| is_rs := rs1; is_ps := PMap.init false; is_mem := m1 |} (RBop None op args res :: nil) ->
      (fn_code tf) ! pc1 = Some x ->
      RBgoto pc' = bb_exit x ->
      valid_succ (fn_code tf) pc' ->
      exists b' s2,
        plus step tge (State stk' tf sp pc1 rs1 (PMap.init false) m1) E0 s2 /\
          match_states b' (RTL.State s f sp pc' rs # res <- v m) s2.
  Proof.
    intros * H H0 TF CODE STK STARSIMU BB H3 H2 H7.
    inv H0. simplify.
    unfold valid_succ in H7; simplify.
    do 3 econstructor. apply plus_one. econstructor.
    eassumption. eapply BB; [| eassumption ].
    econstructor; econstructor; eauto.
    rewrite <- eval_op_eq; eassumption.
    constructor. setoid_rewrite <- H2.
    econstructor.

    econstructor; try eassumption. eauto.
    eapply star_refl.
    unfold sem_extrap. intros. setoid_rewrite H0 in H5.
    crush.
  Qed.

  Lemma transl_Iop_correct:
    forall s f sp pc rs m op args res pc' v,
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res pc') ->
      Op.eval_operation ge sp op rs##args m = Some v ->
      forall b s2, match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2'
           \/ star step tge s2 E0 s2' /\ ltof _ measure b' b)
          /\ match_states b' (RTL.State s f sp pc' (rs # res <- v) m) s2'.
  Proof.
    intros * H H0.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify.
    { apply sim_star; eapply transl_Iop_correct_nj; eassumption. }
    { apply sim_plus. eapply transl_Iop_correct_j; eassumption. }
  Qed.

  Lemma transl_Iload_correct:
    forall s f sp pc rs m chunk addr args dst pc' a v,
      (RTL.fn_code f) ! pc = Some (RTL.Iload chunk addr args dst pc') ->
      Op.eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      forall b s2, match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2'
           \/ star step tge s2 E0 s2' /\ ltof _ measure b' b)
          /\ match_states b' (RTL.State s f sp pc' (rs # dst <- v) m) s2'.
  Proof.
    intros * H H0 H1.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify.
    { apply sim_star.
      do 3 econstructor. eapply star_refl. constructor.
      instantiate (1 := Some b); unfold ltof; auto.

      constructor; try eassumption. econstructor; eauto.
      eapply star_right; eauto.
      eapply RTL.exec_Iload; eauto. auto.

      unfold sem_extrap in *. intros.
      eapply BB. econstructor; eauto.
      econstructor; eauto.
      rewrite <- eval_addressing_eq; eassumption.
      constructor. auto.
    }
    { apply sim_plus.
      inv H0. simplify.
      unfold valid_succ in H8; simplify.
      do 3 econstructor. apply plus_one. econstructor.
      eassumption. eapply BB; [| eassumption ].
      econstructor; econstructor; eauto.
      rewrite <- eval_addressing_eq; eassumption.
      constructor. setoid_rewrite <- H3.
      econstructor.

      econstructor; try eassumption. eauto.
      eapply star_refl.
      unfold sem_extrap. intros. setoid_rewrite H0 in H8.
      crush.
    }
  Qed.

  Lemma transl_Istore_correct:
    forall s f sp pc rs m chunk addr args src pc' a m',
      (RTL.fn_code f) ! pc = Some (RTL.Istore chunk addr args src pc') ->
      Op.eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      forall b s2, match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2'
           \/ star step tge s2 E0 s2' /\ ltof _ measure b' b)
          /\ match_states b' (RTL.State s f sp pc' rs m') s2'.
  Proof.
    intros * H H0 H1.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify.
    { apply sim_star.
      do 3 econstructor. eapply star_refl. constructor.
      instantiate (1 := Some b); unfold ltof; auto.

      constructor; try eassumption. econstructor; eauto.
      eapply star_right; eauto.
      eapply RTL.exec_Istore; eauto. auto.

      unfold sem_extrap in *. intros.
      eapply BB. econstructor; eauto.
      econstructor; eauto.
      rewrite <- eval_addressing_eq; eassumption.
      constructor. auto.
    }
    { apply sim_plus.
      inv H0. simplify.
      unfold valid_succ in H8; simplify.
      do 3 econstructor. apply plus_one. econstructor.
      eassumption. eapply BB; [| eassumption ].
      econstructor; econstructor; eauto.
      rewrite <- eval_addressing_eq; eassumption.
      constructor. setoid_rewrite <- H3.
      econstructor.

      econstructor; try eassumption. eauto.
      eapply star_refl.
      unfold sem_extrap. intros. setoid_rewrite H0 in H8.
      crush.
    }
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: RTL.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma find_function_translated:
    forall ros rs rs' f,
      (forall x, rs !! x = rs' !! x) ->
      RTL.find_function ge ros rs = Some f ->
      exists tf, find_function tge ros rs' = Some tf
                 /\ transl_fundef f = OK tf.
  Proof using TRANSL.
    Ltac ffts := match goal with
                 | [ H: forall _, Val.lessdef _ _, r: Registers.reg |- _ ] =>
                   specialize (H r); inv H
                 | [ H: Vundef = ?r, H1: Genv.find_funct _ ?r = Some _ |- _ ] =>
                   rewrite <- H in H1
                 | [ H: Genv.find_funct _ Vundef = Some _ |- _] => solve [inv H]
                 | _ => solve [exploit functions_translated; eauto]
                 end.
    destruct ros; simplify; try rewrite <- H;
    [| rewrite symbols_preserved; destruct_match;
      try (apply function_ptr_translated); crush ];
    intros;
    repeat ffts.
  Qed.

  Lemma transl_Icall_correct:
    forall s f sp pc rs m sig ros args res pc' fd,
      (RTL.fn_code f) ! pc = Some (RTL.Icall sig ros args res pc') ->
      RTL.find_function ge ros rs = Some fd ->
      RTL.funsig fd = sig ->
      forall b s2, match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof _ measure b' b) /\
            match_states b' (RTL.Callstate (RTL.Stackframe res f sp pc' rs :: s) fd rs ## args m) s2'.
  Proof.
    intros * H H0 H1.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify;
    apply sim_plus.
    inv H0. simplify.
    unfold valid_succ in H7; simplify.
    exploit find_function_translated; eauto; simplify.
    do 3 econstructor. apply plus_one. econstructor.
    eassumption. eapply BB; [| eassumption ].
    econstructor; econstructor; eauto.
    setoid_rewrite <- H1.
    econstructor; eauto.
    apply sig_transl_function; auto.

    econstructor; try eassumption.
    constructor. constructor; auto.
    unfold valid_succ; eauto. auto.
  Qed.

  Lemma transl_Itailcall_correct:
    forall s f stk pc rs m sig ros args fd m',
      (RTL.fn_code f) ! pc = Some (RTL.Itailcall sig ros args) ->
      RTL.find_function ge ros rs = Some fd ->
      RTL.funsig fd = sig ->
      Mem.free m stk 0 (RTL.fn_stacksize f) = Some m' ->
      forall b s2,
        match_states b (RTL.State s f (Vptr stk Integers.Ptrofs.zero) pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof (option bb) measure b' b) /\
            match_states b' (RTL.Callstate s fd rs ## args m') s2'.
  Proof.
    intros * H H0 H1 H2.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify;
    apply sim_plus.
    inv H0. simplify.
    unfold valid_succ in H7; simplify.
    exploit find_function_translated; eauto; simplify.
    do 3 econstructor. apply plus_one. econstructor.
    eassumption. eapply BB; [| eassumption ].
    econstructor; econstructor; eauto.
    setoid_rewrite <- H1.
    econstructor; eauto.
    apply sig_transl_function; auto.
    assert (fn_stacksize tf = RTL.fn_stacksize f).
    { unfold transl_function in TF.
      repeat (destruct_match; try discriminate; []).
      inv TF; auto. }
    rewrite H5. eassumption.

    econstructor; try eassumption.
  Qed.

  Lemma transl_Ibuiltin_correct:
    forall s f sp pc rs m ef args res pc' vargs t vres m',
      (RTL.fn_code f) ! pc = Some (RTL.Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r : positive => rs # r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      forall b s2,
        match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 t s2' \/ star step tge s2 t s2' /\ ltof _ measure b' b) /\
            match_states b' (RTL.State s f sp pc' (regmap_setres res vres rs) m') s2'.
  Proof.
    intros * H H0 H1.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify.
    eapply sim_plus.
    unfold valid_succ in H8; simplify.
    do 3 econstructor. apply plus_one. econstructor.
    eassumption. eapply BB; [| eassumption ].
    econstructor; econstructor; eauto.
    setoid_rewrite <- H3. econstructor; eauto.
    eauto using eval_builtin_args_preserved, symbols_preserved.
    eauto using external_call_symbols_preserved, senv_preserved.

    econstructor; try eassumption. eauto.
    eapply star_refl.
    unfold sem_extrap. intros. setoid_rewrite H5 in H8. crush.
  Qed.

  Lemma transl_entrypoint_exists :
    forall f tf,
      transl_function f = OK tf ->
      exists b, (fn_code tf) ! (fn_entrypoint tf) = Some b.
  Proof. Admitted.

  Lemma transl_match_code :
    forall f tf,
      transl_function f = OK tf ->
      match_code f.(RTL.fn_code) tf.(fn_code).
  Proof. Admitted.

  Lemma init_regs_equiv :
    forall b a, init_regs a b = RTL.init_regs a b.
  Proof. induction b; crush. Qed.

  Lemma transl_initcall_correct:
    forall s f args m m' stk,
      Mem.alloc m 0 (RTL.fn_stacksize f) = (m', stk) ->
      forall b s2,
        match_states b (RTL.Callstate s (Internal f) args m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof (option bb) measure b' b) /\
            match_states b'
                         (RTL.State s f (Vptr stk Integers.Ptrofs.zero) (RTL.fn_entrypoint f) (RTL.init_regs args (RTL.fn_params f)) m') s2'.
  Proof.
    intros * H.
    inversion 1; subst; simplify.
    monadInv TF. inv H0.
    pose proof (transl_match_code _ _ EQ).
    pose proof (transl_entrypoint_exists _ _ EQ).
    simplify.
    exploit transl_entrypoint_exists; eauto; simplify.
    destruct x0.
    apply sim_plus. do 3 econstructor.
    assert (fn_stacksize x = RTL.fn_stacksize f).
    { unfold transl_function in EQ.
      repeat (destruct_match; try discriminate; []).
      inv EQ; auto. }
    apply plus_one. econstructor; eauto.
    rewrite H1. eauto.

    assert (fn_entrypoint x = RTL.fn_entrypoint f).
    { unfold transl_function in EQ.
      repeat (destruct_match; try discriminate; []).
      inv EQ; auto. }
    assert (fn_params x = RTL.fn_params f).
    { unfold transl_function in EQ.
      repeat (destruct_match; try discriminate; []).
      inv EQ; auto. }
    unfold match_code in H0.
    pose proof (H0 _ _ H3).
    econstructor; eauto.
    rewrite <- H1. eauto.
    rewrite H1.
    rewrite init_regs_equiv. rewrite H4. eapply star_refl.
    unfold sem_extrap; intros.
    setoid_rewrite H2 in H7; simplify.
    rewrite H4. eauto.
  Qed.

  Lemma transl_externalcall_correct:
    forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      forall b s2,
        match_states b (RTL.Callstate s (External ef) args m) s2 ->
        exists b' s2',
          (plus step tge s2 t s2' \/ star step tge s2 t s2' /\ ltof (option bb) measure b' b) /\
            match_states b' (RTL.Returnstate s res m') s2'.
  Proof.
    intros * H.
    inversion 1; subst; simplify.
    inv TF.
    apply sim_plus. do 3 econstructor.
    apply plus_one.
    econstructor; eauto using external_call_symbols_preserved, senv_preserved.
    econstructor; eauto.
  Qed.

  Lemma transl_returnstate_correct:
    forall res f sp pc rs s vres m b s2,
      match_states b (RTL.Returnstate (RTL.Stackframe res f sp pc rs :: s) vres m) s2 ->
      exists b' s2',
        (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof (option bb) measure b' b) /\
          match_states b' (RTL.State s f sp pc rs # res <- vres m) s2'.
  Proof.
    intros.
    inv H. inv STK. inv H1.
    pose proof (transl_match_code _ _ TF).
    unfold valid_succ in VALID. simplify.
    unfold match_code in H.
    pose proof (H _ _ H0).
    apply sim_plus. do 3 econstructor. apply plus_one.
    constructor. constructor; eauto using star_refl.
    unfold sem_extrap; intros.
    setoid_rewrite H0 in H4; crush.
  Qed.

  Lemma transl_Icond_correct:
    forall s f sp pc rs m cond args ifso ifnot b pc',
      (RTL.fn_code f) ! pc = Some (RTL.Icond cond args ifso ifnot) ->
      Op.eval_condition cond rs ## args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      forall b0 s2,
        match_states b0 (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof (option bb) measure b' b0) /\
            match_states b' (RTL.State s f sp pc' rs m) s2'.
  Proof.
    intros * H H0 H1.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify;
    apply sim_plus.
    inv H0. simplify.
    unfold valid_succ in *; simplify.
    destruct b.
    { do 3 econstructor. apply plus_one.
      econstructor; eauto. eapply BB.
      econstructor; constructor. auto.
      setoid_rewrite <- H1. econstructor; eauto.
      constructor; eauto using star_refl.
      unfold sem_extrap; intros. setoid_rewrite H4 in H8. inv H8. auto.
    }
    { do 3 econstructor. apply plus_one.
      econstructor; eauto. eapply BB.
      econstructor; constructor. auto.
      setoid_rewrite <- H1. econstructor; eauto.
      constructor; eauto using star_refl.
      unfold sem_extrap; intros. setoid_rewrite H0 in H8. inv H8. auto.
    }
  Qed.

  Lemma transl_Ijumptable_correct:
    forall s f sp pc rs m arg tbl n pc',
      (RTL.fn_code f) ! pc = Some (RTL.Ijumptable arg tbl) ->
      rs # arg = Vint n ->
      list_nth_z tbl (Integers.Int.unsigned n) = Some pc' ->
      forall b s2,
        match_states b (RTL.State s f sp pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof (option bb) measure b' b) /\
            match_states b' (RTL.State s f sp pc' rs m) s2'.
  Proof.
    intros * H H0 H1.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify;
    apply sim_plus.
    eapply Forall_forall with (x:=pc') in H8; eauto using list_nth_z_in.
    unfold valid_succ in H8; simplify.
    do 3 econstructor. apply plus_one.
    econstructor; eauto. eapply BB.
    econstructor; constructor. auto.
    setoid_rewrite <- H3. econstructor; eauto.

    constructor; eauto using star_refl.
    unfold sem_extrap; intros. setoid_rewrite H5 in H8. inv H8. auto.
  Qed.

  Lemma transl_Ireturn_correct:
    forall s f stk pc rs m or m',
      (RTL.fn_code f) ! pc = Some (RTL.Ireturn or) ->
      Mem.free m stk 0 (RTL.fn_stacksize f) = Some m' ->
      forall b s2,
        match_states b (RTL.State s f (Vptr stk Integers.Ptrofs.zero) pc rs m) s2 ->
        exists b' s2',
          (plus step tge s2 E0 s2' \/ star step tge s2 E0 s2' /\ ltof (option bb) measure b' b) /\
            match_states b' (RTL.Returnstate s (regmap_optget or Vundef rs) m') s2'.
  Proof.
    intros * H H0.
    inversion 1; subst; simplify.
    unfold match_code in *.
    match goal with H: match_block _ _ _ _ _ |- _ => inv H end; simplify;
    apply sim_plus.
    assert (fn_stacksize tf = RTL.fn_stacksize f).
    { unfold transl_function in TF.
      repeat (destruct_match; try discriminate; []).
      inv TF; auto. }
    do 3 econstructor. apply plus_one. econstructor; eauto.
    eapply BB.
    econstructor; constructor. auto.
    setoid_rewrite <- H2. constructor.
    rewrite H4. eauto.
    constructor; eauto.
  Qed.

  Lemma transl_correct:
    forall s1 t s1',
      RTL.step ge s1 t s1' ->
      forall b s2, match_states b s1 s2 ->
        exists b' s2',
          (plus step tge s2 t s2' \/
             (star step tge s2 t s2' /\ ltof _ measure b' b))
          /\ match_states b' s1' s2'.
  Proof.
    induction 1.
    - eauto using transl_Inop_correct.
    - eauto using transl_Iop_correct.
    - eauto using transl_Iload_correct.
    - eauto using transl_Istore_correct.
    - eauto using transl_Icall_correct.
    - eauto using transl_Itailcall_correct.
    - eauto using transl_Ibuiltin_correct.
    - eauto using transl_Icond_correct.
    - eauto using transl_Ijumptable_correct.
    - eauto using transl_Ireturn_correct.
    - eauto using transl_initcall_correct.
    - eauto using transl_externalcall_correct.
    - eauto using transl_returnstate_correct.
  Qed.

  Theorem transf_program_correct:
    forward_simulation (RTL.semantics prog) (RTLBlock.semantics tprog).
  Proof using TRANSL.
    eapply (Forward_simulation
              (L1:=RTL.semantics prog)
              (L2:=RTLBlock.semantics tprog)
              (ltof _ measure) match_states).
    constructor.
    - apply well_founded_ltof.
    - eauto using transl_initial_states.
    - intros; eapply transl_final_states; eauto.
    - eapply transl_correct.
    - apply senv_preserved.
  Qed.

End CORRECTNESS.
