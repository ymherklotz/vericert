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

Variant transl_code_spec (c: RTL.code) (tc: code) (x x': node): Prop :=
| transl_code_standard_bb :
  forall i i',
    c ! x = Some i ->
    find_instr_spec tc x i x' i' ->
    Is_true (check_instr x i i') ->
    transl_code_spec c tc x x'
| transl_code_standard_cf :
  forall i i' il,
    c ! x = Some i ->
    tc ! x' = Some il ->
    find_instr_spec tc x i x' i' ->
    Is_true (check_cf_instr_body i i') ->
    Is_true (check_cf_instr i il.(bb_exit)) ->
    transl_code_spec c tc x x'
.

(*|
Matches the basic block that should be present in the state.  This simulates the
small step execution of the basic block from the big step semantics that are
currently present.

Why does it not need to find the pc' value using ``find_block``?

It doesn't have to find the value because it's given as an input, and the
finding is actually done at that higher level already.
|*)

Variant match_bblock (tc: code) (pc pc': node): list instr -> Prop :=
| match_bblock_intro :
  forall bb cf,
    tc ! pc' = Some (mk_bblock bb cf) ->
    match_bblock tc pc pc' (list_drop (offset pc pc') bb).

Variant match_stackframe : RTL.stackframe -> stackframe -> Prop :=
| match_stackframe_init :
  forall res f tf sp pc pc' rs
    (TF: transl_function f = OK tf)
    (PC: transl_code_spec f.(RTL.fn_code) tf.(fn_code) pc pc'),
    match_stackframe (RTL.Stackframe res f sp pc rs)
                     (Stackframe res tf sp pc' rs (PMap.init false)).

(*|
The ``match_states`` predicate defines how to find the correct ``bb`` that
should be executed, as well as the value of ``pc``.
|*)

Variant match_states : RTL.state -> RTLBlock.state -> Prop :=
| match_state :
  forall stk stk' f tf sp pc rs m pc' bb
         (TF: transl_function f = OK tf)
         (PC: transl_code_spec f.(RTL.fn_code) tf.(fn_code) pc pc')
         (STK: Forall2 match_stackframe stk stk')
         (BB: match_bblock tf.(fn_code) pc pc' bb),
    match_states (RTL.State stk f sp pc rs m)
                 (State stk' tf sp pc' bb rs (PMap.init false) m)
| match_callstate :
  forall cs cs' f tf args m
    (TF: transl_fundef f = OK tf)
    (STK: Forall2 match_stackframe cs cs'),
    match_states (RTL.Callstate cs f args m) (Callstate cs' tf args m)
| match_returnstate :
  forall cs cs' v m
    (STK: Forall2 match_stackframe cs cs'),
    match_states (RTL.Returnstate cs v m) (Returnstate cs' v m).

Definition match_prog (p: RTL.program) (tp: RTLBlock.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Section CORRECTNESS.

  Context (prog : RTL.program).
  Context (tprog : RTLBlock.program).

  Context (TRANSL : match_prog prog tprog).

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof using TRANSL. intros; eapply (Genv.senv_transf_partial TRANSL). Qed.
  #[local] Hint Resolve senv_preserved : rtlgp.

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
  Proof
    (Genv.find_funct_ptr_transf_partial TRANSL).

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

  Lemma transl_initial_states :
    forall s1, RTL.initial_state prog s1 ->
      exists s2, RTLBlock.initial_state tprog s2 /\ match_states s1 s2.
  Proof using TRANSL.
    induction 1.
    exploit function_ptr_translated; eauto. intros [tf [A B]].
    econstructor. simplify. econstructor.
    apply (Genv.init_mem_transf_partial TRANSL); eauto.
    replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
    symmetry; eapply Linking.match_program_main; eauto. eauto.
    erewrite sig_transl_function; eauto. constructor. auto. auto.
  Qed.

  Lemma transl_final_states :
    forall s1 s2 r,
      match_states s1 s2 ->
      RTL.final_state s1 r ->
      RTLBlock.final_state s2 r.
  Proof using.
    inversion 2; crush. subst. inv H. inv STK. econstructor.
  Qed.

  Lemma transl_Inop_correct:
    forall s f sp pc rs m pc',
      (RTL.fn_code f) ! pc = Some (RTL.Inop pc') ->
      forall s2, match_states (RTL.State s f sp pc rs m) s2 ->
        exists s2', Smallstep.plus step tge s2 Events.E0 s2'
               /\ match_states (RTL.State s f sp pc' rs m) s2'.
  Proof.
    intros s f sp pc rs m pc' H.
  Admitted.

  Lemma transl_Iop_correct:
    forall s f sp pc rs m op args res pc' v,
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res pc') ->
      Op.eval_operation ge sp op rs##args m = Some v ->
      forall s2, match_states (RTL.State s f sp pc rs m) s2 ->
        exists s2', Smallstep.plus step tge s2 Events.E0 s2'
               /\ match_states (RTL.State s f sp pc' (Registers.Regmap.set res v rs) m) s2'.
  Proof.
    intros s f sp pc rs m op args res pc' v H H0.
  Admitted.

  Lemma transl_Iload_correct:
    forall s f sp pc rs m chunk addr args dst pc' a v,
      (RTL.fn_code f) ! pc = Some (RTL.Iload chunk addr args dst pc') ->
      Op.eval_addressing ge sp addr rs##args = Some a ->
      Memory.Mem.loadv chunk m a = Some v ->
      forall s2, match_states (RTL.State s f sp pc rs m) s2 ->
        exists s2', Smallstep.plus step tge s2 Events.E0 s2'
               /\ match_states (RTL.State s f sp pc' (Registers.Regmap.set dst v rs) m) s2'.
  Proof.
    intros s f sp pc rs m chunk addr args dst pc' a v H H0 H1.
  Admitted.

  Lemma transl_correct:
    forall s1 t s1',
      RTL.step ge s1 t s1' ->
      forall s2, match_states s1 s2 ->
        exists s2', Smallstep.plus step tge s2 t s2' /\ match_states s1' s2'.
  Proof.
    induction 1.
    - eauto using transl_Inop_correct.
    - eauto using transl_Iop_correct.
    - eauto using transl_Iload_correct.
  Admitted.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog)
                                 (RTLBlock.semantics tprog).
  Proof using TRANSL.
    eapply Smallstep.forward_simulation_plus.
    apply senv_preserved.
    eauto using transl_initial_states.
    eapply transl_final_states.
    eauto using transl_correct.
  Qed.

End CORRECTNESS.
