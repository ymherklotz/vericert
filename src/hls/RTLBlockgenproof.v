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
|*)

Parameter find_block_spec : code -> node -> node -> Prop.

Definition find_instr_spec (c: code) (n: node) (i: RTL.instruction)
           (n': node) (i': instr) :=
    find_block_spec c n n'
    /\ exists il,
      c ! n' = Some il
      /\ nth_error il.(bb_body) (Pos.to_nat n - Pos.to_nat n')%nat = Some i'.

(*|
.. index::
   pair: semantics; transl_code_spec

Translation Specification
-------------------------

This specification should describe the translation that the unverified
transformation performs.  This should be proven from the validation of the
transformation.
|*)

Variant transl_code_spec (c: RTL.code) (tc: code) :=
| transl_code_standard_bb :
  forall x x' i i',
    c ! x = Some i ->
    find_instr_spec tc x i x' i' ->
    Is_true (check_instr x i i') ->
    transl_code_spec c tc
| transl_code_standard_cf :
  forall x x' i i' il,
    c ! x = Some i ->
    tc ! x' = Some il ->
    find_instr_spec tc x i x' i' ->
    Is_true (check_cf_instr_body i i') ->
    Is_true (check_cf_instr i il.(bb_exit)) ->
    transl_code_spec c tc
.

Lemma transl_function_correct :
  forall f tf,
    transl_function f = OK tf ->
    transl_code_spec f.(RTL.fn_code) tf.(fn_code).
Proof. Admitted.

Variant match_stackframe : RTL.stackframe -> stackframe -> Prop :=
| match_stackframe_init :
  forall a b,
    match_stackframe a b.

Variant match_states : RTL.state -> RTLBlock.state -> Prop :=
| match_state :
  forall stk stk' f tf sp pc rs m pc' ps bb
         (TF: transl_function f = OK tf)
         (PC: find_block_spec tf.(fn_code) pc pc')
         (STK: Forall2 match_stackframe stk stk'),
    match_states (RTL.State stk f sp pc rs m)
                 (State stk' tf sp pc' bb rs ps m).

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

  Lemma transl_initial_states :
    forall s1 : Smallstep.state (RTL.semantics prog),
      Smallstep.initial_state (RTL.semantics prog) s1 ->
      exists s2 : Smallstep.state (semantics tprog),
        Smallstep.initial_state (semantics tprog) s2 /\ match_states s1 s2.
  Proof. Admitted.

  Lemma transl_final_states :
    forall (s1 : Smallstep.state (RTL.semantics prog))
           (s2 : Smallstep.state (semantics tprog))
           (r : Integers.Int.int),
      match_states s1 s2 ->
      Smallstep.final_state (RTL.semantics prog) s1 r ->
      Smallstep.final_state (semantics tprog) s2 r.
  Proof. Admitted.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog)
                                 (RTLBlock.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus.
    apply senv_preserved.
    admit.
    eauto using transl_final_states.
    Admitted.

End CORRECTNESS.
