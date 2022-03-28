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
|*)

Require compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.

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

Parameter find_block_spec : code -> node -> RTL.instruction -> node -> Prop.

Definition find_instr_spec (c: code) (n: node) (i: RTL.instruction) (n': node) (i': instr) :=
    find_block_spec c n i n'
    /\ exists il,
      c ! n' = Some il
      /\ nth_error il.(bb_body) (Pos.to_nat n - Pos.to_nat n')%nat = Some i'.

Inductive transl_code_spec (c: RTL.code) (tc: code) :=
| transl_code_standard_bb :
  forall x x' i i',
    c ! x = Some i ->
    find_instr_spec tc x i x' i' ->
    check_instr x i i' = true ->
    transl_code_spec c tc
| transl_code_standard_goto :
  forall
.

Inductive match_states : RTL.state -> RTLBlock.state -> Prop :=
| match_state :
  forall stk f tf sp pc rs m
         (TF: transl_function f = OK tf),
    match_states (RTL.State stk f sp pc rs m)
                 (State stk tf sp (find_block max n i) rs m).

Section CORRECTNESS.

  Context (prog : RTL.program).
  Context (tprog : RTLBlock.program).

  Context (TRANSL : match_prog prog tprog).

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog) (RTLBlock.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus; eauto with htlproof.
    apply senv_preserved.

End CORRECTNESS.
*)
