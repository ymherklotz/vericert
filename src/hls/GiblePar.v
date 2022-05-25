(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.
Require Import vericert.hls.Gible.

(*|
========
RTLBlock
========
|*)

Module BB <: BlockType.

  Definition t := list (list (list instr)).

  Section RELSEM.

    Context {A B: Type} (ge: Genv.t A B).

    Definition step_instr_list := step_list (step_instr ge).
    Definition step_instr_seq := step_list step_instr_list.
    Definition step_instr_block := step_list step_instr_seq.

(*|
Instruction list step
---------------------

The ``step_instr_list`` definition describes the execution of a list of
instructions in one big step, inductively traversing the list of instructions
and applying the ``step_instr``.

This is simply using the high-level function ``step_list``, which is a general
function that can execute lists of things, given their execution rule.
|*)

    Definition step := step_instr_block.

  End RELSEM.

  Definition max_reg (m : positive) (pc : node) (bb : t) :=
    fold_left
      (fun x l => fold_left (fun x' l' => fold_left max_reg_instr l' x') l x)
      bb m.

  Definition length : t -> nat := @length (list (list instr)).

End BB.

Module GiblePar := Gible(BB).
