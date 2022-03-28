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

Require Import vericert.hls.RTLBlockInstr.

(*|
========
RTLBlock
========
|*)

Definition bb := instr.

Definition bblock := @bblock bb.
Definition code := @code bb.
Definition function := @function bb.
Definition fundef := @fundef bb.
Definition program := @program bb.
Definition funsig := @funsig bb.
Definition stackframe := @stackframe bb.
Definition state := @state bb.

Definition genv := @genv bb.

(*|
Semantics
=========

We first describe the semantics by assuming a global program environment with
type ~genv~ which was declared earlier.
|*)

Section RELSEM.

  Context (ge: genv).

(*|
Instruction list step
---------------------

The ``step_instr_list`` definition describes the execution of a list of
instructions in one big step, inductively traversing the list of instructions
and applying the ``step_instr``.
|*)

  Inductive step_instr_list:
    val -> instr_state -> list instr -> instr_state -> Prop :=
  | exec_RBcons:
    forall state i state' state'' instrs sp,
      step_instr ge sp state i state' ->
      step_instr_list sp state' instrs state'' ->
      step_instr_list sp state (i :: instrs) state''
  | exec_RBnil:
    forall state sp,
      step_instr_list sp state nil state.

(*|
Top-level step
--------------

The step function itself then uses this big step of the list of instructions to
then show a transition from basic block to basic block.
|*)

  Variant step: state -> trace -> state -> Prop :=
  | exec_bblock:
    forall s f sp pc rs rs' m m' t s' bb pr pr',
      f.(fn_code)!pc = Some bb ->
      step_instr_list sp (mk_instr_state rs pr m) bb.(bb_body)
                         (mk_instr_state rs' pr' m') ->
      step_cf_instr ge (State s f sp pc nil rs' pr' m') bb.(bb_exit) t s' ->
      step (State s f sp pc nil rs pr m) t s'
  | exec_function_internal:
    forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
           E0 (State s f
                     (Vptr stk Ptrofs.zero)
                     f.(fn_entrypoint)
                         nil
                         (init_regs args f.(fn_params))
                         (PMap.init false)
                         m')
  | exec_function_external:
    forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
           t (Returnstate s res m')
  | exec_return:
    forall res f sp pc rs s vres m pr,
      step (Returnstate (Stackframe res f sp pc rs pr :: s) vres m)
           E0 (State s f sp pc nil (rs#res <- vres) pr m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->
    initial_state p (Callstate nil f nil m0).

Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
    final_state (Returnstate nil (Vint r) m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
