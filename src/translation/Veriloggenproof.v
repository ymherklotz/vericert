(*
 * CoqUp: Verified high-level synthesis.
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

From compcert Require Import Smallstep Linking.
From coqup Require Import Veriloggen.
From coqup Require HTL Verilog.

Definition match_prog (prog : HTL.program) (tprog : Verilog.program) :=
  match_program (fun cu f tf => tf = transl_fundef f) eq prog tprog.

Lemma transf_program_match:
  forall prog, match_prog prog (transl_program prog).
Proof.
  intros. eapply match_transform_program_contextual. auto.
Qed.

Inductive match_stacks : list HTL.stackframe -> list Verilog.stackframe -> Prop :=
| match_stack :
    forall res m pc reg_assoc arr_assoc hstk vstk,
      match_stacks hstk vstk ->
      match_stacks (HTL.Stackframe res m pc reg_assoc arr_assoc :: hstk)
                   (Verilog.Stackframe res (transl_module m) pc
                                       reg_assoc arr_assoc :: vstk)
| match_stack_nil : match_stacks nil nil.

Inductive match_states : HTL.state -> Verilog.state -> Prop :=
| match_state :
    forall m st reg_assoc arr_assoc hstk vstk,
      match_stacks hstk vstk ->
      match_states (HTL.State hstk m st reg_assoc arr_assoc)
                   (Verilog.State vstk (transl_module m) st reg_assoc arr_assoc)
| match_returnstate :
    forall v hstk vstk,
      match_stacks hstk vstk ->
      match_states (HTL.Returnstate hstk v) (Verilog.Returnstate vstk v)
| match_initial_call :
    forall m,
      match_states (HTL.Callstate nil m nil) (Verilog.Callstate nil (transl_module m) nil).

Section CORRECTNESS.

  Variable prog: HTL.program.
  Variable tprog: Verilog.program.

  Hypothesis TRANSL : match_prog prog tprog.

  Let ge : HTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : Verilog.genv := Globalenvs.Genv.globalenv tprog.

  Theorem transl_step_correct:
    forall (S1 : HTL.state) t S2,
      HTL.step ge S1 t S2 ->
      forall (R1 : Verilog.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus Verilog.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; intros R1 MSTATE.

  Theorem transf_program_correct:
    forward_simulation (HTL.semantics prog) (Verilog.semantics tprog).


End CORRECTNESS.

