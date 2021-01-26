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

Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Linking.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLPargen.

Definition match_prog (prog : RTLBlock.program) (tprog : RTLPar.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.

Inductive match_stackframes: RTLBlock.stackframe -> RTLPar.stackframe -> Prop :=
| match_stackframe:
    forall f tf res sp pc rs,
      transl_function f = OK tf ->
      match_stackframes (RTLBlock.Stackframe res f sp pc rs)
                        (RTLPar.Stackframe res tf sp pc rs).

Inductive match_states: RTLBlock.state -> RTLPar.state -> Prop :=
| match_state:
    forall sf f sp pc rs mem sf' tf
      (TRANSL: transl_function f = OK tf)
      (STACKS: list_forall2 match_stackframes sf sf'),
      match_states (RTLBlock.State sf f sp pc rs mem)
                   (RTLPar.State sf' tf sp pc rs mem)
| match_block:
    forall sf f sp bb bb' rs mem sf' tf
    (TRANSL: transl_function f = OK tf)
    (STACKS: list_forall2 match_stackframes sf sf')
    (BB: schedule_oracle bb bb' = true),
    match_states (RTLBlock.Block sf f sp bb rs mem)
                 (RTLPar.Block sf' tf sp bb' rs mem)
| match_returnstate:
    forall stack stack' v mem
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (RTLBlock.Returnstate stack v mem)
                   (RTLPar.Returnstate stack' v mem)
| match_initial_call:
    forall stack stack' f tf args m
      (TRANSL: transl_fundef f = OK tf)
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (RTLBlock.Callstate stack f args m)
      (RTLPar.Callstate stack' tf args m).

Section CORRECTNESS.

  Context (prog: RTLBlock.program) (tprog : RTLPar.program).
  Context (TRANSL: match_prog prog tprog).

  Let ge : RTLBlock.genv := Globalenvs.Genv.globalenv prog.
  Let tge : RTLPar.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. intros. eapply (Genv.find_symbol_match TRANSL). Qed.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: RTLBlock.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: RTLBlock.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof
    (Genv.senv_transf_partial TRANSL).

  Theorem transl_step_correct :
    forall (S1 : RTLBlock.state) t S2,
      RTLBlock.step ge S1 t S2 ->
      forall (R1 : RTLPar.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus RTLPar.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    Ltac t :=
      match goal with
      | [ H: context[match_states _ _] |- _ ] => inv H
      | [ H: transl_function ?f = OK _ |- _ ] =>
        let H2 := fresh "TRANSL" in
        learn H as H2;
        unfold transl_function in H2;
        destruct (check_scheduled_trees (RTLBlock.fn_code f) (fn_code (schedule f))) eqn:?;
                 [| discriminate ]; inv H2
      | [ H: context[check_scheduled_trees] |- _ ] =>
        eapply check_scheduled_trees_correct in H; [| solve [ eauto ] ]
      | [ H: exists _, _ |- _ ] => inv H
      end.

    induction 1; simplify; repeat t; simplify.

    - repeat econstructor; eauto.
    - admit.
    - repeat econstructor; eauto.
