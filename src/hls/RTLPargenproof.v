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
Require Import compcert.common.Linking.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPargen.

Definition match_prog (prog : RTLBlock.program) (tprog : RTLPar.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.

Inductive match_stackframes: RTLBlock.stackframe -> RTLPar.stackframe -> Prop :=
| match_stackframe:
    forall f tf res sp pc rs,
      transl_function f = OK tf ->
      match_stackframes (Stackframe res f sp pc rs)
                        (Stackframe res tf sp pc rs).

Inductive match_states: RTLBlock.state -> RTLPar.state -> Prop :=
| match_state:
    forall sf f sp pc rs mem sf' tf
      (TRANSL: transl_function f = OK tf)
      (STACKS: list_forall2 match_stackframes sf sf'),
      match_states (State sf f sp pc rs mem)
                   (State sf' tf sp pc rs mem)
| match_returnstate:
    forall stack stack' v mem
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (Returnstate stack v mem)
                   (Returnstate stack' v mem)
| match_initial_call:
    forall stack stack' f tf args m
      (TRANSL: transl_fundef f = OK tf)
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (Callstate stack f args m)
                   (Callstate stack' tf args m).

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
  Proof (Genv.senv_transf_partial TRANSL).

  Lemma sig_transl_function:
    forall (f: RTLBlock.fundef) (tf: RTLPar.fundef),
      transl_fundef f = OK tf ->
      funsig tf = funsig f.
  Proof.
    unfold transl_fundef, transf_partial_fundef, transl_function; intros;
    repeat destruct_match; crush;
    match goal with H: OK _ = OK _ |- _ => inv H end; auto.
  Qed.

  Lemma find_function_translated:
    forall ros rs f,
      find_function ge ros rs = Some f ->
      exists tf, find_function tge ros rs = Some tf
                 /\ transl_fundef f = OK tf.
  Proof.
    destruct ros; simplify;
    [ exploit functions_translated; eauto
    | rewrite symbols_preserved; destruct_match;
      try (apply function_ptr_translated); crush ].
  Qed.

  Lemma schedule_oracle_nil:
    forall bb cfi,
      schedule_oracle {| bb_body := nil; bb_exit := cfi |} bb = true ->
      bb_body bb = nil /\ bb_exit bb = cfi.
  Proof.
    unfold schedule_oracle, check_control_flow_instr.
    simplify; repeat destruct_match; crush.
  Qed.

  Lemma schedule_oracle_nil2:
    forall cfi,
      schedule_oracle {| bb_body := nil; bb_exit := cfi |}
                      {| bb_body := nil; bb_exit := cfi |} = true.
  Proof.
    unfold schedule_oracle, check_control_flow_instr.
    simplify; repeat destruct_match; crush.
  Qed.

  Lemma schedule_sem_correct:
    forall bb bb' cfi sp rs m rs' m',
      schedule_oracle {| bb_body := bb; bb_exit := cfi |} {| bb_body := bb'; bb_exit := cfi |} = true ->
      step_instr_list ge sp (InstrState rs m) bb (InstrState rs' m') ->
      step_instr_block tge sp (InstrState rs m) bb' (InstrState rs' m').
  Proof. Admitted.

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
        destruct (check_scheduled_trees (fn_code f) (fn_code (schedule f))) eqn:?;
                 [| discriminate ]; inv H2
      | [ H: context[check_scheduled_trees] |- _ ] =>
        let H2 := fresh "CHECK" in
        learn H as H2;
        eapply check_scheduled_trees_correct in H2; [| solve [eauto] ]
      | [ H: schedule_oracle {| bb_body := nil; bb_exit := _ |} ?bb = true |- _ ] =>
        let H2 := fresh "SCHED" in
        learn H as H2;
        apply schedule_oracle_nil in H2
      | [ H: exists _, _ |- _ ] => inv H
      | _ => progress simplify
      end.

    induction 1; repeat t.

    admit.
    { unfold bind in *. destruct_match; try discriminate. repeat t. inv TRANSL0.
      repeat econstructor; eauto. }
    { inv TRANSL0. repeat econstructor; eauto using Events.external_call_symbols_preserved, symbols_preserved, senv_preserved, Events.E0_right. }
    { inv STACKS. inv H1. repeat econstructor; eauto. }
  Qed.
