(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

From vericert Require Import HTLgenproof.

From compcert.common Require Import
    Errors
    Linking.

From compcert.lib Require Import
    Coqlib.

From compcert.backend Require
    Selection
    RTL
    RTLgen
    Tailcall
    Inlining
    Renumber
    Constprop
    CSE
    Deadcode
    Unusedglob.

From compcert.cfrontend Require
    Csyntax
    SimplExpr
    SimplLocals
    Cshmgen
    Cminorgen.

From compcert.driver Require
    Compiler.

From vericert Require
     Verilog
     Veriloggen
     Veriloggenproof
     HTLgen
     RTLBlock
     RTLBlockgen.

From compcert Require Import Smallstep.

Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_HTL: HTL.program -> unit.

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Notation "a @@@ b" :=
   (Compiler.apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
  (Compiler.apply_total _ _ a b) (at level 50, left associativity).

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

Definition transf_backend (r : RTL.program) : res Verilog.program :=
  OK r
  @@@ Inlining.transf_program
  @@ print (print_RTL 1)
  @@@ HTLgen.transl_program
  @@ print print_HTL
  @@ Veriloggen.transl_program.

Definition transf_hls (p : Csyntax.program) : res Verilog.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@ print (print_RTL 0)
  @@@ transf_backend.

Definition transf_hls_temp (p : Csyntax.program) : res RTLBlock.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@ Renumber.transf_program
  @@ print (print_RTL 0)
  @@@ RTLBlockgen.transl_program.

Local Open Scope linking_scope.

Definition CompCert's_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass Inliningproof.match_prog
  ::: (@mkpass _ _ HTLgenproof.match_prog (HTLgenproof.TransfHTLLink HTLgen.transl_program))
  ::: mkpass Veriloggenproof.match_prog
  ::: pass_nil _.

Definition match_prog: Csyntax.program -> Verilog.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

Theorem transf_hls_match:
  forall p tp,
    transf_hls p = OK tp ->
    match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_hls in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  rewrite ! compose_print_identity in T.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_backend in T. simpl in T. rewrite ! compose_print_identity in T.
  destruct (Inlining.transf_program p6) as [p7|e] eqn:P7; simpl in T; try discriminate.
  destruct (HTLgen.transl_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Veriloggen.transl_program p8) in *.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply Inliningproof.transf_program_match; auto.
  exists p8; split. apply HTLgenproof.transf_program_match; auto.
  exists p9; split. apply Veriloggenproof.transf_program_match; auto.
  inv T. reflexivity.
Qed.

Remark forward_simulation_identity:
  forall sem, forward_simulation sem sem.
Proof.
  intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Theorem cstrategy_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Cstrategy.semantics p) (Verilog.semantics tp)
  /\ backward_simulation (atomic (Cstrategy.semantics p)) (Verilog.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation (Cstrategy.semantics p) (Verilog.semantics p9)).
  {
  eapply compose_forward_simulations.
    eapply SimplExprproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply HTLgenproof.transf_program_correct. eassumption.
  eapply Veriloggenproof.transf_program_correct; eassumption.
  }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Verilog.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Verilog.semantics_determinate.
Qed.

Theorem c_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  backward_simulation (Csem.semantics p) (Verilog.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Verilog.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (proj2 (cstrategy_semantic_preservation _ _ H)).
Qed.

Theorem transf_c_program_correct:
  forall p tp,
  transf_hls p = OK tp ->
  backward_simulation (Csem.semantics p) (Verilog.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_hls_match; auto.
Qed.

Theorem separate_transf_c_program_correct:
  forall c_units verilog_units c_program,
  nlist_forall2 (fun cu tcu => transf_hls cu = OK tcu) c_units verilog_units ->
  link_list c_units = Some c_program ->
  exists verilog_program,
      link_list verilog_units = Some verilog_program
   /\ backward_simulation (Csem.semantics c_program) (Verilog.semantics verilog_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units verilog_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_hls_match; auto. }
  assert (exists verilog_program, link_list verilog_units = Some verilog_program
                                  /\ match_prog c_program verilog_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (verilog_program & P & Q).
  exists verilog_program; split; auto. apply c_semantic_preservation; auto.
Qed.
