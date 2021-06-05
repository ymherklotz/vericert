(*|
.. coq:: none
|*)

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

(*|
==============
Compiler Proof
==============

.. contents:: Table of Contents
   :depth: 2

This is the top-level module of the correctness proof and proves the final backwards simulation correct.

Imports
=======

We first need to import all of the modules that are used in the correctness proof, which includes all of the passes that are performed in Vericert and the CompCert front end.
|*)

Require compcert.backend.Selection.
Require compcert.backend.RTL.
Require compcert.backend.RTLgen.
Require compcert.backend.Tailcall.
Require compcert.backend.Inlining.
Require compcert.backend.Renumber.
Require compcert.backend.Constprop.
Require compcert.backend.CSE.
Require compcert.backend.Deadcode.
Require compcert.backend.Unusedglob.
Require compcert.cfrontend.Csyntax.
Require compcert.cfrontend.SimplExpr.
Require compcert.cfrontend.SimplLocals.
Require compcert.cfrontend.Cshmgen.
Require compcert.cfrontend.Cminorgen.
Require compcert.driver.Compiler.

Require Import compcert.common.Errors.
Require Import compcert.common.Linking.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Coqlib.

Require vericert.hls.Verilog.
Require vericert.hls.Veriloggen.
Require vericert.hls.Veriloggenproof.
Require vericert.hls.Renaming.
Require vericert.hls.HTLgen.
Require vericert.hls.RTLBlock.
Require vericert.hls.RTLBlockgen.
Require vericert.hls.RTLPargen.
Require vericert.hls.HTLPargen.
Require vericert.hls.Pipeline.
Require vericert.hls.IfConversion.
Require vericert.HLSOpts.

Require Import vericert.hls.HTLgenproof.

(*|
Declarations
============

We then need to declare the external OCaml functions used to print out intermediate steps in the compilation, such as ``print_RTL``, ``print_HTL`` and ``print_RTLBlock``.
|*)

Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_HTL: Z -> HTL.program -> unit.
Parameter print_RTLBlock: Z -> RTLBlock.program -> unit.

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

(*|
We also declare some new notation, which is also used in CompCert to combine the monadic results of each pass.
|*)

Notation "a @@@ b" :=
   (Compiler.apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
  (Compiler.apply_total _ _ a b) (at level 50, left associativity).

(*|
As printing is used in the translation but does not change the output, we need to prove that it has no effect so that it can be removed during the proof.
|*)

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(*|
Finally, some optimisation passes are only activated by a flag, which is handled by the following functions for partial and total passes.
|*)

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
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

Lemma match_if_simulation:
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst. apply forward_simulation_identity.
Qed.

(*|
Top-level Translation
---------------------

An optimised transformation function from ``RTL`` to ``Verilog`` can then be defined, which applies the front end compiler optimisations of CompCert to the RTL that is generated and then performs the two Vericert passes from RTL to HTL and then from HTL to Verilog.
|*)

Definition transf_backend (r : RTL.program) : res Verilog.program :=
  OK r
  @@@ Inlining.transf_program
   @@ print (print_RTL 1)
   @@ Renumber.transf_program
   @@ print (print_RTL 2)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 4)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 6)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 7)
  @@@ HTLgen.transl_program
   @@ print (print_HTL 1)
  @@@ Renaming.transf_program
   @@ print (print_HTL 2)
  @@@ Veriloggen.transl_program.

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

(*|
.. coq:: none
|*)

Definition transf_hls_temp (p : Csyntax.program) : res Verilog.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@@ Inlining.transf_program
   @@ print (print_RTL 1)
   @@ Renumber.transf_program
   @@ print (print_RTL 2)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 4)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 6)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 7)
  @@@ RTLBlockgen.transl_program
   @@ print (print_RTLBlock 1)
   @@ total_if HLSOpts.optim_if_conversion IfConversion.transf_program
   @@ print (print_RTLBlock 2)
  @@@ RTLPargen.transl_program
  @@@ HTLPargen.transl_program
   @@ print (print_HTL 1)
  @@@ Veriloggen.transl_program.

(*|
Correctness Proof
=================

Finally, the top-level definition for all the passes is defined, which combines the ``match_prog`` predicates of each translation pass from C until Verilog.
|*)

Local Open Scope linking_scope.

Definition verilog_transflink : TransfLink Veriloggenproof.match_prog.
Admitted.

Definition CompCert's_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: (@mkpass _ _ HTLgenproof.match_prog (HTLgenproof.TransfHTLLink HTLgen.transl_program))
  ::: (@mkpass _ _ Veriloggenproof.match_prog verilog_transflink)
  ::: pass_nil _.

(*|
These passes are then composed into a larger, top-level ``match_prog`` predicate which matches a C program directly with a Verilog program.
|*)

Definition match_prog: Csyntax.program -> Verilog.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

(*|
We then need to prove that this predicate holds, assuming that the translation is performed using the ``transf_hls`` function declared above.
|*)

Theorem transf_hls_match:
  forall p tp,
    transf_hls p = OK tp ->
    match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_hls, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  rewrite ! compose_print_identity in T.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_backend, time in T. simpl in T. rewrite ! compose_print_identity in T.
  destruct (Inlining.transf_program p6) as [p7|e] eqn:P7; simpl in T; try discriminate.
  set (p8 := Renumber.transf_program p7) in *.
  set (p9 := total_if Compopts.optim_constprop Constprop.transf_program p8) in *.
  set (p10 := total_if Compopts.optim_constprop Renumber.transf_program p9) in *.
  destruct (partial_if Compopts.optim_CSE CSE.transf_program p10) as [p11|e] eqn:P11; simpl in T; try discriminate.
  destruct (partial_if Compopts.optim_redundancy Deadcode.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (HTLgen.transl_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Veriloggen.transl_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply Inliningproof.transf_program_match; auto.
  exists p8; split. apply Renumberproof.transf_program_match; auto.
  exists p9; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p10; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p11; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p13; split. apply Unusedglobproof.transf_program_match; auto.
  exists p14; split. apply HTLgenproof.transf_program_match; auto.
  exists p15; split. (*apply Veriloggenproof.transf_program_match; auto.
  inv T. reflexivity.*)
Admitted.

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
  assert (F: forward_simulation (Cstrategy.semantics p) (Verilog.semantics p15)).
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
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
  eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply HTLgenproof.transf_program_correct. eassumption.
  (* eapply Veriloggenproof.transf_program_correct; eassumption. *)
  admit.
  }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Verilog.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Verilog.semantics_determinate.
Admitted.

(*|
Backward Simulation
-------------------

The following theorem is a *backward simulation* between the C and Verilog, which proves the semantics preservation of the translation.  We can assume that the C and Verilog programs match, as we have proven previously in ``transf_hls_match`` that our translation implies that the ``match_prog`` predicate will hold.
|*)

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

(*|
We can then use ``transf_hls_match`` to prove the backward simulation where the assumption is that the translation is performed using the ``transf_hls`` function and that it succeeds.
|*)

Theorem transf_c_program_correct:
  forall p tp,
  transf_hls p = OK tp ->
  backward_simulation (Csem.semantics p) (Verilog.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_hls_match; auto.
Qed.

(*|
The final theorem of the semantic preservation of the translation of separate translation units can also be proven correct, however, this is only because the translation fails if more than one translation unit is passed to Vericert at the moment.
|*)

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
