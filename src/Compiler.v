(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2019-2022 Yann Herklotz <yann@yannherklotz.com>

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

==============
Compiler Proof
==============

This is the top-level module of the correctness proof and proves the final
backwards simulation correct.

Imports
=======


We first need to import all of the modules that are used in the correctness
proof, which includes all of the passes that are performed in Vericert and the
CompCert front end.

.. coq:: none
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
Require Import compcert.lib.Maps.

Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Unusedglobproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
Require vericert.hls.Verilog.
Require vericert.hls.GibleSeq.
Require vericert.hls.GibleSeqgen.
Require vericert.hls.GibleSeqgenproof.
Require vericert.hls.GiblePargen.
Require vericert.hls.GiblePargenproof.
Require vericert.hls.GibleSubPargen.
Require vericert.hls.GibleSubPargenproof.
Require vericert.hls.DHTLgen.
Require vericert.hls.DVeriloggen.
Require vericert.hls.DVeriloggenproof.
(*Require vericert.hls.Pipeline.*)
Require vericert.hls.IfConversion.
Require vericert.hls.IfConversionproof.
Require vericert.hls.CondElim.
Require vericert.hls.CondElimproof.
Require vericert.hls.DeadBlocks.
Require vericert.hls.DeadBlocksproof.
(*Require vericert.hls.PipelineOp.*)
Require vericert.HLSOpts.
Require vericert.hls.DMemorygen.
Require vericert.hls.ClockRegisters.
Require vericert.hls.ClockMemory.
Require vericert.hls.ClockRegistersproof.
Require vericert.hls.ClockMemoryproof.

Require Import vericert.hls.DHTLgenproof0.
Require Import vericert.hls.DHTLgenproof.

(*|
Declarations
============

We then need to declare the external OCaml functions used to print out
intermediate steps in the compilation, such as ``print_RTL``, ``print_HTL`` and
``print_RTLBlock``.
|*)

Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_DHTL: Z -> DHTL.program -> unit.
Parameter print_GibleSeq: Z -> GibleSeq.GibleSeq.program -> unit.
Parameter print_GiblePar: Z -> GiblePar.GiblePar.program -> unit.
Parameter print_GibleSubPar: Z -> GibleSubPar.GibleSubPar.program -> unit.

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

(*|
We also declare some new notation, which is also used in CompCert to combine the
monadic results of each pass.
|*)

Notation "a @@@ b" :=
   (Compiler.apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
  (Compiler.apply_total _ _ a b) (at level 50, left associativity).

(*|
As printing is used in the translation but does not change the output, we need
to prove that it has no effect so that it can be removed during the proof.
|*)

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(*|
Finally, some optimisation passes are only activated by a flag, which is handled
by the following functions for partial and total passes.
|*)

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop)
  : A -> A -> Prop :=
  if flag tt then R else eq.

Definition match_rep {A: Type} (R: A -> A -> Prop): A -> A -> Prop :=
  Relation_Operators.clos_refl_trans A R.

Global Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(* Global Instance TransfIfLink {A: Type} {LA: Linker A} *)
(*                       (transf: A -> A -> Prop) (TL: TransfLink transf) *)
(*                       : TransfLink (match_rep transf). *)
(* Admitted. *)

(* Lemma total_rep_match: *)
(*   forall (A B: Type) (n: list B) (f: A -> B -> A) *)
(*          (rel: A -> A -> Prop) (prog: A), *)
(*     (forall b p, rel p (f p b)) -> *)
(*   match_rep rel prog (fold_left f n prog). *)
(* Proof. Admitted. *)

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A)
         (rel: A -> A -> Prop) (prog: A),
    (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A)
         (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt).
  auto. congruence.
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
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool)
         (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst.
  apply forward_simulation_identity.
Qed.

(*|
Top-level Translation
---------------------

An optimised transformation function from ``RTL`` to ``Verilog`` can then be
defined, which applies the front end compiler optimisations of CompCert to the
RTL that is generated and then performs the two Vericert passes from RTL to HTL
and then from HTL to Verilog.
|*)

Definition transf_hls3 p :=
  OK p
  @@@ GibleSubPargen.transl_program
   @@ print (print_GibleSubPar 0)
  (* @@@ HTLPargen.transl_program *)
  @@@ DHTLgen.transl_program
   @@ print (print_DHTL 0)
   @@ ClockMemory.transf_program
   @@ print (print_DHTL 1)
   @@ DMemorygen.transf_program
   @@ print (print_DHTL 2)
  @@@ ClockRegisters.transf_program
   @@ print (print_DHTL 3)
   @@ DVeriloggen.transl_program.

Definition transf_hls2 (p : RTL.program) : res Verilog.program :=
  OK p
  @@@ GibleSeqgen.transl_program
   @@ print (print_GibleSeq 0)
   @@ total_if HLSOpts.optim_if_conversion CondElim.transf_program
   @@ print (print_GibleSeq 1)
   (* @@ total_if HLSOpts.optim_if_conversion (fold_left (fun a b => IfConversion.transf_program b a) (PTree.empty _ :: PTree.empty _ :: nil)) *)
   @@ total_if HLSOpts.optim_if_conversion (IfConversion.transf_program)
   @@ print (print_GibleSeq 2)
   @@ total_if HLSOpts.optim_if_conversion (IfConversion.transf_program)
   @@ print (print_GibleSeq 3)
   @@ total_if HLSOpts.optim_if_conversion (IfConversion.transf_program)
   @@ print (print_GibleSeq 4)
  @@@ DeadBlocks.transf_program
   @@ print (print_GibleSeq 5)
  @@@ time "Scheduling" GiblePargen.transl_program
   @@ print (print_GiblePar 0)
  @@@ transf_hls3.

Definition transf_hls1 (p : RTL.program) :=
  OK p
  @@@ Inlining.transf_program
   @@ print (print_RTL 1)
   @@ Renumber.transf_program
   @@ print (print_RTL 2)
   @@ total_if Compopts.optim_constprop
      (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop
      (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 4)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_redundancy
      (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 6)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 7)
  @@@ transf_hls2.

Definition transf_hls (p: Csyntax.program) :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@@ transf_hls1.

(*|
Correctness Proof
=================

Finally, the top-level definition for all the passes is defined, which combines
the ``match_prog`` predicates of each translation pass from C until Verilog.
|*)

Local Open Scope linking_scope.

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
  ::: mkpass GibleSeqgenproof.match_prog
  ::: mkpass (match_if HLSOpts.optim_if_conversion CondElimproof.match_prog)
  ::: mkpass (match_if HLSOpts.optim_if_conversion IfConversionproof.match_prog)
  ::: mkpass (match_if HLSOpts.optim_if_conversion IfConversionproof.match_prog)
  ::: mkpass (match_if HLSOpts.optim_if_conversion IfConversionproof.match_prog)
  ::: mkpass DeadBlocksproof.match_prog
  ::: mkpass GiblePargenproof.match_prog
  ::: mkpass GibleSubPargenproof.match_prog
  ::: (@mkpass _ _ DHTLgenproof0.match_prog
               (DHTLgenproof0.TransfHTLLink DHTLgen.transl_program))
  ::: mkpass ClockMemoryproof.match_prog
  ::: mkpass DMemorygen.match_prog
  ::: mkpass ClockRegistersproof.match_prog
  ::: mkpass DVeriloggenproof.match_prog
  ::: pass_nil _.

(*|
These passes are then composed into a larger, top-level ``match_prog`` predicate
which matches a C program directly with a Verilog program.
|*)

Definition match_prog: Csyntax.program -> Verilog.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

(*|
We then need to prove that this predicate holds, assuming that the translation
is performed using the ``transf_hls`` function declared above.
|*)

Theorem transf_hls_match:
  forall p tp,
    transf_hls p = OK tp ->
    match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_hls, time in T. simpl in *.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1;
    cbn in T; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2;
    simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3;
    simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4;
    simpl in T; try discriminate.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5;
    simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6;
    simpl in T; try discriminate.
  unfold transf_hls1, time in T. simpl in T. rewrite ! compose_print_identity in T.
  destruct (Inlining.transf_program p6) as [p7|e] eqn:P7;
    simpl in T; try discriminate.
  set (p8 := Renumber.transf_program p7) in *.
  set (p9 := total_if Compopts.optim_constprop
                      Constprop.transf_program p8) in *.
  set (p10 := total_if Compopts.optim_constprop
                       Renumber.transf_program p9) in *.
  destruct (partial_if Compopts.optim_CSE CSE.transf_program p10)
    as [p11|e] eqn:P11; simpl in T; try discriminate.
  destruct (partial_if Compopts.optim_redundancy Deadcode.transf_program p11)
    as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p12) as [p13|e] eqn:P13;
    simpl in T; try discriminate.
  unfold transf_hls2, time in *. simpl in T. rewrite ! compose_print_identity in T.
  destruct (GibleSeqgen.transl_program p13) as [p14|e] eqn:P14;
    simpl in T; try discriminate.
  set (p15 := total_if HLSOpts.optim_if_conversion
                       CondElim.transf_program p14) in *.
  set (p16 := total_if HLSOpts.optim_if_conversion
                       IfConversion.transf_program p15) in *.
  set (p17 := total_if HLSOpts.optim_if_conversion
                       IfConversion.transf_program p16) in *.
  set (p18 := total_if HLSOpts.optim_if_conversion
                       IfConversion.transf_program p17) in *.
  destruct (DeadBlocks.transf_program p18) as [p19|e] eqn:P19;
    simpl in T; try discriminate.
  destruct (GiblePargen.transl_program p19) as [p20|e] eqn:P20;
    simpl in T; try discriminate.
  unfold transf_hls3, time in T. simpl in T. rewrite ! compose_print_identity in T.
  destruct (GibleSubPargen.transl_program p20) as [p21|e] eqn:P21;
    simpl in T; try discriminate.
  destruct (DHTLgen.transl_program p21) as [p22|e] eqn:P22;
    simpl in T; try discriminate.
  set (p23 := ClockMemory.transf_program p22) in *.
  set (p24 := DMemorygen.transf_program p23) in *.
  destruct (ClockRegisters.transf_program p24) as [p25|e] eqn:P25;
    simpl in T; try discriminate.
  set (p26 := DVeriloggen.transl_program p25) in *. inv T.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply Inliningproof.transf_program_match; auto.
  exists p8; split. apply Renumberproof.transf_program_match; auto.
  exists p9; split. apply total_if_match.
  apply Constpropproof.transf_program_match.
  exists p10; split. apply total_if_match.
  apply Renumberproof.transf_program_match.
  exists p11; split. eapply partial_if_match; eauto.
  apply CSEproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto.
  apply Deadcodeproof.transf_program_match.
  exists p13; split. apply Unusedglobproof.transf_program_match; auto.
  exists p14; split. apply GibleSeqgenproof.transf_program_match; auto.
  exists p15; split. eapply total_if_match; eauto.
  apply CondElimproof.transf_program_match; auto.
  exists p16; split. eapply total_if_match; eauto.
  apply IfConversionproof.transf_program_match; auto.
  exists p17; split. eapply total_if_match; eauto.
  apply IfConversionproof.transf_program_match; auto.
  exists p18; split. eapply total_if_match; eauto.
  apply IfConversionproof.transf_program_match; auto.
  exists p19; split. apply DeadBlocksproof.transf_program_match; auto.
  exists p20; split. apply GiblePargenproof.transf_program_match; auto.
  exists p21; split. apply GibleSubPargenproof.transf_program_match; auto.
  exists p22; split. apply DHTLgenproof0.transf_program_match; auto.
  exists p23; split. apply ClockMemoryproof.transf_program_match; auto.
  exists p24; split. apply DMemorygen.transf_program_match; auto.
  exists p25; split. apply ClockRegistersproof.transf_program_match; auto.
  exists p26; split. apply DVeriloggenproof.transf_program_match; auto.
  reflexivity.
Qed.

Theorem cstrategy_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Cstrategy.semantics p) (Verilog.semantics tp)
  /\ backward_simulation (atomic (Cstrategy.semantics p))
                         (Verilog.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation (Cstrategy.semantics p)
                                (Verilog.semantics p26)).
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
  eapply match_if_simulation. eassumption.
  exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
  exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
  exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
  exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply GibleSeqgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact CondElimproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact IfConversionproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact IfConversionproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact IfConversionproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply DeadBlocksproof.transf_program_correct. eassumption.
  eapply compose_forward_simulations.
    eapply GiblePargenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply GibleSubPargenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply DHTLgenproof.transf_program_correct. eassumption.
  eapply compose_forward_simulations.
    eapply ClockMemoryproof.transf_program_correct. eassumption.
  eapply compose_forward_simulations.
    eapply DMemorygen.transf_program_correct. eassumption.
  eapply compose_forward_simulations.
    eapply ClockRegistersproof.transf_program_correct. eassumption.
  eapply DVeriloggenproof.transf_program_correct; eassumption.
  }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces.
  eapply Verilog.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Verilog.semantics_determinate.
Qed.

(*|
Backward Simulation
-------------------

The following theorem is a *backward simulation* between the C and Verilog,
which proves the semantics preservation of the translation.  We can assume that
the C and Verilog programs match, as we have proven previously in
``transf_hls_match`` that our translation implies that the ``match_prog``
predicate will hold.
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
We can then use ``transf_hls_match`` to prove the backward simulation where the
assumption is that the translation is performed using the ``transf_hls``
function and that it succeeds.
|*)

Theorem transf_c_program_correct:
  forall p tp,
  transf_hls p = OK tp ->
  backward_simulation (Csem.semantics p) (Verilog.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_hls_match; auto.
Qed.

(*|
The final theorem of the semantic preservation of the translation of separate
translation units can also be proven correct, however, this is only because the
translation fails if more than one translation unit is passed to Vericert at the
moment.
|*)

Theorem separate_transf_c_program_correct:
  forall c_units verilog_units c_program,
  nlist_forall2 (fun cu tcu => transf_hls cu = OK tcu) c_units verilog_units ->
  link_list c_units = Some c_program ->
  exists verilog_program,
      link_list verilog_units = Some verilog_program
   /\ backward_simulation (Csem.semantics c_program)
                          (Verilog.semantics verilog_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units verilog_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros.
    apply transf_hls_match; auto. }
  assert (exists verilog_program, link_list verilog_units = Some verilog_program
                                  /\ match_prog c_program verilog_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (verilog_program & P & Q).
  exists verilog_program; split; auto. apply c_semantic_preservation; auto.
Qed.
