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

Require vericert.hls.Verilog.
Require vericert.hls.Veriloggen.
Require vericert.hls.Veriloggenproof.
Require vericert.hls.HTLgen.
Require vericert.hls.GibleSeq.
Require vericert.hls.GiblePar.
Require vericert.hls.GibleSeqgen.
Require vericert.hls.GiblePargen.
Require vericert.hls.HTLPargen.
Require vericert.hls.DVeriloggen.
(*Require vericert.hls.Pipeline.*)
Require vericert.hls.IfConversion.
Require vericert.hls.CondElim.
Require vericert.hls.DeadBlocks.
(*Require vericert.hls.PipelineOp.*)
Require vericert.HLSOpts.
Require vericert.hls.DMemorygen.
Require vericert.hls.ClockRegisters.
Require vericert.hls.GibleSeqgenproof.
Require vericert.hls.CondElimproof.
Require vericert.hls.IfConversionproof.
Require vericert.hls.DeadBlocksproof.
Require vericert.hls.GiblePargenproof.

(*|
Declarations
============

We then need to declare the external OCaml functions used to print out
intermediate steps in the compilation, such as ``print_RTL``, ``print_HTL`` and
``print_RTLBlock``.
|*)

Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_HTL: Z -> HTL.program -> unit.
Parameter print_DHTL: Z -> DHTL.program -> unit.
Parameter print_GibleSeq: Z -> GibleSeq.GibleSeq.program -> unit.
Parameter print_GiblePar: Z -> GiblePar.GiblePar.program -> unit.

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
This is an unverified version of transf_hls with some experimental additions
such as scheduling that aren't completed yet.
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
  @@@ GiblePargen.transl_program
   @@ print (print_GiblePar 0)
  @@@ HTLPargen.transl_program
   @@ print (print_DHTL 0)
   @@ DMemorygen.transf_program
   @@ print (print_DHTL 1)
  @@@ ClockRegisters.transl_program
   @@ print (print_DHTL 2)
   @@ DVeriloggen.transl_program.

Definition transf_hls_scheduled (p : Csyntax.program) : res GiblePar.GiblePar.program :=
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
  @@@ GiblePargen.transl_program
   @@ print (print_GiblePar 0).

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
  ::: pass_nil _.

(*|
These passes are then composed into a larger, top-level ``match_prog`` predicate
which matches a C program directly with a Verilog program.
|*)

Definition match_prog: Csyntax.program -> GiblePar.GiblePar.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

(*|
We then need to prove that this predicate holds, assuming that the translation
is performed using the ``transf_hls`` function declared above.
|*)

Theorem transf_hls_match:
  forall p tp,
    transf_hls_scheduled p = OK tp ->
    match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_hls_scheduled, time in T. cbn in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1;
    cbn in T; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2;
    cbn in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3;
    cbn in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4;
    cbn in T; try discriminate.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5;
    cbn in T; try discriminate.
  rewrite ! compose_print_identity in T.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6;
    cbn in T; try discriminate.
  unfold time in T. cbn in T.
  destruct (Inlining.transf_program p6) as [p7|e] eqn:P7;
    cbn in T; try discriminate.
  set (p8 := Renumber.transf_program p7) in *.
  set (p9 := total_if Compopts.optim_constprop
                      Constprop.transf_program p8) in *.
  set (p10 := total_if Compopts.optim_constprop
                       Renumber.transf_program p9) in *.
  destruct (partial_if Compopts.optim_CSE CSE.transf_program p10)
    as [p11|e] eqn:P11; cbn in T; try discriminate.
  destruct (partial_if Compopts.optim_redundancy Deadcode.transf_program p11)
    as [p12|e] eqn:P12; cbn in T; try discriminate.
  destruct (Unusedglob.transform_program p12) as [p13|e] eqn:P13;
    cbn in T; try discriminate.
  destruct (GibleSeqgen.transl_program p13) as [p14|e] eqn:P14;
    cbn in T; try discriminate.
  set (p15 := total_if HLSOpts.optim_if_conversion CondElim.transf_program p14) in *.
  set (p16 := total_if HLSOpts.optim_if_conversion IfConversion.transf_program p15) in *.
  set (p17 := total_if HLSOpts.optim_if_conversion IfConversion.transf_program p16) in *.
  set (p18 := total_if HLSOpts.optim_if_conversion IfConversion.transf_program p17) in *.
  destruct (DeadBlocks.transf_program p18) as [p19|e] eqn:P19; cbn in T; try discriminate.
  destruct (GiblePargen.transl_program p19) as [p20|e] eqn:P20; cbn in T; try discriminate.
  unfold match_prog; cbn.
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
  exists p15; split. apply total_if_match.
    apply CondElimproof.transf_program_match; auto.
  exists p16; split. apply total_if_match.
    apply IfConversionproof.transf_program_match; auto.
  exists p17; split. apply total_if_match.
    apply IfConversionproof.transf_program_match; auto.
  exists p18; split. apply total_if_match.
    apply IfConversionproof.transf_program_match; auto.
  exists p19; split. apply DeadBlocksproof.transf_program_match; auto.
  exists p20; split. apply GiblePargenproof.transf_program_match; auto.
  inv T. reflexivity.
Qed.

Theorem cstrategy_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Cstrategy.semantics p) (GiblePar.GiblePar.semantics tp).
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
                                (GiblePar.GiblePar.semantics p20)).
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
    eapply GibleSeqgenproof.transf_program_correct. eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact CondElimproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact IfConversionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact IfConversionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact IfConversionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply DeadBlocksproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply GiblePargenproof.transf_program_correct; eassumption.
  apply forward_simulation_identity.
  }
  auto.
Qed.

(*|
We can then use ``transf_hls_match`` to prove the backward simulation where the
assumption is that the translation is performed using the ``transf_hls``
function and that it succeeds.
|*)

Theorem transf_c_program_correct:
  forall p tp,
  transf_hls_scheduled p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (GiblePar.GiblePar.semantics tp).
Proof.
  intros. eapply cstrategy_semantic_preservation. apply transf_hls_match; auto.
Qed.
