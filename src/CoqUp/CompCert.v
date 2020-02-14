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

Notation "a @@@ b" :=
   (Compiler.apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (Compiler.apply_total _ _ a b) (at level 50, left associativity).

Definition transf_frontend (p: Csyntax.program) : res RTL.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program.

Local Open Scope linking_scope.

Definition CompCert's_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: pass_nil _.

Definition match_prog: Csyntax.program -> RTL.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

Theorem transf_frontend_match:
  forall p tp,
    transf_frontend p = OK tp ->
    match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_frontend in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  inversion T. reflexivity.
Qed.
