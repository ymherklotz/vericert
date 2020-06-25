(*
 * CoqUp: Verified high-level synthesis.
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

From coqup Require
     Verilog
     Veriloggen
     HTLgen.

Parameter print_RTL: Z -> RTL.program -> unit.

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
  @@ Tailcall.transf_program
  @@@ Inlining.transf_program
  @@ Renumber.transf_program
  @@ Constprop.transf_program
  @@ Renumber.transf_program
  @@@ CSE.transf_program
  @@@ Deadcode.transf_program
  @@@ Unusedglob.transform_program
  @@ print (print_RTL 1)
  @@@ HTLgen.transl_program
  @@ Veriloggen.transl_program.

(* Unoptimised below: *)
(*Definition transf_backend (r : RTL.program) : res Verilog.program :=
  OK r
  @@@ Inlining.transf_program
  @@ print (print_RTL 1)
  @@@ HTLgen.transl_program
  @@ Veriloggen.transl_program.
*)

Definition transf_frontend (p: Csyntax.program) : res RTL.program :=
  OK p
  @@@ SimplExpr.transl_program
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@ print (print_RTL 0).

Definition transf_hls (p : Csyntax.program) : res Verilog.program :=
  OK p
  @@@ transf_frontend
  @@@ transf_backend.

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
  rewrite ! compose_print_identity in T.
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
