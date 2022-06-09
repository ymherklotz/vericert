(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>

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

===================
If Conversion Proof
===================

.. coq:: none
|*)

Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Maps.
Require Import compcert.backend.Registers.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.

Require Import vericert.common.Vericertlib.
Require Import vericert.common.DecEq.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.IfConversion.
Require Import vericert.hls.Predicate.

#[local] Open Scope positive.
#[local] Notation "'mki'" := (mk_instr_state) (at level 1).

Variant match_stackframe : stackframe -> stackframe -> Prop :=
  | match_stackframe_init :
    forall res f tf sp pc rs p
           (TF: transf_function f = tf),
      match_stackframe (Stackframe res f sp pc rs p) (Stackframe res tf sp pc rs p).

(* c ! pc = fc ! pc *)
(* \/ (c ! pc = a ++ fc ! pc' ++ b /\ fc ! pc = a ++ if p goto pc' ++ b) *)

Definition bool_order (b: bool): nat := if b then 1 else 0.

Section CORRECTNESS.

  Context (prog tprog : program).

  Let ge : genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

  Definition sem_extrap f pc sp in_s in_s' block :=
    forall out_s block2,
      SeqBB.step tge sp in_s block out_s ->
      f.(fn_code) ! pc = Some block2 ->
      SeqBB.step tge sp in_s' block2 out_s.

  Variant match_states : option SeqBB.t -> state -> state -> Prop :=
    | match_state_true :
      forall stk stk' f tf sp pc rs p m b pc0 rs0 p0 m0
             (TF: transf_function f = tf)
             (STK: Forall2 match_stackframe stk stk')
             (EXT: sem_extrap tf pc0 sp (Iexec (mki rs p m)) (Iexec (mki rs0 p0 m0)) b)
             (STAR: star step ge (State stk f sp pc0 rs0 p0 m0) E0 (State stk f sp pc rs p m)),
        match_states (Some b) (State stk f sp pc rs p m) (State stk' tf sp pc0 rs0 p0 m0)
    | match_callstate :
      forall cs cs' f tf args m
             (TF: transf_fundef f = tf)
             (STK: Forall2 match_stackframe cs cs'),
        match_states None (Callstate cs f args m) (Callstate cs' tf args m)
    | match_returnstate :
      forall cs cs' v m
             (STK: Forall2 match_stackframe cs cs'),
        match_states None (Returnstate cs v m) (Returnstate cs' v m).

  Definition match_prog (p: program) (tp: program) :=
    Linking.match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

  Context (TRANSL : match_prog prog tprog).

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof using TRANSL. intros; eapply (Genv.senv_transf TRANSL). Qed.

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef f).
  Proof (Genv.find_funct_ptr_transf TRANSL).

  Lemma sig_transf_function:
    forall (f tf: fundef),
      funsig (transf_fundef f) = funsig f.
  Proof using.
    unfold transf_fundef. unfold AST.transf_fundef; intros. destruct f.
    unfold transf_function. destruct_match; auto. auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: GibleSeq.fundef),
      Genv.find_funct ge v = Some f ->
      Genv.find_funct tge v = Some (transf_fundef f).
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto. simplify. eauto.
  Qed.

  Lemma find_function_translated:
    forall ros rs f,
      find_function ge ros rs = Some f ->
      find_function tge ros rs = Some (transf_fundef f).
  Proof using TRANSL.
    Ltac ffts := match goal with
                 | [ H: forall _, Val.lessdef _ _, r: Registers.reg |- _ ] =>
                     specialize (H r); inv H
                 | [ H: Vundef = ?r, H1: Genv.find_funct _ ?r = Some _ |- _ ] =>
                     rewrite <- H in H1
                 | [ H: Genv.find_funct _ Vundef = Some _ |- _] => solve [inv H]
                 | _ => solve [exploit functions_translated; eauto]
                 end.
    destruct ros; simplify; try rewrite <- H;
      [| rewrite symbols_preserved; destruct_match;
         try (apply function_ptr_translated); crush ];
      intros;
      repeat ffts.
  Qed.

  Lemma transf_initial_states :
    forall s1,
      initial_state prog s1 ->
      exists s2, initial_state tprog s2 /\ match_states s1 s2.
  Proof using TRANSL.
    induction 1.
    exploit function_ptr_translated; eauto; intros.
    do 2 econstructor; simplify. econstructor.
    apply (Genv.init_mem_transf TRANSL); eauto.
    replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
    symmetry; eapply Linking.match_program_main; eauto. eauto.
    erewrite sig_transf_function; eauto. constructor. auto. auto.
  Qed.

  Lemma transf_final_states :
    forall s1 s2 r,
      match_states s1 s2 -> final_state s1 r -> final_state s2 r.
  Proof using.
    inversion 2; crush. subst. inv H. inv STK. econstructor.
  Qed.

  Lemma eval_op_eq:
    forall (sp0 : Values.val) (op : Op.operation) (vl : list Values.val) m,
      Op.eval_operation ge sp0 op vl m = Op.eval_operation tge sp0 op vl m.
  Proof using TRANSL.
    intros.
    destruct op; auto; unfold Op.eval_operation, Genv.symbol_address, Op.eval_addressing32;
    [| destruct a; unfold Genv.symbol_address ];
    try rewrite symbols_preserved; auto.
  Qed.

  Lemma eval_addressing_eq:
    forall sp addr vl,
      Op.eval_addressing ge sp addr vl = Op.eval_addressing tge sp addr vl.
  Proof using TRANSL.
    intros.
    destruct addr;
      unfold Op.eval_addressing, Op.eval_addressing32;
      unfold Genv.symbol_address;
      try rewrite symbols_preserved; auto.
  Qed.

  #[local] Hint Resolve eval_builtin_args_preserved : core.
  #[local] Hint Resolve symbols_preserved : core.
  #[local] Hint Resolve external_call_symbols_preserved : core.
  #[local] Hint Resolve senv_preserved : core.
  #[local] Hint Resolve find_function_translated : core.
  #[local] Hint Resolve sig_transf_function : core.

  Lemma transf_step_correct:
    forall (s1 : state) (t : trace) (s1' : state),
      step ge s1 t s1' ->
      forall s2 : state,
        match_states s1 s2 ->
        exists s2' : state, step tge s2 t s2' /\ match_states s1' s2'.
  Proof using TRANSL. Admitted.

  Theorem transf_program_correct:
    forward_simulation (semantics prog) (semantics tprog).
  Proof using TRANSL.
    eapply forward_simulation_step.
    + apply senv_preserved.
    + apply transf_initial_states.
    + apply transf_final_states.
    + apply transf_step_correct.
  Qed.

End CORRECTNESS.
