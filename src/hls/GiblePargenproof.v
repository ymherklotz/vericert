(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2023 Yann Herklotz <git@yannherklotz.com>
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

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Linking.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePargenproofEquiv.
Require Import vericert.hls.GiblePargen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.
Require Import vericert.common.Monad.
Require Import vericert.hls.GiblePargenproofForward.
Require Import vericert.hls.GiblePargenproofBackward.

Module Import OptionExtra := MonadExtra(Option).

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

#[local] Opaque simplify.
#[local] Opaque deep_simplify.

Ltac destr := destruct_match; try discriminate; [].

Definition state_lessdef := GiblePargenproofEquiv.match_states.

Definition match_prog (prog : GibleSeq.program) (tprog : GiblePar.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.

(* TODO: Fix the `bb` and add matches for them. *)
Inductive match_stackframes: GibleSeq.stackframe -> GiblePar.stackframe -> Prop :=
| match_stackframe:
    forall f tf res sp pc rs rs' ps ps',
      transl_function f = OK tf ->
      (forall x, rs !! x = rs' !! x) ->
      (forall x, ps !! x = ps' !! x) ->
      match_stackframes (GibleSeq.Stackframe res f sp pc rs ps)
                        (Stackframe res tf sp pc rs' ps').

Inductive match_states: GibleSeq.state -> GiblePar.state -> Prop :=
| match_state:
    forall sf f sp pc rs rs' m sf' tf ps ps'
      (TRANSL: transl_function f = OK tf)
      (STACKS: list_forall2 match_stackframes sf sf')
      (REG: forall x, rs !! x = rs' !! x)
      (REG: forall x, ps !! x = ps' !! x),
      match_states (GibleSeq.State sf f sp pc rs ps m)
                   (State sf' tf sp pc rs' ps' m)
| match_returnstate:
    forall stack stack' v m
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (GibleSeq.Returnstate stack v m)
                   (Returnstate stack' v m)
| match_callstate:
    forall stack stack' f tf args m
      (TRANSL: transl_fundef f = OK tf)
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (GibleSeq.Callstate stack f args m)
                   (Callstate stack' tf args m).

Section CORRECTNESS.

  Context (prog: GibleSeq.program) (tprog : GiblePar.program).
  Context (TRANSL: match_prog prog tprog).

  Let ge : GibleSeq.genv := Globalenvs.Genv.globalenv prog.
  Let tge : GiblePar.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.
  Hint Resolve symbols_preserved : rtlgp.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: GibleSeq.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: GibleSeq.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof (Genv.senv_transf_partial TRANSL).
  Hint Resolve senv_preserved : rtlgp.

  Lemma sig_transl_function:
    forall (f: GibleSeq.fundef) (tf: GiblePar.fundef),
      transl_fundef f = OK tf ->
      funsig tf = GibleSeq.funsig f.
  Proof using .
    unfold transl_fundef, transf_partial_fundef, transl_function; intros;
    repeat destruct_match; crush;
    match goal with H: OK _ = OK _ |- _ => inv H end; auto.
  Qed.
  Hint Resolve sig_transl_function : rtlgp.

  Hint Resolve Val.lessdef_same : rtlgp.
  Hint Resolve regs_lessdef_regs : rtlgp.

  Lemma find_function_translated:
    forall ros rs rs' f,
      (forall x, rs !! x = rs' !! x) ->
      GibleSeq.find_function ge ros rs = Some f ->
      exists tf, find_function tge ros rs' = Some tf
                 /\ transl_fundef f = OK tf.
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

  Lemma schedule_oracle_nil:
    forall bb,
      schedule_oracle nil bb = true ->
      bb = nil.
  Proof using .
    unfold schedule_oracle, check_control_flow_instr.
    simplify; repeat destruct_match; crush.
  Qed.

  Lemma schedule_oracle_nil2:
      schedule_oracle nil nil = true.
  Proof using .
    unfold schedule_oracle, check_control_flow_instr, check.
    simplify; repeat destruct_match; crush.
    (* now rewrite ! check_mutexcl_singleton. *)
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
  Hint Resolve eval_op_eq : rtlgp.

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
  Hint Resolve eval_addressing_eq : rtlgp.

(*|
==============
RTLPargenproof
==============

RTLBlock to abstract translation
================================

Correctness of translation from RTLBlock to the abstract interpretation
language.

This is the top-level lemma which uses the following proofs to complete the
square:

- ``abstr_sequence_correct``: This is the lemma that states the forward
  translation form ``GibleSeq`` to ``Abstr`` was correct.
- ``abstr_check_correct``: This is the lemma that states that if a check between
  two ``Abstr`` programs succeeds, that they will also behave the same.  This
  depends on the SAT solver correctness, as the predicates might be
  syntactically different to each other.
- ``abstr_seq_reverse_correct``: This is the lemma that shows that the backwards
  simulation between the abstract translation and the concrete execution also
  holds.  We only have a translation from the concrete into the abstract, but
  then prove that if we have an execution in the abstract, we can observe that
  same execution in the concrete.
- ``seqbb_step_parbb_step``: Finally, this lemma states that the parallel
  execution of the basic block is equivalent to the sequential execution of the
  concatenation of that parallel block.  This is because even in the translation
  to HTL, the Verilog semantics are sequential within a clock cycle, but will
  then be parallelised by the synthesis tool.  The argument for why this is
  still useful is because we are identifying and scheduling instructions into
  clock cycles.
|*)

  Definition local_abstr_check_correct :=
    @abstr_check_correct GibleSeq.fundef GiblePar.fundef.

  Definition local_abstr_check_correct2 :=
    @abstr_check_correct GibleSeq.fundef GibleSeq.fundef.

  Lemma ge_preserved_local :
    ge_preserved ge tge.
  Proof.
    unfold ge_preserved; 
    eauto using eval_op_eq, eval_addressing_eq.
  Qed.

  Lemma lessdef_regmap_optget:
    forall or rs rs',
      regs_lessdef rs rs' ->
      Val.lessdef (regmap_optget or Vundef rs) (regmap_optget or Vundef rs').
  Proof using. destruct or; crush. Qed.
  Hint Resolve lessdef_regmap_optget : rtlgp.

  Lemma regmap_equiv_lessdef:
    forall rs rs',
      (forall x, rs !! x = rs' !! x) ->
      regs_lessdef rs rs'.
  Proof using.
    intros; unfold regs_lessdef; intros.
    rewrite H. apply Val.lessdef_refl.
  Qed.
  Hint Resolve regmap_equiv_lessdef : rtlgp.

  Lemma int_lessdef:
    forall rs rs',
      regs_lessdef rs rs' ->
      (forall arg v,
          rs !! arg = Vint v ->
          rs' !! arg = Vint v).
  Proof using. intros ? ? H; intros; specialize (H arg); inv H; crush. Qed.
  Hint Resolve int_lessdef : rtlgp.

  Ltac semantics_simpl :=
    match goal with
    | [ H: match_states _ _ |- _ ] =>
      let H2 := fresh "H" in
      learn H as H2; inv H2
    | [ H: transl_function ?f = OK _ |- _ ] =>
      let H2 := fresh "TRANSL" in
      learn H as H2;
      unfold transl_function in H2;
      destruct (check_scheduled_trees
                  (GibleSeq.fn_code f)
                  (fn_code (schedule f))) eqn:?;
               [| discriminate ]; inv H2
    | [ H: context[check_scheduled_trees] |- _ ] =>
      let H2 := fresh "CHECK" in
      learn H as H2;
      eapply check_scheduled_trees_correct in H2; [| solve [eauto] ]
    | [ H: schedule_oracle nil ?bb = true |- _ ] =>
      let H2 := fresh "SCHED" in
      learn H as H2;
      apply schedule_oracle_nil in H2
    | [ H: find_function _ _ _ = Some _, H2: forall x, ?rs !! x = ?rs' !! x |- _ ] =>
      learn H; exploit find_function_translated; try apply H2; eauto; inversion 1
    | [ H: Mem.free ?m _ _ _ = Some ?m', H2: Mem.extends ?m ?m'' |- _ ] =>
      learn H; exploit Mem.free_parallel_extends; eauto; intros
    | [ H: Events.eval_builtin_args _ _ _ _ _ _, H2: regs_lessdef ?rs ?rs' |- _ ] =>
      let H3 := fresh "H" in
      learn H; exploit Events.eval_builtin_args_lessdef; [apply H2 | | |];
      eauto with rtlgp; intro H3; learn H3
    | [ H: Events.external_call _ _ _ _ _ _ _ |- _ ] =>
      let H2 := fresh "H" in
      learn H; exploit Events.external_call_mem_extends;
      eauto; intro H2; learn H2
    | [ H: exists _, _ |- _ ] => inv H
    | _ => progress simplify
    end.

  Hint Resolve Events.eval_builtin_args_preserved : rtlgp.
  Hint Resolve Events.external_call_symbols_preserved : rtlgp.
  Hint Resolve set_res_lessdef : rtlgp.
  Hint Resolve set_reg_lessdef : rtlgp.
  Hint Resolve Op.eval_condition_lessdef : rtlgp.

  Hint Constructors Events.eval_builtin_arg: barg.

  Lemma eval_builtin_arg_eq:
    forall A ge a v1 m1 e1 e2 sp,
      (forall x, e1 x = e2 x) ->
      @Events.eval_builtin_arg A ge e1 sp m1 a v1 ->
      Events.eval_builtin_arg ge e2 sp m1 a v1.
Proof. induction 2; try rewrite H; eauto with barg. Qed.

  Lemma eval_builtin_args_eq:
    forall A ge e1 sp m1 e2 al vl1,
      (forall x, e1 x = e2 x) ->
      @Events.eval_builtin_args A ge e1 sp m1 al vl1 ->
      Events.eval_builtin_args ge e2 sp m1 al vl1.
  Proof.
    induction 2.
    - econstructor; split.
    - exploit eval_builtin_arg_eq; eauto. intros.
      destruct IHlist_forall2 as [| y]. constructor; eauto.
      constructor. constructor; auto.
      constructor; eauto.
  Qed.

  #[local] Hint Resolve Events.external_call_symbols_preserved : core.
  #[local] Hint Resolve eval_builtin_args_eq : core.
  #[local] Hint Resolve symbols_preserved : core.
  #[local] Hint Resolve senv_preserved : core.
  #[local] Hint Resolve eval_op_eq : core.
  #[local] Hint Resolve eval_addressing_eq : core.

  Lemma step_instr_ge :
    forall sp a i i',
      step_instr ge sp i a i' ->
      step_instr tge sp i a i'.
  Proof.
    inversion 1; subst; simplify; try solve [econstructor; eauto].
    - constructor; auto; rewrite <- eval_op_eq; eauto.
    - econstructor; eauto; rewrite <- eval_addressing_eq; eauto.
    - econstructor; eauto; rewrite <- eval_addressing_eq; eauto.
  Qed.
  #[local] Hint Resolve step_instr_ge : core.

  Lemma seqbb_step_step_instr_list :
    forall sp a i i',
      SeqBB.step ge sp i a i' ->
      ParBB.step_instr_list tge sp i a i'.
  Proof.
    induction a; simplify; inv H.
    econstructor; eauto. eapply IHa; eauto.
    econstructor; eauto. constructor.
  Qed.
  #[local] Hint Resolve seqbb_step_step_instr_list : core.

  Lemma step_list2_step_instr_list :
    forall sp a i i',
      step_list2 (step_instr ge) sp i a i' ->
      ParBB.step_instr_list tge sp i a i'.
  Proof.
    induction a; simplify; inv H.
    econstructor; eauto.
    destruct i; try solve [inv H4].
    econstructor; eauto. apply IHa; auto.
  Qed.
  #[local] Hint Resolve step_list2_step_instr_list : core.

  Lemma seqbb_step_step_instr_seq :
    forall sp x i i' cf,
      SeqBB.step ge sp (Iexec i) (concat x) (Iterm i' cf) ->
      ParBB.step_instr_seq tge sp (Iexec i) x (Iterm i' cf).
  Proof.
    induction x; crush. inv H. eapply step_options in H.
    inv H. econstructor. eauto. constructor.
    simplify. econstructor; eauto.
    eapply IHx; eauto.
  Qed.

  Lemma step_list2_step_instr_seq :
    forall sp x i i',
      step_list2 (step_instr ge) sp (Iexec i) (concat x) (Iexec i') ->
      ParBB.step_instr_seq tge sp (Iexec i) x (Iexec i').
  Proof.
    induction x; crush. inv H. constructor.
    eapply step_options2 in H. simplify.
    econstructor; eauto.
    eapply IHx; eauto.
  Qed.

  Lemma seqbb_step_parbb_step :
    forall sp x i i' cf,
      SeqBB.step ge sp (Iexec i) (concat (concat x)) (Iterm i' cf) ->
      ParBB.step tge sp (Iexec i) x (Iterm i' cf).
  Proof.
    induction x; crush. inv H.
    rewrite concat_app in H.
    eapply step_options in H. inv H.
    constructor. eapply seqbb_step_step_instr_seq; eauto.
    simplify. econstructor.
    eapply step_list2_step_instr_seq; eauto.
    eapply IHx; eauto.
  Qed.

  Lemma schedule_oracle_correct :
    forall x y sp i i' ti cf,
      schedule_oracle x y = true ->
      SeqBB.step ge sp (Iexec i) x (Iterm i' cf) ->
      state_lessdef i ti ->
      exists ti', ParBB.step tge sp (Iexec ti) y (Iterm ti' cf)
             /\ state_lessdef i' ti'.
  Proof.
    unfold schedule_oracle; intros. repeat (destruct_match; try discriminate). simplify.
    exploit abstr_sequence_correct; eauto; simplify.
    exploit local_abstr_check_correct2; eauto.
    { constructor. eapply ge_preserved_refl. reflexivity. }
(*    { inv H. inv H8. exists pr'. intros x0. specialize (H x0). auto. } *)
    simplify.
    exploit abstr_seq_reverse_correct; eauto. admit. admit. admit. admit. reflexivity. simplify.
    exploit seqbb_step_parbb_step; eauto; intros.
    econstructor; split; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
  Admitted.

  Lemma step_cf_correct :
    forall cf ts s s' t,
      GibleSeq.step_cf_instr ge s cf t s' ->
      match_states s ts ->
      exists ts', step_cf_instr tge ts cf t ts'
             /\ match_states s' ts'.
  Proof.

(*|
Proof Sketch:  Trivial because of structural equality.
|*)

  Admitted.

  Lemma match_states_stepBB :
    forall s f sp pc rs pr m sf' f' trs tps tm rs' pr' m' trs' tpr' tm',
      match_states (GibleSeq.State s f sp pc rs pr m) (State sf' f' sp pc trs tps tm) ->
      state_lessdef (mk_instr_state rs' pr' m') (mk_instr_state trs' tpr' tm') ->
      match_states (GibleSeq.State s f sp pc rs' pr' m') (State sf' f' sp pc trs' tpr' tm').
  Proof.
    inversion 1; subst; simplify.
    inv H0. econstructor; eauto.
  Qed.

  Theorem transl_step_correct :
    forall (S1 : GibleSeq.state) t S2,
      GibleSeq.step ge S1 t S2 ->
      forall (R1 : GiblePar.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus GiblePar.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; repeat semantics_simpl.
    { exploit schedule_oracle_correct; eauto. constructor; eauto. simplify.
      destruct x0.
      pose proof H2 as X. eapply match_states_stepBB in X; eauto.
      exploit step_cf_correct; eauto. simplify.
      eexists; split. apply Smallstep.plus_one.
      econstructor; eauto. auto.
    }
    { unfold bind in *. inv TRANSL0. clear Learn. inv H0. destruct_match; crush.
      inv H2. unfold transl_function in Heqr. destruct_match; crush.
      inv Heqr.
      repeat econstructor; eauto.
      unfold bind in *. destruct_match; crush. }
    { inv TRANSL0.
      repeat econstructor;
        eauto using Events.E0_right. }
    { inv STACKS. inv H2. repeat econstructor; eauto.
      intros. apply PTree_matches; eauto. }
    Qed.

  Lemma transl_initial_states:
    forall S,
      GibleSeq.initial_state prog S ->
      exists R, GiblePar.initial_state tprog R /\ match_states S R.
  Proof.
    induction 1.
    exploit function_ptr_translated; eauto. intros [tf [A B]].
    econstructor; split.
    econstructor. apply (Genv.init_mem_transf_partial TRANSL); eauto.
    replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
    symmetry; eapply match_program_main; eauto.
    eexact A.
    rewrite <- H2. apply sig_transl_function; auto.
    constructor. auto. constructor.
  Qed.

  Lemma transl_final_states:
    forall S R r,
      match_states S R -> GibleSeq.final_state S r -> GiblePar.final_state R r.
  Proof. intros. inv H0. inv H. inv STACKS. constructor. Qed.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (GibleSeq.semantics prog) (GiblePar.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus.
    apply senv_preserved.
    eexact transl_initial_states.
    eexact transl_final_states.
    exact transl_step_correct.
  Qed.

End CORRECTNESS.
