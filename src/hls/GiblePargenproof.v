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

Lemma equiv_update_top:
  forall i p f l lm p' f' l' lm',
    update_top (p, f, l, lm) i = Some (p', f', l', lm') ->
    update (p, f) i = Some (p', f').
Proof.
  intros. unfold update_top, Option.bind2, Option.ret in *. repeat destr.
  inv Heqp1. now inv H.
Qed.

Lemma equiv_update_top_inc:
  forall i p f l lm p' f' l' lm',
    update_top_inc (p, f, l, lm) i = Some (p', f', l', lm') ->
    update (p, f) i = Some (p', f').
Proof.
  intros. unfold update_top_inc, Option.bind2, Option.ret in *. repeat destr.
  inv Heqp1. now inv H.
Qed.

Lemma remember_expr_eq :
  forall l i f,
    remember_expr f (map snd l) i = map snd (GiblePargen.remember_expr f l i).
Proof.
  induction l; destruct i; auto.
Qed.

Lemma remember_expr_eq_inc :
  forall l i f,
    remember_expr_inc f (map snd l) i = map snd (GiblePargen.remember_expr_inc f l i).
Proof.
  unfold remember_expr_inc, GiblePargen.remember_expr_inc.
  induction l; destruct i; cbn; intros; repeat destruct_match; auto.
Qed.

Lemma equiv_update'_top:
  forall i p f l lm p' f' l' lm',
    update_top (p, f, l, lm) i = Some (p', f', l', lm') ->
    update' (p, f, map snd l, lm) i = Some (p', f', map snd l', lm').
Proof.
  intros. unfold update', update_top, Option.bind2, Option.ret in *. repeat destr.
  inv Heqp1. inv H. repeat f_equal. apply remember_expr_eq.
Qed.

Lemma equiv_update'_top_inc:
  forall i p f l lm p' f' l' lm',
    update_top_inc (p, f, l, lm) i = Some (p', f', l', lm') ->
    update'_inc (p, f, map snd l, lm) i = Some (p', f', map snd l', lm').
Proof.
  intros. unfold update'_inc, update_top_inc, Option.bind2, Option.ret in *. repeat destr.
  inv Heqp1. inv H. repeat f_equal. apply remember_expr_eq_inc.
Qed.

Lemma equiv_fold_update'_top:
  forall i p f l lm p' f' l' lm',
    mfold_left update_top i (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left update' i (Some (p, f, map snd l, lm)) = Some (p', f', map snd l', lm').
Proof.
  induction i; cbn -[update_top update'] in *; intros.
  - inv H; auto.
  - exploit OptionExtra.mfold_left_Some; eauto;
      intros [[[[p_mid f_mid] l_mid] lm_mid] HB].
    exploit equiv_update'_top; try eassumption.
    intros. rewrite H0. eapply IHi. rewrite HB in H. eauto.
Qed.

Lemma equiv_fold_update'_top_inc:
  forall i p f l lm p' f' l' lm',
    mfold_left update_top_inc i (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left update'_inc i (Some (p, f, map snd l, lm)) = Some (p', f', map snd l', lm').
Proof.
  induction i; cbn -[update_top_inc update'_inc] in *; intros.
  - inv H; auto.
  - exploit OptionExtra.mfold_left_Some; eauto;
      intros [[[[p_mid f_mid] l_mid] lm_mid] HB].
    exploit equiv_update'_top_inc; try eassumption.
    intros. rewrite H0. eapply IHi. rewrite HB in H. eauto.
Qed.

Lemma equiv_fold_update_top:
  forall i p f l lm p' f' l' lm',
    mfold_left update_top i (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left update i (Some (p, f)) = Some (p', f').
Proof.
  induction i; cbn -[update_top update] in *; intros.
  - inv H; auto.
  - exploit OptionExtra.mfold_left_Some; eauto;
      intros [[[[p_mid f_mid] l_mid] lm_mid] HB].
    exploit equiv_update_top; try eassumption.
    intros. rewrite H0. eapply IHi. rewrite HB in H. eauto.
Qed.

Lemma equiv_fold_update_top_inc:
  forall i p f l lm p' f' l' lm',
    mfold_left update_top_inc i (Some (p, f, l, lm)) = Some (p', f', l', lm') ->
    mfold_left update i (Some (p, f)) = Some (p', f').
Proof.
  induction i; cbn -[update_top_inc update] in *; intros.
  - inv H; auto.
  - exploit OptionExtra.mfold_left_Some; eauto;
      intros [[[[p_mid f_mid] l_mid] lm_mid] HB].
    exploit equiv_update_top_inc; try eassumption.
    intros. rewrite H0. eapply IHi. rewrite HB in H. eauto.
Qed.

Lemma top_implies_abstract_sequence :
  forall y f l1 l2,
    abstract_sequence_top y = Some (f, l1, l2) ->
    abstract_sequence y = Some f.
Proof.
  unfold abstract_sequence, abstract_sequence_top; intros.
  unfold Option.bind in *. repeat destr.
  inv H.
  unfold Option.map in *|-. repeat destr. subst. inv Heqo.
  erewrite equiv_fold_update_top by eauto. auto.
Qed.

Lemma top_implies_abstract_sequence_inc :
  forall y f l1 l2,
    abstract_sequence_top_inc y = Some (f, l1, l2) ->
    abstract_sequence y = Some f.
Proof.
  unfold abstract_sequence, abstract_sequence_top_inc; intros.
  unfold Option.bind in *. repeat destr.
  inv H.
  unfold Option.map in *|-. repeat destr. subst. inv Heqo.
  erewrite equiv_fold_update_top_inc by eauto. auto.
Qed.

Lemma top_implies_abstract_sequence' :
  forall y f l1 l2,
    abstract_sequence_top y = Some (f, l1, l2) ->
    abstract_sequence' y = Some (f, map snd l1, l2).
Proof.
  unfold abstract_sequence', abstract_sequence_top; intros.
  unfold Option.bind in *|-. repeat destr.
  inv H.
  unfold Option.map in *|-. repeat destr. subst. inv Heqo.
  exploit equiv_fold_update'_top; eauto; intros.
  setoid_rewrite H. cbn. setoid_rewrite Heqm. auto.
Qed.

Lemma top_implies_abstract_sequence'_inc :
  forall y f l1 l2,
    abstract_sequence_top_inc y = Some (f, l1, l2) ->
    abstract_sequence'_inc y = Some (f, map snd l1, l2).
Proof.
  unfold abstract_sequence'_inc, abstract_sequence_top_inc; intros.
  unfold Option.bind in *|-. repeat destr.
  inv H.
  unfold Option.map in *|-. repeat destr. subst. inv Heqo.
  exploit equiv_fold_update'_top_inc; eauto; intros.
  setoid_rewrite H. cbn. setoid_rewrite Heqm. auto.
Qed.

Definition state_lessdef := GiblePargenproofEquiv.match_states.

Definition match_prog (prog : GibleSeq.program) (tprog : GiblePar.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  intros. unfold transl_program, match_prog.
  eapply Linking.match_transform_partial_program; auto.
Qed.

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
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: GibleSeq.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
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
                  (fn_code (schedule f))
                  || check_scheduled_trees_inc
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

(*|
Proof sketch: This should follow directly from the correctness property, because
it states that we can execute the forest.
|*)

  Lemma eval_forest_gather_predicates :
    forall G A B a_sem i0 sp ge x p f p' f' pe pe_val preds preds',
      update (p, f) x = Some (p', f') ->
      gather_predicates preds x = Some preds' ->
      @sem_pred_expr G A B f.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val ->
      NE.Forall (fun x => forall pred, PredIn pred (fst x) -> preds ! pred = Some tt) pe ->
      sem_pred_expr f'.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val.
  Proof.
    intros.
    eapply abstr_seq_revers_correct_fold_sem_pexpr_eval_sem; eauto.
    apply NE.Forall_forall. intros [pe_op a] YIN pred_tmp YPREDIN.
    apply NE.Forall_forall with (x:=(pe_op, a)) in H2; auto.
    specialize (H2 pred_tmp YPREDIN).
    cbn [fst snd] in *.
    eapply abstr_seq_revers_correct_fold_sem_pexpr_sem2; eauto.
  Qed.

  Lemma eval_forest_gather_predicates_fold :
    forall G A B a_sem i0 sp ge x p f p' f' pe pe_val preds preds' l l_m l' l_m',
      OptionExtra.mfold_left update_top x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      OptionExtra.mfold_left gather_predicates x (Some preds) = Some preds' ->
      @sem_pred_expr G A B f.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val ->
      NE.Forall (fun x => forall pred, PredIn pred (fst x) -> preds ! pred = Some tt) pe ->
      sem_pred_expr f'.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val.
  Proof.
    induction x.
    - intros * HF; cbn in *. now inv HF.
    - intros * HFOLD1 HFOLD2 HSEM HFRL.
      cbn -[update] in *.
      exploit OptionExtra.mfold_left_Some. eapply HFOLD1.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HSTATE].
      rewrite HSTATE in HFOLD1.
      exploit OptionExtra.mfold_left_Some. eapply HFOLD2.
      intros [preds_mid HPRED]. rewrite HPRED in HFOLD2.
      unfold Option.bind2, Option.ret in HSTATE; repeat destr; subst. inv HSTATE.
      eapply IHx; eauto using eval_forest_gather_predicates.
      eapply NE.Forall_forall; intros.
      eapply gather_predicates_in; eauto.
      eapply NE.Forall_forall in HFRL; eauto.
  Qed.

  Lemma eval_forest_gather_predicates_fold_inc :
    forall G A B a_sem i0 sp ge x p f p' f' pe pe_val preds preds' l l_m l' l_m',
      OptionExtra.mfold_left update_top_inc x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      OptionExtra.mfold_left gather_predicates x (Some preds) = Some preds' ->
      @sem_pred_expr G A B f.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val ->
      NE.Forall (fun x => forall pred, PredIn pred (fst x) -> preds ! pred = Some tt) pe ->
      sem_pred_expr f'.(forest_preds) a_sem (mk_ctx i0 sp ge) pe pe_val.
  Proof.
    induction x.
    - intros * HF; cbn in *. now inv HF.
    - intros * HFOLD1 HFOLD2 HSEM HFRL.
      cbn -[update] in *.
      exploit OptionExtra.mfold_left_Some. eapply HFOLD1.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HSTATE].
      rewrite HSTATE in HFOLD1.
      exploit OptionExtra.mfold_left_Some. eapply HFOLD2.
      intros [preds_mid HPRED]. rewrite HPRED in HFOLD2.
      unfold Option.bind2, Option.ret in HSTATE; repeat destr; subst. inv HSTATE.
      eapply IHx; eauto using eval_forest_gather_predicates.
      eapply NE.Forall_forall; intros.
      eapply gather_predicates_in; eauto.
      eapply NE.Forall_forall in HFRL; eauto.
  Qed.

  Lemma abstract_sequence_evaluable_fold2 :
    forall x sp i i' i0 cf p f l l_m p' f' l' l_m' preds preds',
      sem (mk_ctx i0 sp ge) f (i, Some cf) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = false ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l) ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l').
  Proof.
    induction x; cbn -[update]; intros * HSEM HSEM2 HPRED HGATHER HALL HPIN **.
    - inv H. auto.
    - exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      unfold evaluable_pred_list in *; intros.
      eapply IHx. 7: { eauto. }
      + eapply abstr_fold_falsy. eapply HSEM. instantiate (3 := (a :: nil)).
        cbn -[update]. eauto. auto.
      + eauto.
      + destruct i. eapply sem_update_falsy_input; eauto.
      + eauto.
      + eapply gather_predicates_in_forest; eauto.
      + eapply gather_predicates_update_constant; eauto.
      + intros.
        { destruct a; cbn -[gather_predicates update] in *; eauto.
          - inv H2; eauto.
            inv HSEM. inv H4.
            unfold evaluable_pred_expr. exists (rs' !! r).
            eapply eval_forest_gather_predicates_fold; eauto.
            eapply eval_forest_gather_predicates; eauto.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HALL; eauto.
            specialize (HALL _ H4).
            eapply gather_predicates_in; eauto.
          - inv H2; eauto.
            inv HSEM. inv H4.
            unfold evaluable_pred_expr. exists (rs' !! r).
            eapply eval_forest_gather_predicates_fold; eauto.
            eapply eval_forest_gather_predicates; eauto.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HALL; eauto.
            specialize (HALL _ H4).
            eapply gather_predicates_in; eauto.
        }
      + eauto.
  Qed.

  Lemma abstract_sequence_evaluable_fold :
    forall x sp i i' ti' i0 cf p f l l_m p' f' l' l_m' preds preds',
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem (mk_ctx i0 sp ge) f (i, None) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = true ->
      GiblePargenproofCommon.valid_mem (is_mem i0) (is_mem i) ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l) ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l').
  Proof.
    induction x; cbn -[update]; intros * ? HLESSDEF HSEM HSEM2 HPRED HVALID_MEM HGATHER HALL HPREDALL **.
    - inv H0. auto.
    - exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H0. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      inv H.
      + unfold evaluable_pred_list; intros. exploit IHx.
        eauto. eauto. eapply sem_update_instr; eauto.
        eauto. eapply eval_predf_update_true; eauto.
        transitivity (is_mem i); auto. eapply sem_update_valid_mem; eauto.
        eauto. eapply gather_predicates_in_forest; eauto. eapply gather_predicates_update_constant; eauto.
        eauto. unfold evaluable_pred_list in *; intros.
        { destruct a; cbn -[gather_predicates update] in *; eauto.
          - inv H2; eauto.
            inv HSEM. inv H4.
            unfold evaluable_pred_expr. exists (rs' !! r).
            eapply eval_forest_gather_predicates_fold; eauto.
            eapply eval_forest_gather_predicates; eauto.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HALL; eauto.
            specialize (HALL _ H4).
            eapply gather_predicates_in; eauto.
          - inv H2; eauto.
            inv HSEM. inv H4.
            unfold evaluable_pred_expr. exists (rs' !! r).
            eapply eval_forest_gather_predicates_fold; eauto.
            eapply eval_forest_gather_predicates; eauto.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HALL; eauto.
            specialize (HALL _ H4).
            eapply gather_predicates_in; eauto.
        }
        eauto. auto.
      + unfold evaluable_pred_list in *; intros.
        inversion H5; subst.
        exploit sem_update_instr_term; eauto; intros [HSEM3 HEVAL_PRED].
        eapply abstract_sequence_evaluable_fold2; eauto using
          gather_predicates_in_forest, gather_predicates_update_constant.
  Qed.

  Opaque app_predicated.

  Lemma abstract_sequence_evaluable_fold2_inc :
    forall x sp i i' i0 cf p f l l_m p' f' l' l_m' preds preds',
      sem (mk_ctx i0 sp ge) f (i, Some cf) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = false ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top_inc x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l) ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l').
  Proof.
    induction x; intros * HSEM HSEM2 HPRED HGATHER HALL HPIN **.
    - inv H. auto.
    - exploit abstr_fold_falsy. apply HSEM.
            eapply equiv_fold_update_top_inc; eauto. eauto. intros HSEM3. cbn -[update] in *. exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      unfold evaluable_pred_list in *; intros.
      eapply IHx. 7: { eauto. }
      + eapply abstr_fold_falsy. eapply HSEM. instantiate (3 := (a :: nil)).
        cbn -[update]. eauto. auto.
      + eauto.
      + destruct i. eapply sem_update_falsy_input; eauto.
      + eauto.
      + eapply gather_predicates_in_forest; eauto.
      + eapply gather_predicates_update_constant; eauto.
      + intros.
        { destruct a; cbn -[gather_predicates update seq_app remember_expr_inc remember_expr_m_inc] in *; eauto.
          - inv H2; eauto. exists (is_rs i0)!!1. inv HSEM3. inv H5.
            eapply AbstrSemIdent.sem_pred_expr_app_predicated_false. repeat constructor. eauto.
            rewrite eval_predf_Pand. cbn in *. rewrite HPRED. auto with bool.
            - inv H2; eauto. exists (is_rs i0)!!1. inv HSEM3. inv H5.
            eapply AbstrSemIdent.sem_pred_expr_app_predicated_false. repeat constructor. eauto.
            rewrite eval_predf_Pand. cbn in *. rewrite HPRED. auto with bool.
        }
      + eauto.
  Qed.

  Lemma abstract_sequence_evaluable_fold_inc :
    forall x sp i i' ti' i0 cf p f l l_m p' f' l' l_m' preds preds',
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem (mk_ctx i0 sp ge) f (i, None) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = true ->
      GiblePargenproofCommon.valid_mem (is_mem i0) (is_mem i) ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top_inc x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l) ->
      evaluable_pred_list (mk_ctx i0 sp ge) f'.(forest_preds) (map snd l').
  Proof.
    induction x; cbn -[update seq_app remember_expr_inc remember_expr_m_inc]; intros * ? HLESSDEF HSEM HSEM2 HPRED HVALID_MEM HGATHER HALL HPREDALL **.
    - inv H0. auto.
    - exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H0. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      inv H.
      + unfold evaluable_pred_list; intros. exploit IHx.
        eauto. eauto. eapply sem_update_instr; eauto.
        eauto. eapply eval_predf_update_true; eauto.
        transitivity (is_mem i); auto. eapply sem_update_valid_mem; eauto.
        eauto. eapply gather_predicates_in_forest; eauto. eapply gather_predicates_update_constant; eauto.
        eauto. unfold evaluable_pred_list in *; intros.
        { destruct a; cbn -[gather_predicates update seq_app remember_expr_inc remember_expr_m_inc] in *; eauto.
          - inv H2; eauto.
            exploit sem_update_instr; eauto. intros. inv H2. inv H5. specialize (H2 r).
            inv HSEM. inv H8.
            exploit gather_predicates_in_forest; eauto. instantiate (1:=Reg r). intros HPRED_IN.
            unfold update, Option.bind in Heqo. destruct_match; try discriminate. inv Heqo.
            rewrite forest_reg_gss in H2.
            exploit eval_forest_gather_predicates_fold_inc. eauto. eauto. apply H2.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HPRED_IN; eauto.
            rewrite forest_reg_gss. auto. intros HSEMEXEC.
            inv HSEM2. inv H13. exploit AbstrSemIdent.sem_pred_expr_prune_predicated2. eauto.
            apply HSEMEXEC. eassumption.
            intros HSEM_APP.
            case_eq (eval_predf pr'1 (dfltp o ∧ p_mid)); intros.
            + exists rs'!!r. eapply AbstrSemIdent.sem_pred_expr_app_predicated; eauto.
              eapply AbstrSemIdent.sem_pred_expr_app_predicated2; eauto.
            + exists (is_rs i0)!!1. eapply AbstrSemIdent.sem_pred_expr_app_predicated_false; eauto.
              repeat constructor.
          - inv H2; eauto.
            exploit sem_update_instr; eauto. intros. inv H2. inv H5. specialize (H2 r).
            inv HSEM. inv H8.
            exploit gather_predicates_in_forest; eauto. instantiate (1:=Reg r). intros HPRED_IN.
            unfold update, Option.bind in Heqo. destruct_match; try discriminate. inv Heqo.
            rewrite forest_reg_gss in H2.
            exploit eval_forest_gather_predicates_fold_inc. eauto. eauto. apply H2.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HPRED_IN; eauto.
            rewrite forest_reg_gss. auto. intros HSEMEXEC.
            inv HSEM2. inv H13. exploit AbstrSemIdent.sem_pred_expr_prune_predicated2. eauto.
            apply HSEMEXEC. eassumption.
            intros HSEM_APP.
            case_eq (eval_predf pr'1 (dfltp o ∧ p_mid)); intros.
            + exists rs'!!r. eapply AbstrSemIdent.sem_pred_expr_app_predicated; eauto.
              eapply AbstrSemIdent.sem_pred_expr_app_predicated2; eauto.
            + exists (is_rs i0)!!1. eapply AbstrSemIdent.sem_pred_expr_app_predicated_false; eauto.
              repeat constructor.
        }
        eauto. auto.
      + unfold evaluable_pred_list in *; intros.
        inversion H5; subst.
        exploit sem_update_instr_term; eauto; intros [HSEM3 HEVAL_PRED].
        eapply abstract_sequence_evaluable_fold2_inc; eauto using
          gather_predicates_in_forest, gather_predicates_update_constant.
  Qed.

  Lemma abstract_sequence_evaluable_fold2_m :
    forall x sp i i' i0 cf p f l l_m p' f' l' l_m' preds preds',
      sem (mk_ctx i0 sp ge) f (i, Some cf) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = false ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m'.
  Proof.
    induction x; cbn -[update]; intros * HSEM HSEM2 HPRED HGATHER HALL HPIN **.
    - inv H. auto.
    - exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      unfold evaluable_pred_list_m in *; intros.
      eapply IHx. 7: { eauto. }
      + eapply abstr_fold_falsy. eapply HSEM. instantiate (3 := (a :: nil)).
        cbn -[update]. eauto. auto.
      + eauto.
      + destruct i. eapply sem_update_falsy_input; eauto.
      + eauto.
      + eapply gather_predicates_in_forest; eauto.
      + eapply gather_predicates_update_constant; eauto.
      + intros.
        { destruct a; cbn -[gather_predicates update] in *; eauto.
          inv H2; eauto.
          inv HSEM.
          unfold evaluable_pred_expr_m. exists m'.
          eapply eval_forest_gather_predicates_fold; eauto.
          eapply eval_forest_gather_predicates; eauto.
          eapply NE.Forall_forall; intros.
          eapply NE.Forall_forall in HALL; eauto.
          specialize (HALL _ H3).
          eapply gather_predicates_in; eauto.
        }
      + eauto.
  Qed.

  Lemma abstract_sequence_evaluable_fold_m :
    forall x sp i i' ti' i0 cf p f l l_m p' f' l' l_m' preds preds',
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem (mk_ctx i0 sp ge) f (i, None) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = true ->
      GiblePargenproofCommon.valid_mem (is_mem i0) (is_mem i) ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m'.
  Proof.
    induction x; cbn -[update]; intros * ? HLESSDEF HSEM HSEM2 HPRED HVALID_MEM HGATHER HALL HPREDALL **.
    - inv H0. auto.
    - exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H0. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      inv H.
      + unfold evaluable_pred_list_m; intros. exploit IHx.
        eauto. eauto. eapply sem_update_instr; eauto.
        eauto. eapply eval_predf_update_true; eauto.
        transitivity (is_mem i); auto. eapply sem_update_valid_mem; eauto.
        eauto. eapply gather_predicates_in_forest; eauto. eapply gather_predicates_update_constant; eauto.
        eauto. unfold evaluable_pred_list_m in *; intros.
        { destruct a; cbn -[gather_predicates update] in *; eauto.
          inv H2; eauto.
          inv HSEM.
          unfold evaluable_pred_expr_m. exists m'.
          eapply eval_forest_gather_predicates_fold; eauto.
          eapply eval_forest_gather_predicates; eauto.
          eapply NE.Forall_forall; intros.
          eapply NE.Forall_forall in HALL; eauto.
          specialize (HALL _ H3).
          eapply gather_predicates_in; eauto.
        }
        eauto. auto.
      + unfold evaluable_pred_list_m in *; intros.
        inversion H5; subst.
        exploit sem_update_instr_term; eauto; intros [HSEM3 HEVAL_PRED].
        eapply abstract_sequence_evaluable_fold2_m; eauto using
          gather_predicates_in_forest, gather_predicates_update_constant.
Qed.

  Lemma abstract_sequence_evaluable_fold2_m_inc :
    forall x sp i i' i0 cf p f l l_m p' f' l' l_m' preds preds',
      sem (mk_ctx i0 sp ge) f (i, Some cf) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = false ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top_inc x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m'.
  Proof.
    induction x; intros * HSEM HSEM2 HPRED HGATHER HALL HPIN **.
    - inv H. auto.
    - exploit abstr_fold_falsy. apply HSEM.
            eapply equiv_fold_update_top_inc; eauto. eauto. intros HSEM3. cbn -[update] in *. exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      unfold evaluable_pred_list_m in *; intros.
      eapply IHx. 7: { eauto. }
      + eapply abstr_fold_falsy. eapply HSEM. instantiate (3 := (a :: nil)).
        cbn -[update]. eauto. auto.
      + eauto.
      + destruct i. eapply sem_update_falsy_input; eauto.
      + eauto.
      + eapply gather_predicates_in_forest; eauto.
      + eapply gather_predicates_update_constant; eauto.
      + intros.
        { destruct a; cbn -[gather_predicates update seq_app remember_expr_inc remember_expr_m_inc] in *; eauto.
          - inv H2; eauto. exists (is_mem i0). inv HSEM3. inv H5.
            eapply AbstrSemIdent.sem_pred_expr_app_predicated_false. repeat constructor. eauto.
            rewrite eval_predf_Pand. cbn in *. rewrite HPRED. auto with bool.
        }
      + eauto.
  Qed.

  Lemma abstract_sequence_evaluable_fold_m_inc :
    forall x sp i i' ti' i0 cf p f l l_m p' f' l' l_m' preds preds',
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem (mk_ctx i0 sp ge) f (i, None) ->
      sem (mk_ctx i0 sp ge) f' (i', Some cf) ->
      eval_predf (is_ps i) p = true ->
      GiblePargenproofCommon.valid_mem (is_mem i0) (is_mem i) ->
      mfold_left gather_predicates x (Some preds) = Some preds' ->
      all_preds_in f preds ->
      (forall in_pred : Predicate.predicate, PredIn in_pred p -> preds ! in_pred = Some tt) ->
      OptionExtra.mfold_left update_top_inc x (Some (p, f, l, l_m)) = Some (p', f', l', l_m') ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m ->
      evaluable_pred_list_m (mk_ctx i0 sp ge) f'.(forest_preds) l_m'.
  Proof.
    induction x; cbn -[update seq_app remember_expr_inc remember_expr_m_inc]; intros * ? HLESSDEF HSEM HSEM2 HPRED HVALID_MEM HGATHER HALL HPREDALL **.
    - inv H0. auto.
    - exploit OptionExtra.mfold_left_Some. eassumption.
      intros [[[[p_mid f_mid] l_mid] l_m_mid] HBIND].
      rewrite HBIND in H0. unfold Option.bind2, Option.ret in HBIND; repeat destr; subst.
      inv HBIND.
      exploit OptionExtra.mfold_left_Some. eapply HGATHER.
      intros [preds_mid HGATHER0]. rewrite HGATHER0 in HGATHER.
      inv H.
      + unfold evaluable_pred_list_m; intros. exploit IHx.
        eauto. eauto. eapply sem_update_instr; eauto.
        eauto. eapply eval_predf_update_true; eauto.
        transitivity (is_mem i); auto. eapply sem_update_valid_mem; eauto.
        eauto. eapply gather_predicates_in_forest; eauto. eapply gather_predicates_update_constant; eauto.
        eauto. unfold evaluable_pred_list_m in *; intros.
        { destruct a; cbn -[gather_predicates update seq_app remember_expr_inc remember_expr_m_inc] in *; eauto.
          - inv H2; eauto.
            exploit sem_update_instr; eauto. intros. inv H2. inv H5. specialize (H2 r).
            inv HSEM. inv H8.
            exploit gather_predicates_in_forest; eauto. instantiate (1:=Mem). intros HPRED_IN.
            unfold update, Option.bind in Heqo. destruct_match; try discriminate. inv Heqo.
            rewrite forest_reg_gss in H11.
            exploit eval_forest_gather_predicates_fold_inc. eauto. eauto. apply H11.
            eapply NE.Forall_forall; intros.
            eapply NE.Forall_forall in HPRED_IN; eauto.
            rewrite forest_reg_gss. auto. intros HSEMEXEC.
            inv HSEM2. inv H13. exploit AbstrSemIdent.sem_pred_expr_prune_predicated2. eauto.
            apply HSEMEXEC. eassumption.
            intros HSEM_APP.
            case_eq (eval_predf pr'1 (dfltp o ∧ p_mid)); intros.
            + exists m'. eapply AbstrSemIdent.sem_pred_expr_app_predicated; eauto.
              eapply AbstrSemIdent.sem_pred_expr_app_predicated2; eauto.
            + exists (is_mem i0). eapply AbstrSemIdent.sem_pred_expr_app_predicated_false; eauto.
              repeat constructor.
        }
        eauto. auto.
      + unfold evaluable_pred_list in *; intros.
        inversion H5; subst.
        exploit sem_update_instr_term; eauto; intros [HSEM3 HEVAL_PRED].
        eapply abstract_sequence_evaluable_fold2_m_inc; eauto using
          gather_predicates_in_forest, gather_predicates_update_constant.
  Qed.

(*|
Proof sketch: If I can execute the list of instructions, then every single
forest element that is added to the forest will be evaluable too.  This then
means that if we gather these in a list, that everything in the list should also
have been evaluable.
|*)

  Lemma abstract_sequence_evaluable :
    forall sp x i i' ti' cf f l0 l,
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem {| ctx_is := i; ctx_sp := sp; ctx_ge := ge |} f (i', Some cf) ->
      abstract_sequence_top x = Some (f, l0, l) ->
      evaluable_pred_list (mk_ctx i sp ge) f.(forest_preds) (map snd l0).
  Proof.
    intros * ? HLESSDEF **. unfold abstract_sequence_top in *.
    unfold Option.bind, Option.map in H1; repeat destr.
    inv H1. inv Heqo.
    eapply abstract_sequence_evaluable_fold; eauto; auto.
    - apply sem_empty.
    - reflexivity.
    - apply all_preds_in_empty.
    - inversion 1.
    - cbn; unfold evaluable_pred_list; inversion 1.
  Qed.

  Lemma abstract_sequence_evaluable_inc :
    forall sp x i i' ti' cf f l0 l,
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem {| ctx_is := i; ctx_sp := sp; ctx_ge := ge |} f (i', Some cf) ->
      abstract_sequence_top_inc x = Some (f, l0, l) ->
      evaluable_pred_list (mk_ctx i sp ge) f.(forest_preds) (map snd l0).
  Proof.
    intros * ? HLESSDEF **. unfold abstract_sequence_top_inc in *.
    unfold Option.bind, Option.map in H1; repeat destr.
    inv H1. inv Heqo.
    eapply abstract_sequence_evaluable_fold_inc; eauto; auto.
    - apply sem_empty.
    - reflexivity.
    - apply all_preds_in_empty.
    - inversion 1.
    - cbn; unfold evaluable_pred_list; inversion 1.
  Qed.

  Lemma abstract_sequence_evaluable_m :
    forall sp x i i' ti' cf f l0 l,
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem {| ctx_is := i; ctx_sp := sp; ctx_ge := ge |} f (i', Some cf) ->
      abstract_sequence_top x = Some (f, l0, l) ->
      evaluable_pred_list_m (mk_ctx i sp ge) f.(forest_preds) l.
  Proof.
    intros * ? HLESSDEF **. unfold abstract_sequence_top in *.
    unfold Option.bind, Option.map in H1; repeat destr.
    inv H1. inv Heqo.
    eapply abstract_sequence_evaluable_fold_m; eauto; auto.
    - apply sem_empty.
    - reflexivity.
    - apply all_preds_in_empty.
    - inversion 1.
    - cbn; unfold evaluable_pred_list; inversion 1.
  Qed.

  Lemma abstract_sequence_evaluable_m_inc :
    forall sp x i i' ti' cf f l0 l,
      SeqBB.step ge sp (Iexec i) x (Iterm ti' cf) ->
      state_lessdef i' ti' ->
      sem {| ctx_is := i; ctx_sp := sp; ctx_ge := ge |} f (i', Some cf) ->
      abstract_sequence_top_inc x = Some (f, l0, l) ->
      evaluable_pred_list_m (mk_ctx i sp ge) f.(forest_preds) l.
  Proof.
    intros * ? HLESSDEF **. unfold abstract_sequence_top_inc in *.
    unfold Option.bind, Option.map in H1; repeat destr.
    inv H1. inv Heqo.
    eapply abstract_sequence_evaluable_fold_m_inc; eauto; auto.
    - apply sem_empty.
    - reflexivity.
    - apply all_preds_in_empty.
    - inversion 1.
    - cbn; unfold evaluable_pred_list; inversion 1.
  Qed.

  Lemma check_evaluability1_evaluable :
    forall G (ctx: @Abstr.ctx G) l1 l2 f ps,
      (forall x : positive, sem_pexpr ctx (get_forest_p' x f) ps !! x) ->
      check_evaluability1 l1 l2 = true ->
      evaluable_pred_list ctx f (map snd l1) ->
      evaluable_pred_list ctx f (map snd l2).
  Proof.
    unfold check_evaluability1; intros * HPREDS H H0.
    unfold evaluable_pred_list, evaluable_pred_expr in *; intros p H1.
    exploit list_in_map_inv; eauto.
    intros [[res expr] [HTEMP HIN]]; subst; cbn in *.
    eapply forallb_forall in H; eauto.
    apply existsb_exists in H.
    inversion_clear H as [[res' expr'] [HIN' HRES']].
    simplify.
    pose proof H2 as HCHECKEXPR.
    pose proof H4 as HCHECKEXPR'.
    pose proof H as HRESEQ.
    pose proof H5 as HBEQ.
    clear H2 H4 H H5.
    destruct (resource_eq res' res); subst; [|discriminate].
    assert (XX: In expr' (map snd l1)).
    { replace expr' with (snd (res, expr')) by auto. now apply in_map. }
    apply H0 in XX.
    inversion_clear XX as [v HSEM].
    exists v. eapply HN.beq_pred_expr_correct_top;
    eauto using check_mutexcl_correct.
    auto.
  Qed.

  Lemma check_evaluability2_evaluable :
    forall G (ctx: @Abstr.ctx G) l1 l2 f ps,
      (forall x : positive, sem_pexpr ctx (get_forest_p' x f) ps !! x) ->
      check_evaluability2 l1 l2 = true ->
      evaluable_pred_list_m ctx f l1 ->
      evaluable_pred_list_m ctx f l2.
  Proof.
    unfold check_evaluability1; intros * HPREDS H H0.
    unfold evaluable_pred_list_m, evaluable_pred_expr_m in *; intros p H1.
    eapply forallb_forall in H; eauto.
    apply existsb_exists in H.
    inversion_clear H as [expr' [HIN' HRES']].
    simplify.
    pose proof H2 as HCHECKEXPR.
    pose proof H4 as HCHECKEXPR'.
    pose proof H3 as HBEQ.
    clear H2 H4 H3.
    apply H0 in HIN'.
    inversion_clear HIN' as [v HSEM].
    exists v. eapply HN.beq_pred_expr_correct_top;
    eauto using check_mutexcl_correct.
    auto.
  Qed.

  Lemma evaluable_same_preds :
    forall G (ctx: @Abstr.ctx G) f f' l1,
      PTree.beq beq_pred_pexpr f f' = true ->
      evaluable_pred_list ctx f l1 ->
      evaluable_pred_list ctx f' l1.
  Proof.
    unfold evaluable_pred_list, evaluable_pred_expr in *; intros.
    apply H0 in H1; simplify. exists x.
    eapply sem_pred_exec_beq_correct; eauto.
  Qed.

  Lemma evaluable_same_state :
    forall G i i' sp (ge: Genv.t G unit) f l1,
      state_lessdef i i' ->
      evaluable_pred_list (mk_ctx i sp ge) f l1 ->
      evaluable_pred_list (mk_ctx i' sp ge) f l1.
  Proof.
    unfold evaluable_pred_list, evaluable_pred_expr in *; intros.
    apply H0 in H1. simplify. exists x.
    eapply sem_pred_expr_corr. 3: { eauto. }
    constructor; auto. unfold ge_preserved; auto.
    apply sem_value_corr.
    constructor; auto. unfold ge_preserved; auto.
  Qed.

  Lemma evaluable_same_preds_m :
    forall G (ctx: @Abstr.ctx G) f f' l1,
      PTree.beq beq_pred_pexpr f f' = true ->
      evaluable_pred_list_m ctx f l1 ->
      evaluable_pred_list_m ctx f' l1.
  Proof.
    unfold evaluable_pred_list_m, evaluable_pred_expr_m in *; intros.
    apply H0 in H1; simplify. exists x.
    eapply sem_pred_exec_beq_correct; eauto.
  Qed.

  Lemma evaluable_same_state_m :
    forall G i i' sp (ge: Genv.t G unit) f l1,
      state_lessdef i i' ->
      evaluable_pred_list_m (mk_ctx i sp ge) f l1 ->
      evaluable_pred_list_m (mk_ctx i' sp ge) f l1.
  Proof.
    unfold evaluable_pred_list_m, evaluable_pred_expr_m in *; intros.
    apply H0 in H1. simplify. exists x.
    eapply sem_pred_expr_corr. 3: { eauto. }
    constructor; auto. unfold ge_preserved; auto.
    apply sem_mem_corr.
    constructor; auto. unfold ge_preserved; auto.
  Qed.

(* abstract_sequence_top x = Some (f, l0, l) -> *)

  Lemma schedule_oracle_correct :
    forall x y sp i i' ti cf,
      schedule_oracle x y = true ->
      SeqBB.step ge sp (Iexec i) x (Iterm i' cf) ->
      state_lessdef i ti ->
      exists ti', ParBB.step tge sp (Iexec ti) y (Iterm ti' cf)
             /\ state_lessdef i' ti'.
  Proof.
    unfold schedule_oracle; intros. repeat (destruct_match; try discriminate). simplify.
    exploit top_implies_abstract_sequence; [eapply Heqo|]; intros.
    exploit top_implies_abstract_sequence'; eauto; intros.
    exploit abstr_sequence_correct; eauto; simplify.
    exploit local_abstr_check_correct2; eauto.
    { constructor. eapply ge_preserved_refl. reflexivity. }
(*    { inv H. inv H8. exists pr'. intros x0. specialize (H x0). auto. } *)
    simplify.
    exploit abstr_seq_reverse_correct; eauto.
    { inv H8. inv H14.
      eapply check_evaluability1_evaluable.
      eauto. eauto.
      eapply evaluable_same_preds. unfold check in *. simplify. eauto.
      eapply evaluable_same_state; eauto.
      eapply abstract_sequence_evaluable. eauto. symmetry; eauto.
      eapply sem_correct; eauto.
      { constructor. constructor; auto. symmetry; auto. }
      eauto.
    }
    { inv H8. inv H14.
      eapply check_evaluability2_evaluable.
      eauto. eauto.
      eapply evaluable_same_preds_m. unfold check in *. simplify. eauto.
      eapply evaluable_same_state_m; eauto.
      eapply abstract_sequence_evaluable_m. eauto. symmetry; eauto.
      eapply sem_correct; eauto.
      { constructor. constructor; auto. symmetry; auto. }
      eauto.
    }
    reflexivity. simplify.
    exploit seqbb_step_parbb_step; eauto; intros.
    econstructor; split; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
  Qed.

  Lemma schedule_oracle_correct_inc:
    forall x y sp i i' ti cf,
      schedule_oracle_inc x y = true ->
      SeqBB.step ge sp (Iexec i) x (Iterm i' cf) ->
      state_lessdef i ti ->
      exists ti', ParBB.step tge sp (Iexec ti) y (Iterm ti' cf)
             /\ state_lessdef i' ti'.
  Proof.
    unfold schedule_oracle_inc; intros. repeat (destruct_match; try discriminate). simplify.
    exploit top_implies_abstract_sequence_inc; [eapply Heqo|]; intros.
    exploit top_implies_abstract_sequence'_inc; eauto; intros.
    exploit abstr_sequence_correct; eauto; simplify.
    exploit local_abstr_check_correct2; eauto.
    { constructor. eapply ge_preserved_refl. reflexivity. }
(*    { inv H. inv H8. exists pr'. intros x0. specialize (H x0). auto. } *)
    simplify.
    exploit abstr_seq_reverse_correct_inc; eauto.
    { inv H8. inv H14.
      eapply check_evaluability1_evaluable.
      eauto. eauto.
      eapply evaluable_same_preds. unfold check in *. simplify. eauto.
      eapply evaluable_same_state; eauto.
      eapply abstract_sequence_evaluable_inc. eauto. symmetry; eauto.
      eapply sem_correct; eauto.
      { constructor. constructor; auto. symmetry; auto. }
      eauto.
    }
    { inv H8. inv H14.
      eapply check_evaluability2_evaluable.
      eauto. eauto.
      eapply evaluable_same_preds_m. unfold check in *. simplify. eauto.
      eapply evaluable_same_state_m; eauto.
      eapply abstract_sequence_evaluable_m_inc. eauto. symmetry; eauto.
      eapply sem_correct; eauto.
      { constructor. constructor; auto. symmetry; auto. }
      eauto.
    }
    reflexivity. simplify.
    exploit seqbb_step_parbb_step; eauto; intros.
    econstructor; split; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
  Qed.

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
    inversion 1; subst; clear H; inversion 1; subst; clear H.
    - exploit find_function_translated; eauto; simplify.
      econstructor; split.
      + constructor; eauto using sig_transl_function.
      + replace (rs' ## args) with (rs ## args).
        now (repeat (constructor; auto)).
        erewrite map_ext; auto.
    - exploit find_function_translated; eauto; simplify.
      econstructor; split.
      + constructor; eauto using sig_transl_function.
        unfold transl_function in TRANSL0. destruct_match; try discriminate.
        inv TRANSL0. eauto.
      + replace (rs' ## args) with (rs ## args).
        now (repeat (constructor; auto)).
        erewrite map_ext; auto.
    - econstructor; split.
      + econstructor; eauto using sig_transl_function.
        eapply Events.eval_builtin_args_preserved; eauto.
        eapply eval_builtin_args_eq; eauto.
        auto.
      + constructor; auto.
        unfold regmap_setres; intros. destruct_match; auto.
        subst. destruct (peq x0 x); subst.
        * now rewrite ! PMap.gss.
        * now rewrite ! PMap.gso by auto.
    - econstructor; split.
      + econstructor; eauto. eapply Op.eval_condition_lessdef; eauto.
        replace (rs' ## args) with (rs ## args).
        apply regs_lessdef_regs.
        unfold regs_lessdef; auto.
        erewrite map_ext; auto.
        apply Mem.extends_refl.
      + constructor; auto.
    - econstructor; split.
      + econstructor; eauto. now rewrite <- REG.
      + constructor; auto.
    - econstructor; split.
      + econstructor; eauto. unfold transl_function in TRANSL0.
        destruct_match; try discriminate. inv TRANSL0. eauto.
      + replace (regmap_optget or Vundef rs') with (regmap_optget or Vundef rs).
        constructor; auto. unfold regmap_optget. destruct_match; auto.
    - econstructor; split.
      + econstructor; eauto.
      + constructor; auto.
  Qed.

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
    { apply orb_prop in Heqb. inv Heqb. 
    { eapply check_scheduled_trees_correct in H3; [| solve [eauto] ].
      inv H3.  inv H4.
       exploit schedule_oracle_correct; eauto. constructor; eauto. simplify.
      destruct x0.
      pose proof H2 as X. eapply match_states_stepBB in X; eauto.
      exploit step_cf_correct; eauto. simplify.
      eexists; split. apply Smallstep.plus_one.
      econstructor; eauto. auto. }
      { eapply check_scheduled_trees_correct_inc in H3; [| solve [eauto] ].
      inv H3.  inv H4.
       exploit schedule_oracle_correct_inc; eauto. constructor; eauto. simplify.
      destruct x0.
      pose proof H2 as X. eapply match_states_stepBB in X; eauto.
      exploit step_cf_correct; eauto. simplify.
      eexists; split. apply Smallstep.plus_one.
      econstructor; eauto. auto. }
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
