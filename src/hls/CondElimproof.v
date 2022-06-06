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

================
RTLBlockgenproof
================

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
Require Import vericert.hls.CondElim.
Require Import vericert.hls.Predicate.

#[local] Open Scope positive.

Lemma forbidden_term_trans :
  forall A B ge sp i c b i' c',
    ~ @SeqBB.step A B ge sp (Iterm i c) b (Iterm i' c').
Proof. induction b; unfold not; intros; inv H. Qed.

Lemma step_instr_false :
  forall A B ge sp i c a i0,
    ~ @step_instr A B ge sp (Iterm i c) a (Iexec i0).
Proof. destruct a; unfold not; intros; inv H. Qed.

Lemma step_list2_false :
  forall A B ge l0 sp i c i0',
    ~ step_list2 (@step_instr A B ge) sp (Iterm i c) l0 (Iexec i0').
Proof.
  induction l0; unfold not; intros.
  inv H. inv H. destruct i1. eapply step_instr_false in H4. auto.
  eapply IHl0; eauto.
Qed.

Lemma append' :
  forall A B l0 cf i0 i1 l1 sp ge i0',
    step_list2 (@step_instr A B ge) sp (Iexec i0) l0 (Iexec i0') ->
    @SeqBB.step A B ge sp (Iexec i0') l1 (Iterm i1 cf) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof.
  induction l0; crush. inv H. eauto. inv H. destruct i3.
  econstructor; eauto. eapply IHl0; eauto.
  eapply step_list2_false in H7. exfalso; auto.
Qed.

Lemma append :
  forall A B cf i0 i1 l0 l1 sp ge,
      (exists i0', step_list2 (@step_instr A B ge) sp (Iexec i0) l0 (Iexec i0') /\
                    @SeqBB.step A B ge sp (Iexec i0') l1 (Iterm i1 cf)) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof. intros. simplify. eapply append'; eauto. Qed.

Lemma append2 :
  forall A B l0 cf i0 i1 l1 sp ge,
    @SeqBB.step A B ge sp (Iexec i0) l0 (Iterm i1 cf) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof.
  induction l0; crush.
  inv H.
  inv H. econstructor; eauto. eapply IHl0; eauto.
  constructor; auto.
Qed.

Definition to_cf c :=
  match c with | Iterm _ cf => Some cf | _ => None end.

#[local] Notation "'mki'" := (mk_instr_state) (at level 1).

Variant match_ps : positive -> predset -> predset -> Prop :=
| match_ps_intro :
  forall ps ps' m,
    (forall x, x <= m -> ps !! x = ps' !! x) ->
    match_ps m ps ps'.

Lemma match_ps_eval_pred :
  forall p v ps tps b,
    eval_predf ps p = b ->
    match_ps v ps tps ->
    Forall (fun p => p <= v) (predicate_use p) ->
    eval_predf tps p = b.
Proof.
  induction p; crush.
  - repeat destruct_match. inv H1.
    unfold eval_predf; simpl.
    inv H0. rewrite H. eauto. rewrite Pos2Nat.id; auto.
  - apply Forall_app in H1; inv H1.
    rewrite ! eval_predf_Pand.
    erewrite IHp1; eauto.
    erewrite IHp2; eauto.
  - apply Forall_app in H1; inv H1.
    rewrite ! eval_predf_Por.
    erewrite IHp1; eauto.
    erewrite IHp2; eauto.
Qed.

Lemma eval_pred_under_match:
  forall rs m rs' m' ps tps tps' ps' v p1 rs'' ps'' m'',
    eval_pred (Some p1) (mki rs ps m) (mki rs' ps' m') (mki rs'' ps'' m'') ->
    Forall (fun p => p <= v) (predicate_use p1) ->
    match_ps v ps tps ->
    match_ps v ps' tps' ->
    exists tps'',
      eval_pred (Some p1) (mki rs tps m) (mki rs' tps' m') (mki rs'' tps'' m'')
      /\ match_ps v ps'' tps''.
Proof.
  inversion 1; subst; simplify.
  econstructor. econstructor. econstructor. simpl.
  eapply match_ps_eval_pred; eauto. eauto.
  econstructor. econstructor. econstructor. simpl.
  eapply match_ps_eval_pred; eauto. eauto.
Qed.

Lemma eval_pred_eq_predset :
  forall p rs ps m rs' m' ps' rs'' m'',
    eval_pred p (mki rs ps m) (mki rs' ps m') (mki rs'' ps' m'') ->
    ps' = ps.
Proof. inversion 1; subst; crush. Qed.

Lemma predicate_lt :
  forall p p0,
    In p0 (predicate_use p) -> p0 <= max_predicate p.
Proof.
  induction p; crush.
  - destruct_match. inv H; try lia; contradiction.
  - eapply Pos.max_le_iff.
    eapply in_app_or in H. inv H; eauto.
  - eapply Pos.max_le_iff.
    eapply in_app_or in H. inv H; eauto.
Qed.

Lemma truthy_match_ps :
  forall v ps tps p,
    truthy ps p ->
    (forall p', p = Some p' -> Forall (fun x => x <= v) (predicate_use p')) ->
    match_ps v ps tps ->
    truthy tps p.
Proof.
  inversion 1; crush.
  constructor.
  constructor. symmetry in H1. eapply match_ps_eval_pred; eauto.
Qed.

Lemma instr_falsy_match_ps :
  forall v ps tps i,
    instr_falsy ps i ->
    Forall (fun x => x <= v) (pred_uses i) ->
    match_ps v ps tps ->
    instr_falsy tps i.
Proof.
  inversion 1; crush; constructor; eapply match_ps_eval_pred; eauto.
  inv H2; auto.
Qed.

Ltac truthy_falsy :=
  match goal with
  | H1: truthy _ _, H2: instr_falsy _ _ |- _ => inv H1; inv H2; solve [crush]
  end.

Lemma elim_cond_s_spec :
  forall A B ge sp rs m rs' m' ps tps ps' p a p0 l v,
    step_instr ge sp (Iexec (mki rs ps m)) a (Iexec (mki rs' ps' m')) ->
    Forall (fun p => p <= v) (pred_uses a) ->
    match_ps v ps tps ->
    elim_cond_s p a = (p0, l) ->
    exists tps',
      step_list2 (@step_instr A B ge) sp (Iexec (mki rs tps m)) l (Iexec (mki rs' tps' m'))
      /\ match_ps v ps' tps'.
Proof.
  inversion 1; subst; simplify.
  - inv H2. econstructor. split; eauto; econstructor; econstructor.
  - inv H2. do 2 econstructor; eauto. econstructor; eauto.
    econstructor; eauto. eapply truthy_match_ps; eauto.
    intros. destruct p1; try discriminate; crush.
    constructor.
  - inv H2. do 2 econstructor; eauto. econstructor; eauto.
    econstructor; eauto. eapply truthy_match_ps; eauto.
    intros. destruct p1; try discriminate; crush.
    constructor.
  - inv H2. do 2 econstructor; eauto. econstructor; eauto.
    econstructor; eauto. eapply truthy_match_ps; eauto.
    intros. destruct p1; try discriminate; crush.
    constructor.
  - inv H2. do 2 econstructor; eauto. econstructor; eauto.
    econstructor; eauto. eapply truthy_match_ps; eauto.
    intros. destruct p'; try discriminate; crush. inv H0; auto.
    constructor.
    constructor; intros.
    destruct (peq x p1); subst.
    { rewrite ! PMap.gss; auto. }
    { inv H1. rewrite ! PMap.gso; auto. }
  - do 2 econstructor; eauto.
    unfold elim_cond_s in H2.
    destruct a; inv H2;
      try (econstructor;
           [eapply exec_RB_falsy; simplify; eapply instr_falsy_match_ps; eauto|constructor]).
    destruct c; inv H5;
      try (econstructor;
           [eapply exec_RB_falsy; simplify; eapply instr_falsy_match_ps; eauto|constructor]).
    inv H4.
    econstructor. eapply exec_RB_falsy. econstructor. eapply match_ps_eval_pred; eauto.
    econstructor. eapply exec_RB_falsy. econstructor. simplify.
    rewrite eval_predf_Pand. apply andb_false_intro2. eapply match_ps_eval_pred; eauto.
    econstructor. eapply exec_RB_falsy. econstructor. simplify.
    rewrite eval_predf_Pand. apply andb_false_intro2. eapply match_ps_eval_pred; eauto.
    constructor.
Qed.

Definition wf_predicate (v: predicate) (p: predicate) := v < p.

Lemma eval_predf_match_ps :
  forall p p' p0 v,
    match_ps v p p' ->
    Forall (fun x => x <= v) (predicate_use p0) ->
    eval_predf p p0 = eval_predf p' p0.
Proof.
  induction p0; crush.
  - unfold eval_predf. simplify. destruct p0.
    rewrite Pos2Nat.id. inv H. inv H0. rewrite H1; auto.
  - eapply Forall_app in H0. inv H0.
    rewrite ! eval_predf_Pand.
    erewrite IHp0_1; eauto.
    erewrite IHp0_2; eauto.
  - eapply Forall_app in H0. inv H0.
    rewrite ! eval_predf_Por.
    erewrite IHp0_1; eauto.
    erewrite IHp0_2; eauto.
Qed.

Lemma step_cf_instr_ps_const :
  forall ge stk f sp pc rs' ps' m' cf t pc' rs'' ps'' m'',
    step_cf_instr ge (State stk f sp pc rs' ps' m') cf t (State stk f sp pc' rs'' ps'' m'') ->
    ps' = ps''.
Proof. inversion 1; subst; auto. Qed.

Lemma step_cf_instr_ps_idem :
  forall ge stk f sp pc rs' ps' m' cf t pc' rs'' ps'' m'' tps',
    step_cf_instr ge (State stk f sp pc rs' ps' m') cf t (State stk f sp pc' rs'' ps'' m'') ->
    step_cf_instr ge (State stk f sp pc rs' tps' m') cf t (State stk f sp pc' rs'' tps' m'').
Proof. inversion 1; subst; simplify; econstructor; eauto. Qed.

Variant match_stackframe : stackframe -> stackframe -> Prop :=
  | match_stackframe_init :
    forall res f tf sp pc rs p p'
           (TF: transf_function f = tf)
           (PS: match_ps (max_pred_function f) p p'),
      match_stackframe (Stackframe res f sp pc rs p) (Stackframe res tf sp pc rs p').

Variant match_states : state -> state -> Prop :=
  | match_state :
    forall stk stk' f tf sp pc rs p p0 m
           (TF: transf_function f = tf)
           (STK: Forall2 match_stackframe stk stk')
           (PS: match_ps (max_pred_function f) p p0),
      match_states (State stk f sp pc rs p m) (State stk' tf sp pc rs p0 m)
  | match_callstate :
    forall cs cs' f tf args m
           (TF: transf_fundef f = tf)
           (STK: Forall2 match_stackframe cs cs'),
      match_states (Callstate cs f args m) (Callstate cs' tf args m)
  | match_returnstate :
    forall cs cs' v m
           (STK: Forall2 match_stackframe cs cs'),
      match_states (Returnstate cs v m) (Returnstate cs' v m)
.

Lemma step_instr_inv_exit :
  forall A B ge sp i p cf,
    eval_predf (is_ps i) p = true ->
    @step_instr A B ge sp (Iexec i) (RBexit (Some p) cf) (Iterm i cf).
Proof.
  intros.
  econstructor. constructor; eauto.
Qed.

Lemma step_instr_inv_exit2 :
  forall A B ge sp i p cf,
    eval_predf (is_ps i) p = false ->
    @step_instr A B ge sp (Iexec i) (RBexit (Some p) cf) (Iexec i).
Proof.
  intros.
  eapply exec_RB_falsy; constructor; auto.
Qed.

Lemma eval_predf_set_gt:
  forall p1 v ps b p tps,
    eval_predf ps p1 = true ->
    Forall (fun x : positive => x <= v) (predicate_use p1) ->
    wf_predicate v p -> match_ps v ps tps -> eval_predf tps # p <- b p1 = true.
Proof.
  induction p1; crush.
  - unfold eval_predf. simplify. destruct p. rewrite Pos2Nat.id.
    assert (p <> p0).
    { inv H0. unfold wf_predicate in H1. lia. }
    rewrite ! PMap.gso by auto. inv H2.
    inv H0. rewrite <- H4 by auto. unfold eval_predf in H.
    simplify. rewrite Pos2Nat.id in H. auto.
  - rewrite eval_predf_Pand. apply Forall_app in H0.
    rewrite eval_predf_Pand in H. apply andb_true_iff in H.
    apply andb_true_iff; simplify.
    eauto.
    eauto.
  - rewrite eval_predf_Por. apply Forall_app in H0.
    rewrite eval_predf_Por in H. apply orb_true_iff in H.
    apply orb_true_iff; simplify. inv H; eauto.
Qed.

Lemma eval_predf_in_ps :
  forall v ps p1 b p tps,
    eval_predf ps p1 = true ->
    Forall (fun x => x <= v) (predicate_use p1) ->
    wf_predicate v p ->
    match_ps v ps tps ->
    eval_predf tps # p <- b (Pand (Plit (b, p)) p1) = true.
Proof.
  intros.
  rewrite eval_predf_Pand. apply andb_true_iff. split.
  unfold eval_predf. simplify. rewrite Pos2Nat.id.
  rewrite PMap.gss. destruct b; auto.
  eapply eval_predf_set_gt; eauto.
Qed.

Lemma eval_predf_in_ps2 :
  forall v ps p1 b b' p tps,
    eval_predf ps p1 = true ->
    Forall (fun x => x <= v) (predicate_use p1) ->
    wf_predicate v p ->
    match_ps v ps tps ->
    b <> b' ->
    eval_predf tps # p <- b (Pand (Plit (b', p)) p1) = false.
Proof.
  intros.
  rewrite eval_predf_Pand. apply andb_false_iff.
  unfold eval_predf. simplify. left.
  rewrite Pos2Nat.id. rewrite PMap.gss.
  now destruct b, b'.
Qed.

Lemma match_ps_set_gt :
  forall v ps tps p b,
    wf_predicate v p ->
    match_ps v ps tps ->
    match_ps v ps tps # p <- b.
Proof.
  intros. constructor. intros.
  unfold wf_predicate in *. inv H0.
  rewrite PMap.gso; auto; lia.
Qed.

Definition match_prog (p: program) (tp: program) :=
  Linking.match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Section CORRECTNESS.

  Context (prog tprog : program).

  Let ge : genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

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
    unfold transf_function. auto. auto.
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

  Lemma step_instr_ge :
    forall sp i a i',
      step_instr ge sp i a i' ->
      step_instr tge sp i a i'.
  Proof using TRANSL.
    inversion 1; subst; simplify; clear H; econstructor; eauto;
      try (rewrite <- eval_op_eq; auto); rewrite <- eval_addressing_eq; auto.
  Qed.

  #[local] Hint Resolve eval_builtin_args_preserved : core.
  #[local] Hint Resolve symbols_preserved : core.
  #[local] Hint Resolve external_call_symbols_preserved : core.
  #[local] Hint Resolve senv_preserved : core.
  #[local] Hint Resolve find_function_translated : core.
  #[local] Hint Resolve sig_transf_function : core.

  Lemma step_cf_instr_ge :
    forall st cf t st' tst,
      step_cf_instr ge st cf t st' ->
      match_states st tst ->
      exists tst', step_cf_instr tge tst cf t tst' /\ match_states st' tst'.
  Proof using TRANSL.
    inversion 1; subst; simplify; clear H;
      match goal with H: context[match_states] |- _ => inv H end;
      repeat (econstructor; eauto).
  Qed.

  Lemma step_cf_instr_det :
    forall ge st cf t st1 st2,
      step_cf_instr ge st cf t st1 ->
      step_cf_instr ge st cf t st2 ->
      st1 = st2.
  Proof using TRANSL.
    inversion 1; subst; simplify; clear H;
      match goal with H: context[step_cf_instr] |- _ => inv H end; crush;
    assert (vargs0 = vargs) by eauto using eval_builtin_args_determ; subst;
    assert (vres = vres0 /\ m' = m'0) by eauto using external_call_deterministic; crush.
  Qed.

  Lemma step_list2_ge :
    forall sp l i i',
      step_list2 (step_instr ge) sp i l i' ->
      step_list2 (step_instr tge) sp i l i'.
  Proof using TRANSL.
    induction l; simplify; inv H.
    - constructor.
    - econstructor. apply step_instr_ge; eauto.
      eauto.
  Qed.

  Lemma step_list_ge :
    forall sp l i i',
      step_list (step_instr ge) sp i l i' ->
      step_list (step_instr tge) sp i l i'.
  Proof using TRANSL.
    induction l; simplify; inv H.
    - eauto using exec_RBcons, step_instr_ge.
    - eauto using exec_RBterm, step_instr_ge.
  Qed.

  Lemma max_pred_function_use :
    forall f pc bb i p,
      f.(fn_code) ! pc = Some bb ->
      In i bb ->
      In p (pred_uses i) ->
      p <= max_pred_function f.
  Proof. Admitted.

  Lemma elim_cond_s_wf_predicate :
    forall a p p0 l v,
      elim_cond_s p a = (p0, l) ->
      wf_predicate v p ->
      wf_predicate v p0.
  Proof using.
    destruct a; simplify; try match goal with H: (_, _) = (_, _) |- _ => inv H end; auto.
    destruct c; simplify; try match goal with H: (_, _) = (_, _) |- _ => inv H end; auto.
    unfold wf_predicate in *; lia.
  Qed.

  Lemma replace_section_wf_predicate :
    forall bb v p t0 p0,
      replace_section elim_cond_s p bb = (p0, t0) ->
      wf_predicate v p ->
      wf_predicate v p0.
  Proof using.
    induction bb; crush; repeat (destruct_match; crush).
    inv H.
    exploit IHbb; eauto; simplify.
    eapply elim_cond_s_wf_predicate in Heqp2; eauto.
  Qed.

  Lemma elim_cond_s_spec2 :
    forall rs m rs' m' ps tps ps' p a p0 l cf stk f sp pc t st tstk,
      step_instr ge sp (Iexec (mki rs ps m)) a (Iterm (mki rs' ps' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' ps' m') cf t st ->
      Forall (fun p => p <= (max_pred_function f)) (pred_uses a) ->
      match_ps (max_pred_function f) ps tps ->
      wf_predicate (max_pred_function f) p ->
      elim_cond_s p a = (p0, l) ->
      Forall2 match_stackframe stk tstk ->
      exists tps' cf' st',
        SeqBB.step tge sp (Iexec (mki rs tps m)) l (Iterm (mki rs' tps' m') cf')
        /\ match_ps (max_pred_function f) ps' tps'
        /\ step_cf_instr tge (State tstk (transf_function f) sp pc rs' tps' m') cf' t st'
        /\ match_states st st'.
  Proof using TRANSL.
    inversion 1; subst; simplify.
    destruct cf;
      try (inv H5; exploit step_cf_instr_ge; eauto; [econstructor|]; eauto; simplify;
           do 3 econstructor; simplify; eauto;
           constructor; constructor; eapply truthy_match_ps; eauto;
           intros; match goal with H: _ = Some _ |- _ => inv H end; auto).
    inv H0; destruct b.
    + inv H5; do 3 econstructor; simplify.
      econstructor. econstructor; eauto.
      eapply truthy_match_ps; eauto; intros; match goal with H: _ = Some _ |- _ => inv H end; auto.
      constructor.
      econstructor. simplify. destruct p1.
      constructor. inv H4. eapply eval_predf_in_ps; eauto.
      constructor. unfold eval_predf; simplify. rewrite Pos2Nat.id.
      apply PMap.gss.
      apply match_ps_set_gt; auto.
      constructor; auto.
      constructor; auto.
      apply match_ps_set_gt; auto.
    + inv H5; do 3 econstructor; simplify.
      econstructor. econstructor; eauto.
      eapply truthy_match_ps; eauto; intros; match goal with H: _ = Some _ |- _ => inv H end; auto.
      econstructor. eapply exec_RB_falsy. simplify. destruct p1.
      constructor. inv H4. eapply eval_predf_in_ps2; eauto.
      constructor. unfold eval_predf; simplify. rewrite Pos2Nat.id. apply PMap.gss.
      constructor. econstructor. inv H4. constructor. unfold eval_predf; simplify.
      rewrite Pos2Nat.id. rewrite PMap.gss. auto.
      constructor. eapply eval_predf_in_ps; eauto.
      apply match_ps_set_gt; auto.
      constructor; auto.
      constructor; auto.
      apply match_ps_set_gt; auto.
  Qed.

  Lemma replace_section_spec :
    forall sp bb rs ps m rs' ps' m' stk f t cf pc tps p p' bb' st tstk,
      SeqBB.step ge sp (Iexec (mki rs ps m)) bb (Iterm (mki rs' ps' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' ps' m') cf t st ->
      match_ps (max_pred_function f) ps tps ->
      (forall p i, In i bb -> In p (pred_uses i) -> p <= max_pred_function f) ->
      wf_predicate (max_pred_function f) p ->
      replace_section elim_cond_s p bb = (p', bb') ->
      Forall2 match_stackframe stk tstk ->
      exists st' tps' cf',
        SeqBB.step tge sp (Iexec (mki rs tps m)) bb' (Iterm (mki rs' tps' m') cf')
        /\ match_ps (max_pred_function f) ps' tps'
        /\ step_cf_instr tge (State tstk (transf_function f) sp pc rs' tps' m') cf' t st'
        /\ match_states st st'.
  Proof using TRANSL.
    induction bb; simplify; inv H.
    - destruct state'. repeat destruct_match. inv H4.
      exploit elim_cond_s_spec; eauto. apply Forall_forall. intros; eauto. simplify.
      exploit IHbb; eauto; simplify.
      do 3 econstructor. simplify.
      eapply append. econstructor; simplify.
      eapply step_list2_ge; eauto. eauto.
      eauto. eauto. eauto.
    - repeat destruct_match; simplify. inv H4.
      exploit elim_cond_s_spec2. 6: { eauto. } eauto. eauto.
      apply Forall_forall. eauto. eauto.
      eapply replace_section_wf_predicate; eauto. eauto.
      simplify.
      exploit step_cf_instr_ge; eauto. constructor; eauto. simplify.
      exists x1. eexists. exists x0. simplify.
      eapply append2. eauto using step_list_ge. auto. auto. auto.
  Qed.

  Definition lt_pred (c: code) (m: positive) :=
    forall pc bb n,
      c ! pc = Some bb ->
      m = max_pred_block m n bb \/ m < max_pred_block 1 n bb.

  Definition lt_pred2 (c: code) (m: positive) :=
    forall pc bb n,
      c ! pc = Some bb ->
      max_pred_block 1 n bb <= m.

  Lemma elim_cond_s_lt :
    forall p a p0 l x,
      elim_cond_s p a = (p0, l) ->
      p0 <= x ->
      p <= x.
  Proof using.
    destruct a; crush; destruct c; crush.
    inv H. lia.
  Qed.

  Lemma replace_section_lt :
    forall t p1 p0 t2 x,
      replace_section elim_cond_s p1 t = (p0, t2) ->
      p0 <= x ->
      p1 <= x.
  Proof using.
    induction t; crush; repeat destruct_match. inv H.
    eapply IHt; eauto.
    eapply elim_cond_s_lt; eauto.
  Qed.

  Lemma pred_not_in :
    forall l pc p t p' t' x,
      ~ In pc (map fst l) ->
      fold_left (fun a p => elim_cond_fold a (fst p) (snd p)) l (p, t) = (p', t') ->
      t ! pc = x -> t' ! pc = x.
  Proof using.
    induction l; crush.
    repeat destruct_match.
    eapply IHl; eauto. rewrite PTree.gso; auto.
  Qed.

  Lemma pred_greater :
    forall l pc x v p' t',
      In (pc, x) l ->
      list_norepet (map fst l) ->
      fold_left (fun a p => elim_cond_fold a (fst p) (snd p)) l v = (p', t') ->
      exists p, t' ! pc = Some (snd (replace_section elim_cond_s p x))
                /\ (fst v) <= p.
  Proof.
    induction l; crush.
    inv H0. destruct a; simplify. inv H. inv H0.
    remember (elim_cond_fold v pc x). destruct p.
    eapply pred_not_in in H1; eauto. symmetry in Heqp.
    unfold elim_cond_fold in Heqp. repeat destruct_match. inv Heqp0. inv Heqp.
    simplify. econstructor. split. rewrite PTree.gss in H1.
    rewrite Heqp1. eauto. lia.
    remember (elim_cond_fold v p t). destruct p0. symmetry in Heqp0.
    unfold elim_cond_fold in Heqp0. repeat destruct_match. inv Heqp0.
    exploit IHl; eauto; simplify.
    econstructor; simplify. eauto.
    eapply replace_section_lt; eauto.
  Qed.

  Lemma transf_block_spec :
    forall f pc x,
      f.(fn_code) ! pc = Some x ->
      forall p' t',
        PTree.fold elim_cond_fold f.(fn_code) (max_pred_function f + 1, PTree.empty _) = (p', t') ->
        exists p,
          t' ! pc = Some (snd (replace_section elim_cond_s p x)) /\ max_pred_function f + 1 <= p.
  Proof using.
    intros.
    replace (max_pred_function f + 1) with (fst (max_pred_function f + 1, PTree.empty SeqBB.t)); auto.
    eapply pred_greater.
    eapply PTree.elements_correct; eauto.
    apply PTree.elements_keys_norepet.
    rewrite <- PTree.fold_spec. eauto.
  Qed.

  Lemma transf_step_correct:
    forall (s1 : state) (t : trace) (s1' : state),
      step ge s1 t s1' ->
      forall s2 : state,
        match_states s1 s2 ->
        exists s2' : state, step tge s2 t s2' /\ match_states s1' s2'.
  Proof using TRANSL.
    induction 1; intros.
    + inv H2.
      exploit transf_block_spec; eauto.
      assert (X: forall A B (a: A * B), a = (fst a, snd a)).
      { destruct a; auto. } eapply X. simplify.
      remember (replace_section elim_cond_s x bb). destruct p. symmetry in Heqp.
      exploit replace_section_spec; eauto.
      solve [eauto using max_pred_function_use].
      unfold wf_predicate. lia.
      simplify. econstructor.
      simplify. econstructor; eauto. auto.
    + inv H0. econstructor.
      simplify. econstructor; eauto. constructor; eauto. constructor. auto.
    + inv H0. do 3 econstructor; eauto.
    + inv H. inv STK. inv H1. do 3 econstructor; eauto.
  Qed.

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
