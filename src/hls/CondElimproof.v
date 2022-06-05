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

Lemma cf_in_step :
  forall A B ge sp is_ is_' bb cf,
    @SeqBB.step A B ge sp (Iexec is_) bb (Iterm is_' cf) ->
    exists p, In (RBexit p cf) bb
              /\ Option.default true (Option.map (eval_predf (is_ps is_')) p) = true.
  Proof. Admitted.

Lemma forbidden_term_trans :
  forall A B ge sp i c b i' c',
    ~ @SeqBB.step A B ge sp (Iterm i c) b (Iterm i' c').
Proof. induction b; unfold not; intros; inv H. Qed.

Lemma random1 :
  forall A B ge sp is_ b is_' cf,
    @SeqBB.step A B ge sp (Iexec is_) b (Iterm is_' cf) ->
    exists p b', SeqBB.step ge sp (Iexec is_) (b' ++ (RBexit p cf) :: nil) (Iterm is_' cf)
                 /\ Forall2 eq (b' ++ (RBexit p cf) :: nil) b.
Proof.
Admitted.

Lemma append :
  forall A B cf i0 i1 l0 l1 sp ge,
      (exists i0', step_list2 (@step_instr A B ge) sp (Iexec i0) l0 (Iexec i0') /\
                    @SeqBB.step A B ge sp (Iexec i0') l1 (Iterm i1 cf)) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof. Admitted.

Lemma append2 :
  forall A B cf i0 i1 l0 l1 sp ge,
    @SeqBB.step A B ge sp (Iexec i0) l0 (Iterm i1 cf) ->
    @SeqBB.step A B ge sp (Iexec i0) (l0 ++ l1) (Iterm i1 cf).
Proof. Admitted.

Definition to_cf c :=
  match c with | Iterm _ cf => Some cf | _ => None end.

#[local] Notation "'mki'" := (mk_instr_state) (at level 1).

Variant match_ps : positive -> predset -> predset -> Prop :=
| match_ps_intro :
  forall ps ps' m,
    (forall x, x <= m -> ps !! x = ps' !! x) ->
    match_ps m ps ps'.

Lemma eval_pred_under_match:
  forall rs m rs' m' ps tps tps' ps' v p1 rs'' ps'' m'',
    eval_pred (Some p1) (mki rs ps m) (mki rs' ps' m') (mki rs'' ps'' m'') ->
    max_predicate p1 <= v ->
    match_ps v ps tps ->
    match_ps v ps' tps' ->
    exists tps'',
      eval_pred (Some p1) (mki rs tps m) (mki rs' tps' m') (mki rs'' tps'' m'')
      /\ match_ps v ps'' tps''.
Proof.
  inversion 1; subst; simplify.
    Admitted.

Lemma eval_pred_eq_predset :
  forall p rs ps m rs' m' ps' rs'' m'',
    eval_pred p (mki rs ps m) (mki rs' ps m') (mki rs'' ps' m'') ->
    ps' = ps.
Proof. inversion 1; subst; crush. Qed.

Lemma elim_cond_s_spec :
  forall A B ge sp rs m rs' m' ps tps ps' p a p0 l v,
    step_instr ge sp (Iexec (mki rs ps m)) a (Iexec (mki rs' ps' m')) ->
    max_pred_instr v a <= v ->
    match_ps v ps tps ->
    elim_cond_s p a = (p0, l) ->
    exists tps',
      step_list2 (@step_instr A B ge) sp (Iexec (mki rs tps m)) l (Iexec (mki rs' tps' m'))
      /\ match_ps v ps' tps'.
Proof.
  inversion 1; subst; simplify; inv H.
  - inv H2. econstructor. split; eauto; econstructor; econstructor.
  - inv H2. destruct p1.
    + exploit eval_pred_under_match; eauto; try lia; simplify.
      econstructor. split. econstructor. econstructor; eauto. eauto. econstructor.
      eauto.
    + inv H15. econstructor. split. econstructor. econstructor. eauto. constructor; eauto.
      constructor. auto.
  - inv H2. destruct p1.
    + exploit eval_pred_under_match; eauto; try lia; simplify.
      econstructor. split. econstructor. econstructor; eauto.
      constructor. eauto.
    + inv H18. econstructor. split. econstructor. econstructor; eauto. constructor; eauto.
      constructor. auto.
  - inv H2. destruct p1.
    + exploit eval_pred_under_match; eauto; try lia; simplify.
      econstructor. split. econstructor. econstructor; eauto.
      constructor. auto.
    + inv H18. econstructor. split. econstructor. econstructor; eauto. constructor; eauto.
      constructor. auto.
  - inv H2. destruct p'.
    exploit eval_pred_under_match; eauto. lia. Admitted.

Definition wf_predicate (v: predicate) (p: predicate) := v < p.

Lemma eval_predf_match_ps :
  forall p p' p0 v,
    match_ps v p p' ->
    max_predicate p0 <= v ->
    eval_predf p p0 = eval_predf p' p0.
  Admitted.

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
           (TF: transf_function f = tf),
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
  replace (Iterm i cf) with (if (eval_predf (is_ps i) p) then Iterm i cf else Iexec i).
  constructor; auto.
  rewrite H; auto.
Qed.

Lemma step_instr_inv_exit2 :
  forall A B ge sp i p cf,
    eval_predf (is_ps i) p = false ->
    @step_instr A B ge sp (Iexec i) (RBexit (Some p) cf) (Iexec i).
Proof.
  intros.
  replace (Iexec i) with (if (eval_predf (is_ps i) p) then Iterm i cf else Iexec i) at 2.
  constructor; auto.
  rewrite H; auto.
Qed.

Lemma eval_predf_in_ps :
  forall v ps ps' p1 b p tps,
    eval_predf ps p1 = true ->
    max_predicate p1 <= v ->
    wf_predicate v p ->
    match_ps v ps ps' ->
    eval_predf tps # p <- b (Pand (Plit (b, p)) p1) = true.
Admitted.

Lemma eval_predf_in_ps2 :
  forall v ps ps' p1 b b' p tps,
    eval_predf ps p1 = true ->
    max_predicate p1 <= v ->
    wf_predicate v p ->
    match_ps v ps ps' ->
    b <> b' ->
    eval_predf tps # p <- b (Pand (Plit (b', p)) p1) = false.
Admitted.

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

Lemma transf_block_spec :
  forall f pc b,
    f.(fn_code) ! pc = Some b ->
    exists p,
      (transf_function f).(fn_code) ! pc
      = Some (snd (replace_section elim_cond_s p b)). Admitted.

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

  Lemma elim_cond_s_spec2 :
    forall rs m rs' m' ps tps ps' p a p0 l v cf stk f sp pc t st,
      step_instr ge sp (Iexec (mki rs ps m)) a (Iterm (mki rs' ps' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' ps' m') cf t st ->
      max_pred_instr v a <= v ->
      match_ps v ps tps ->
      wf_predicate v p ->
      elim_cond_s p a = (p0, l) ->
      exists tps' cf' st',
        SeqBB.step tge sp (Iexec (mki rs tps m)) l (Iterm (mki rs' tps' m') cf')
        /\ match_ps v ps' tps'
        /\ step_cf_instr tge (State stk f sp pc rs' tps' m') cf' t st'
        /\ match_states st st'.
  Proof.
    inversion 1; subst; simplify.
    - destruct (eval_predf ps p1) eqn:?; [|discriminate]. inv H2.
      destruct cf; inv H5;
        try (do 3 econstructor; simplify;
             [ constructor; apply step_instr_inv_exit; erewrite <- eval_predf_match_ps; eauto; lia
             | auto
             | eauto using step_cf_instr_ps_idem
             | assert (ps' = ps'') by (eauto using step_cf_instr_ps_const); subst; auto ]).
      do 3 econstructor; simplify.
      constructor; apply step_instr_inv_exit; erewrite <- eval_predf_match_ps; eauto; lia.
      auto.
      (*inv H0; destruct b.
      + do 3 econstructor; simplify.
        econstructor. econstructor; eauto. eapply eval_pred_true.
        erewrite <- eval_predf_match_ps; eauto. simpl. lia.
        constructor. apply step_instr_inv_exit. simpl.
        eapply eval_predf_in_ps; eauto. lia.
        apply match_ps_set_gt; auto.
        constructor; auto.
        apply match_ps_set_gt; auto.
      + do 3 econstructor; simplify.
        econstructor. econstructor; eauto. eapply eval_pred_true.
        erewrite <- eval_predf_match_ps; eauto. simpl. lia.
        econstructor. apply step_instr_inv_exit2. simpl.
        eapply eval_predf_in_ps2; eauto. lia.
        constructor. apply step_instr_inv_exit. simpl.
        eapply eval_predf_in_ps; eauto; lia.
        apply match_ps_set_gt; auto.
        constructor; auto.
        apply match_ps_set_gt; auto.
    -*) Admitted.

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

  Lemma step_cf_instr_ge :
    forall st cf t st' tst,
      step_cf_instr ge st cf t st' ->
      match_states st tst ->
      exists tst', step_cf_instr tge tst cf t tst' /\ match_states st' tst'.
  Proof.
    inversion 1; subst; simplify; clear H;
      match goal with H: context[match_states] |- _ => inv H end.
    - do 2 econstructor. rewrite <- sig_transf_function. econstructor; eauto.
      eauto using find_function_translated. auto.
      econstructor; auto. repeat (constructor; auto).
    - do 2 econstructor. econstructor. eauto using find_function_translated.
      eauto using sig_transf_function. eauto.
      econstructor; auto.
    - do 2 econstructor.

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

  Lemma replace_section_spec :
    forall sp bb rs ps m rs' ps' m' stk f t cf pc tps v n p p' bb' st st',
      SeqBB.step ge sp (Iexec (mki rs ps m)) bb (Iterm (mki rs' ps' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' ps' m') cf t st ->
      match_ps v ps tps ->
      max_pred_block v n bb <= v ->
      replace_section elim_cond_s p bb = (p', bb') ->
      exists tps' cf',
        SeqBB.step tge sp (Iexec (mki rs tps m)) bb' (Iterm (mki rs' tps' m') cf')
        /\ match_ps v ps' tps'
        /\ step_cf_instr tge (State stk f sp pc rs' tps' m') cf' t st'
        /\ match_states st st'.
  Proof.
    induction bb; simplify; inv H.
    - destruct state'. repeat destruct_match. inv H3.
      exploit elim_cond_s_spec; eauto. admit. simplify.
      exploit IHbb; eauto; simplify. admit.
      do 2 econstructor. simplify.
      eapply append. econstructor; simplify.
      eapply step_list2_ge; eauto. eauto.
      eauto. eauto. eauto.
    - repeat destruct_match; simplify. inv H3.
      exploit elim_cond_s_spec2; eauto. admit. admit. simplify.
      do 3 econstructor; simplify; eauto.
      eapply append2; eauto using step_list2_ge.
      Unshelve. exact 1.
  Admitted.

  Lemma transf_step_correct:
    forall (s1 : state) (t : trace) (s1' : state),
      step ge s1 t s1' ->
      forall s2 : state,
        match_states s1 s2 ->
        exists s2' : state, step tge s2 t s2' /\ match_states s1' s2'.
  Proof.
    induction 1; intros.
    + inv H2. eapply cf_in_step in H0; simplify.
      exploit transf_block_spec; eauto; simplify.
      do 2 econstructor. econstructor; eauto.
      simplify. Admitted.

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
