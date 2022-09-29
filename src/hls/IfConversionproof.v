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
Require Import compcert.common.Linking.

Require Import vericert.common.Vericertlib.
Require Import vericert.common.DecEq.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.IfConversion.
Require Import vericert.hls.Predicate.

#[local] Opaque decide_if_convert.
#[local] Opaque get_loops.
#[local] Opaque ifconv_list.

#[local] Open Scope positive.
#[local] Notation "'mki'" := (mk_instr_state) (at level 1).

Variant match_stackframe : stackframe -> stackframe -> Prop :=
  | match_stackframe_init :
    forall res f tf sp pc rs p l
           (TF: transf_function l f = tf),
      match_stackframe (Stackframe res f sp pc rs p) (Stackframe res tf sp pc rs p).

Definition bool_order (b: bool): nat := if b then 1 else 0.

Inductive if_conv_block_spec (c: code): SeqBB.t -> SeqBB.t -> Prop :=
| if_conv_block_intro :
  if_conv_block_spec c nil nil
| if_conv_block_eq :
  forall a b tb,
    if_conv_block_spec c b tb ->
    if_conv_block_spec c (a::b) (a::tb)
| if_conv_block_conv :
  forall b tb ta p pc' b',
    if_conv_block_spec c b tb ->
    c ! pc' = Some b' ->
    if_conv_block_spec c b' ta ->
    if_conv_block_spec c (RBexit p (RBgoto pc')::b) (map (map_if_convert p) ta++tb).

Inductive replace_spec_unit (f: instr -> SeqBB.t)
  : SeqBB.t -> SeqBB.t -> Prop :=
| replace_spec_cons : forall i b b',
  replace_spec_unit f b b' ->
  replace_spec_unit f (i :: b) (f i ++ b')
| replace_spec_nil :
  replace_spec_unit f nil nil
.

Definition if_conv_replace n nb := replace_spec_unit (if_convert_block n nb).

Inductive if_conv_spec (c c': code) (pc: node): Prop :=
| if_conv_unchanged :
  c ! pc = c' ! pc ->
  if_conv_spec c c' pc
| if_conv_changed : forall b b' pc' tb,
  if_conv_replace pc' b' b tb ->
  c ! pc = Some b ->
  c ! pc' = Some b' ->
  c' ! pc = Some tb ->
  if_conv_spec c c' pc.

Lemma transf_spec_correct_notin :
  forall l pc c b d,
  ~ In pc (map fst l) ->
  b ! pc = d ! pc ->
  (fold_left (fun s n => if_convert c s (fst n) (snd n)) l b) ! pc = d ! pc.
Proof.
  induction l; crush.
  assert (fst a <> pc /\ ~ In pc (map fst l)).
  split. destruct (peq (fst a) pc); auto.
  unfold not; intros. apply H. tauto.
  simplify. eapply IHl; eauto.
  destruct a; simplify. unfold if_convert.
  repeat (destruct_match; auto; []).
  rewrite PTree.gso; auto.
Qed.

Lemma transf_spec_correct_None :
  forall l pc c b,
  c ! pc = None ->
  b ! pc = None ->
  (fold_left (fun s n => if_convert c s (fst n) (snd n)) l b) ! pc = None.
Proof.
  induction l; crush.
  eapply IHl; eauto.
  destruct (peq (fst a) pc); subst.
  unfold if_convert. rewrite H. auto.
  unfold if_convert. repeat (destruct_match; auto; []).
  now rewrite PTree.gso by auto.
Qed.

Lemma if_convert_neq :
  forall pc pc' pc'' c b,
    pc'' <> pc ->
    (if_convert c b pc'' pc') ! pc = b ! pc.
Proof.
  unfold if_convert; intros.
  repeat (destruct_match; auto; []).
  rewrite PTree.gso; auto.
Qed.

Lemma if_convert_ne_pc :
  forall pc pc' c b,
    c ! pc = None ->
    (if_convert c b pc pc') ! pc = b ! pc.
Proof.
  unfold if_convert; intros.
  repeat (destruct_match; auto; []).
  discriminate.
Qed.

Lemma if_convert_ne_pc' :
  forall pc pc' c b,
    c ! pc' = None ->
    (if_convert c b pc pc') ! pc = b ! pc.
Proof.
  unfold if_convert; intros.
  repeat (destruct_match; auto; []).
  discriminate.
Qed.

Lemma if_convert_decide_false :
  forall pc pc' c b y,
    c ! pc' = Some y ->
    decide_if_convert y = false ->
    (if_convert c b pc pc') ! pc = b ! pc.
Proof.
  unfold if_convert; intros.
  repeat (destruct_match; auto; []).
  setoid_rewrite Heqo0 in H; crush.
Qed.

Lemma if_convert_decide_true :
  forall pc pc' c b y z,
    c ! pc = Some z ->
    c ! pc' = Some y ->
    decide_if_convert y = true ->
    (if_convert c b pc pc') ! pc = Some (snd (replace_section (wrap_unit (if_convert_block pc' y)) tt z)).
Proof.
  unfold if_convert; intros.
  setoid_rewrite H.
  setoid_rewrite H0.
  rewrite H1. rewrite PTree.gss. auto.
Qed.

Lemma transf_spec_correct_in :
  forall l pc c b c' z,
    (fold_left (fun s n => if_convert c s (fst n) (snd n)) l b) = c' ->
    b ! pc = Some z \/ (exists pc' y,
                          c ! pc' = Some y
                          /\ decide_if_convert y = true
                          /\ b ! pc = Some (snd (replace_section (wrap_unit (if_convert_block pc' y)) tt z))) ->
    c ! pc = Some z ->
    c' ! pc = Some z \/ exists pc' y,
                          c ! pc' = Some y
                          /\ decide_if_convert y = true
                          /\ c' ! pc = Some (snd (replace_section (wrap_unit (if_convert_block pc' y)) tt z)).
Proof.
  induction l; crush. inv H0. tauto.
  simplify. right. eauto.
  exploit IHl; eauto. inv H0.
  destruct a; simplify.

  destruct (peq p pc); [|left; rewrite <- H2; eapply if_convert_neq; eauto]; subst; [].
  destruct (c ! p0) eqn:?; [|left; rewrite <- H2; eapply if_convert_ne_pc'; eauto]; [].
  destruct (decide_if_convert t) eqn:?; [|left; rewrite <- H2; eapply if_convert_decide_false; eauto]; [].
  right. do 2 econstructor; simplify; eauto.
  apply if_convert_decide_true; auto.

  simplify. right. destruct a; simplify.
  destruct (peq p pc);
    [|do 2 econstructor; simplify; eauto;
      rewrite <- H3; eapply if_convert_neq; auto]; []; subst.
  destruct (c ! p0) eqn:?;
           [|do 2 econstructor; simplify; eauto;
             rewrite <- H3; eapply if_convert_ne_pc'; auto]; [].
  destruct (decide_if_convert t) eqn:?;
           [|do 2 econstructor; simplify; try eapply H; eauto;
             rewrite <- H3; eapply if_convert_decide_false; eauto].
  do 2 econstructor; simplify; eauto.
  apply if_convert_decide_true; auto.
Qed.

Lemma replace_spec_true' :
  forall f x,
    replace_spec_unit f x (snd (replace_section (wrap_unit f) tt x)).
Proof.
  induction x; crush. constructor.
  destruct_match; simplify. constructor. eauto.
Qed.

Lemma replace_spec_true :
  forall x0 x1 x,
    if_conv_replace x0 x1 x (snd (replace_section (wrap_unit (if_convert_block x0 x1)) tt x)).
Proof.
  unfold if_conv_replace; intros.
  apply replace_spec_true'.
Qed.

Lemma transf_spec_correct :
  forall f pc l,
    if_conv_spec f.(fn_code) (transf_function l f).(fn_code) pc.
Proof.
  intros; unfold transf_function; destruct_match; cbn.
  unfold if_convert_code.
  destruct (f.(fn_code) ! pc) eqn:?.
  - simplify.
    match goal with
      |- context [fold_left ?a ?b ?c] =>
        remember (fold_left a b c) as c'
    end. symmetry in Heqc'.
    eapply transf_spec_correct_in in Heqc'; eauto. inv Heqc'. constructor.
    crush.
    simplify. eapply if_conv_changed; eauto.
    apply replace_spec_true.
  - pose proof Heqo as X. eapply transf_spec_correct_None in Heqo; eauto.
    constructor. rewrite Heqo. auto.
Qed.

Inductive wf_trans : option pred_op -> SeqBB.t -> Prop :=
| wf_trans_None: forall b, wf_trans None b
| wf_trans_Some: forall p b,
    (forall op c args p',
        In (RBsetpred op c args p') b ->
        ~ In p' (predicate_use p)) ->
    wf_trans (Some p) b.

Lemma wf_transition_block_opt_prop :
  forall b p,
    wf_transition_block_opt p b = true <-> wf_trans p b.
Proof.
  destruct p.
  2: {
    split. unfold wf_transition_block_opt; intros.
    constructor.
    intros. unfold wf_transition_block_opt. simplify; auto.
  }
  generalize dependent p. induction b; split; crush.
  - constructor; crush.
  - unfold wf_transition_block_opt in H. simplify.
    constructor; auto. intros. unfold wf_transition in H0.
    unfold not; intros. inv H.
    assert (existsb (Pos.eqb p') (predicate_use p) = true).
    { apply existsb_exists; econstructor. split; eauto. apply Pos.eqb_refl. }
    now rewrite H in H0.
    unfold wf_transition_block in *. eapply forallb_forall in H1; eauto.
    unfold wf_transition in *.
    assert (existsb (Pos.eqb p') (predicate_use p) = true).
    { apply existsb_exists; econstructor. split; eauto. apply Pos.eqb_refl. }
    now rewrite H in H1.
  - inv H. unfold wf_transition_block_opt. cbn [Option.default Option.map].
    unfold wf_transition_block. apply forallb_forall. intros.
    unfold wf_transition. destruct x; auto.
    apply H1 in H.
    rewrite <- negb_involutive. f_equal; cbn.
    destruct (existsb (Pos.eqb p0) (predicate_use p)) eqn:?; auto.
    exfalso; apply H. apply existsb_exists in Heqb0; simplify.
    apply Pos.eqb_eq in H3. subst. auto.
Qed.

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
    | match_state_some :
      forall stk stk' f tf sp pc rs p m b pc0 rs0 p0 m0 l
             (TF: transf_function l f = tf)
             (STK: Forall2 match_stackframe stk stk')
             (* This can be improved with a recursive relation for a more general structure of the
                if-conversion proof. *)
             (IS_B: f.(fn_code)!pc = Some b)
             (IS_TB: forall b',
                 f.(fn_code)!pc0 = Some b' ->
                 exists tb, tf.(fn_code)!pc0 = Some tb /\ if_conv_replace pc b b' tb)
             (EXTRAP: sem_extrap tf pc0 sp (Iexec (mki rs p m)) (Iexec (mki rs0 p0 m0)) b)
             (SIM: step ge (State stk f sp pc0 rs0 p0 m0) E0 (State stk f sp pc rs p m)),
        match_states (Some b) (State stk f sp pc rs p m) (State stk' tf sp pc0 rs0 p0 m0)
    | match_state_none :
      forall stk stk' f tf sp pc rs p m l
             (TF: transf_function l f = tf)
             (STK: Forall2 match_stackframe stk stk'),
        match_states None (State stk f sp pc rs p m) (State stk' tf sp pc rs p m)
    | match_callstate :
      forall cs cs' f tf args m l
             (TF: transf_fundef l f = tf)
             (STK: Forall2 match_stackframe cs cs'),
        match_states None (Callstate cs f args m) (Callstate cs' tf args m)
    | match_returnstate :
      forall cs cs' v m
             (STK: Forall2 match_stackframe cs cs'),
        match_states None (Returnstate cs v m) (Returnstate cs' v m).

  Definition match_prog (p: program) (tp: program) :=
    match_program (fun _ f tf => exists l, transf_fundef l f = tf) eq p tp.

  Context (TRANSL : match_prog prog tprog).

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL.
    intros. eapply (Genv.find_symbol_match TRANSL).
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof using TRANSL.
    intros; eapply (Genv.senv_match TRANSL).
  Qed.

  Lemma function_ptr_translated:
    forall b f l,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef l f).
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    crush.
  Qed.

  Lemma sig_transf_function:
    forall (f tf: fundef) l,
      funsig (transf_fundef l f) = funsig f.
  Proof using.
    unfold transf_fundef. unfold AST.transf_fundef; intros. destruct f.
    unfold transf_function. destruct_match. auto. auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: GibleSeq.fundef) l,
      Genv.find_funct ge v = Some f ->
      Genv.find_funct tge v = Some (transf_fundef l f).
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto. simplify. eauto.
  Qed.

  Lemma find_function_translated:
    forall ros rs f l,
      find_function ge ros rs = Some f ->
      find_function tge ros rs = Some (transf_fundef l f).
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
      exists s2, initial_state tprog s2 /\ match_states None s1 s2.
  Proof using TRANSL.
    induction 1.
    exploit function_ptr_translated; eauto; intros.
    do 2 econstructor; simplify. econstructor.
    apply (Genv.init_mem_match TRANSL); eauto.
    replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
    symmetry; eapply Linking.match_program_main; eauto. eauto.
    erewrite sig_transf_function; eauto. econstructor. auto. auto.
    Unshelve. exact None.
  Qed.

  Lemma transf_final_states :
    forall s1 s2 r b,
      match_states b s1 s2 -> final_state s1 r -> final_state s2 r.
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

  Definition measure (b: option SeqBB.t): nat :=
    match b with
    | None => 1
    | Some _ => 0
    end.

  Lemma sim_star :
    forall s1 b t s,
      (exists b' s2,
          star step tge s1 t s2 /\ ltof _ measure b' b
          /\ match_states b' s s2) ->
      exists b' s2,
        (plus step tge s1 t s2 \/
           star step tge s1 t s2 /\ ltof _ measure b' b) /\
          match_states b' s s2.
  Proof using. intros; simplify. do 3 econstructor; eauto. Qed.

  Lemma sim_plus :
    forall s1 b t s,
      (exists b' s2, plus step tge s1 t s2 /\ match_states b' s s2) ->
      exists b' s2,
        (plus step tge s1 t s2 \/
           star step tge s1 t s2 /\ ltof _ measure b' b) /\
          match_states b' s s2.
  Proof using. intros; simplify. do 3 econstructor; eauto. Qed.

  Lemma step_instr :
    forall sp s1 s2 a,
      step_instr ge sp s1 a s2 ->
      step_instr tge sp s1 a s2.
  Proof using TRANSL.
    inversion 1; subst; econstructor; eauto.
    - now rewrite <- eval_op_eq.
    - now rewrite <- eval_addressing_eq.
    - now rewrite <- eval_addressing_eq.
  Qed.

  Lemma seqbb_eq :
    forall bb sp rs pr m rs' pr' m' cf,
      SeqBB.step ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf) ->
      SeqBB.step tge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf).
  Proof using TRANSL.
    induction bb; crush; inv H.
    - econstructor; eauto. apply step_instr; eassumption.
      destruct state'. eapply IHbb; eauto.
    - constructor; apply step_instr; auto.
  Qed.

  Lemma step_list_2_eq :
    forall bb sp a b,
      step_list2 (Gible.step_instr ge) sp a bb b ->
      step_list2 (Gible.step_instr tge) sp a bb b.
  Proof.
    induction bb; crush; inv H.
    - econstructor; eauto.
    - econstructor; eauto. now apply step_instr.
  Qed.

  Lemma fn_all_eq :
    forall f tf l,
      transf_function l f = tf ->
      fn_stacksize f = fn_stacksize tf
      /\ fn_sig f = fn_sig tf
      /\ fn_params f = fn_params tf
      /\ fn_entrypoint f = fn_entrypoint tf
      /\ exists l, if_convert_code (fn_code f) l = fn_code tf.
  Proof.
    intros; simplify; unfold transf_function in *; destruct_match; inv H; auto.
    eexists; simplify; eauto.
  Qed.

  Ltac func_info :=
    match goal with
      H: transf_function _ _ = _ |- _ =>
        let H2 := fresh "ALL_EQ" in
        pose proof (fn_all_eq _ _ _ H) as H2; simplify
    end.

  Lemma step_cf_eq :
    forall stk stk' f tf sp pc rs pr m cf s t pc' l,
      step_cf_instr ge (State stk f sp pc rs pr m) cf t s ->
      Forall2 match_stackframe stk stk' ->
      transf_function l f = tf ->
      exists s', step_cf_instr tge (State stk' tf sp pc' rs pr m) cf t s'
                 /\ match_states None s s'.
  Proof.
    inversion 1; subst; simplify;
      try solve [func_info; do 2 econstructor; econstructor; eauto].
    - do 2 econstructor. constructor; eauto. econstructor; eauto. constructor; auto.
      econstructor. auto.
    - do 2 econstructor. constructor; eauto.
      func_info.
      rewrite H2 in *. rewrite H12. auto. econstructor; auto.
    - func_info. do 2 econstructor. econstructor; eauto. rewrite H2 in *.
      eauto. econstructor; auto.
    Unshelve. all: exact None.
  Qed.

  Definition cf_dec :
    forall a pc, {a = RBgoto pc} + {a <> RBgoto pc}.
  Proof.
    destruct a; try solve [right; crush].
    intros. destruct (peq n pc); subst.
    left; auto.
    right. unfold not in *; intros. inv H. auto.
  Defined.

  Definition wf_trans_dec :
    forall p b, {wf_trans p b} + {~ wf_trans p b}.
  Proof using.
    intros; destruct (wf_transition_block_opt p b) eqn:?.
    left. apply wf_transition_block_opt_prop; auto.
    right. unfold not; intros. apply wf_transition_block_opt_prop in H.
    rewrite H in Heqb0. discriminate.
  Defined.

  Definition cf_wf_dec :
    forall p b a pc, {a = RBgoto pc /\ wf_trans p b} + {a <> RBgoto pc \/ ~ wf_trans p b}.
  Proof using.
    intros; destruct (cf_dec a pc); destruct (wf_trans_dec p b); tauto.
  Qed.

  Lemma wf_trans_comp_false :
    forall n pc' x b',
      RBgoto n <> RBgoto pc' \/ ~ wf_trans x b' ->
      (pc' =? n) && wf_transition_block_opt x b' = false.
  Proof using.
    inversion 1; subst; simplify.
    destruct (peq n pc'); subst; [exfalso; auto|]; [].
    apply Pos.eqb_neq in n0. rewrite Pos.eqb_sym in n0.
    rewrite n0. auto.
    destruct (wf_transition_block_opt x b') eqn:?.
    - exfalso; apply H0. apply wf_transition_block_opt_prop; auto.
    - apply andb_false_r.
  Qed.

  Lemma step_list2_app :
    forall A B (ge: Genv.t A B) sp a b i i' i'',
      step_list2 (Gible.step_instr ge) sp i'' b i' ->
      step_list2 (Gible.step_instr ge) sp i a i'' ->
      step_list2 (Gible.step_instr ge) sp i (a ++ b) i'.
  Proof using.
    induction a; crush.
    - inv H0; auto.
    - inv H0. econstructor.
      eauto. eapply IHa; eauto.
  Qed.

  Lemma map_if_convert_None :
    forall b',
      map (map_if_convert None) b' = b'.
  Proof using.
    induction b'; crush.
    rewrite IHb'; f_equal. destruct a; crush; destruct o; auto.
  Qed.

    Lemma truthy_true :
    forall pr x p,
      truthy pr x ->
      truthy pr p ->
      truthy pr (combine_pred x p).
  Proof using.
    intros.
    inv H; inv H0; cbn [combine_pred] in *; constructor; auto;
    rewrite eval_predf_Pand; apply andb_true_intro; auto.
  Qed.
  #[local] Hint Resolve truthy_true : core.

  Lemma falsy_false :
    forall i' a x,
      instr_falsy (is_ps i') a ->
      instr_falsy (is_ps i') (map_if_convert x a).
  Proof using.
    inversion 1; subst; destruct x; crush; constructor; rewrite eval_predf_Pand;
      auto using andb_false_intro2.
  Qed.
  #[local] Hint Resolve falsy_false : core.

  Lemma map_truthy_instr :
    forall A B (ge: Genv.t A B) sp i a x i',
      truthy (is_ps i) x ->
      Gible.step_instr ge sp (Iexec i) a i' ->
      Gible.step_instr ge sp (Iexec i) (map_if_convert x a) i'.
  Proof using.
    inversion 2; subst; crush;
      try (solve [econstructor; eauto]).
  Qed.

  Lemma map_falsy_instr :
    forall A B (ge: Genv.t A B) sp i a x,
      eval_predf (is_ps i) x = false ->
      Gible.step_instr ge sp (Iexec i) (map_if_convert (Some x) a) (Iexec i).
  Proof using.
    intros; destruct a; constructor; cbn; destruct o; constructor; auto;
      rewrite eval_predf_Pand; rewrite H; auto.
  Qed.

  Lemma map_falsy_list :
    forall A B (ge: Genv.t A B) sp b' p i0,
      eval_predf (is_ps i0) p = false ->
      step_list2 (Gible.step_instr ge) sp (Iexec i0) (map (map_if_convert (Some p)) b') (Iexec i0).
  Proof using.
    induction b'; crush; try constructor.
    econstructor; eauto.
    apply map_falsy_instr; auto.
  Qed.

  Lemma exec_if_conv3 :
    forall A B (ge: Genv.t A B) sp a pc' b' i i0,
      Gible.step_instr ge sp (Iexec i) a (Iexec i0) ->
      step_list2 (Gible.step_instr ge) sp (Iexec i) (if_convert_block pc' b' a) (Iexec i0).
  Proof with (simplify; try (solve [econstructor; eauto; constructor])) using.
    inversion 1; subst... destruct a... destruct c...
    destruct ((pc' =? n) && wf_transition_block_opt o b') eqn:?...
    apply wf_transition_block_opt_prop in H1. inv H1. inv H4.
    inv H4. apply map_falsy_list; auto.
  Qed.

  Lemma exec_if_conv2 :
    forall A B x0 ge sp pc' b' tb i i' x x1 cf,
      step_list2 (@Gible.step_instr A B ge) sp (Iexec i) x0 (Iexec i') ->
      cf <> RBgoto pc' \/ ~ wf_trans x b' ->
      if_conv_replace pc' b' (x0 ++ RBexit x cf :: x1) tb ->
      exists b rb,
        tb = b ++ RBexit x cf :: rb
        /\ step_list2 (Gible.step_instr ge) sp (Iexec i) b (Iexec i').
  Proof using.
    induction x0; simplify.
    - inv H1. inv H. exists nil. exists b'0.
      split; [|constructor]. rewrite app_nil_l.
      replace (RBexit x cf :: b'0) with ((RBexit x cf :: nil) ++ b'0) by auto.
      f_equal. simplify. destruct cf; auto.
      rewrite wf_trans_comp_false; auto.
    - inv H1. inv H.
      destruct i1; [|exfalso; eapply step_list2_false; eauto].
      exploit IHx0; eauto; simplify.
      exists (if_convert_block pc' b' a ++ x2). exists x3.
      split. rewrite app_assoc. auto.
      eapply step_list2_app; eauto.
      apply exec_if_conv3; auto.
  Qed.

  Lemma predicate_use_eval_predf :
    forall p1 pr p0 b0 b1,
      ~ In p0 (predicate_use p1) ->
      eval_predf pr p1 = b1 ->
      eval_predf pr # p0 <- b0 p1 = b1.
  Proof using.
    induction p1; crush.
    - destruct_match. inv Heqp1. simplify.
      unfold not in *.
      destruct (peq p1 p0); subst; try solve [exfalso; auto].
      unfold eval_predf. simplify. rewrite ! Pos2Nat.id.
      rewrite ! Regmap.gso; auto.
    - rewrite eval_predf_Pand in *.
      assert ((~ In p0 (predicate_use p1_1)) /\ (~ In p0 (predicate_use p1_2))).
      { unfold not in *; split; intros; apply H; apply in_or_app; tauto. }
      simplify.
      erewrite IHp1_1; eauto.
      erewrite IHp1_2; eauto.
    - rewrite eval_predf_Por in *.
      assert ((~ In p0 (predicate_use p1_1)) /\ (~ In p0 (predicate_use p1_2))).
      { unfold not in *; split; intros; apply H; apply in_or_app; tauto. }
      simplify.
      erewrite IHp1_1; eauto.
      erewrite IHp1_2; eauto.
  Qed.

  Lemma wf_trans_stays_truthy :
    forall A B (ge: Genv.t A B) sp i a i' p b,
      Gible.step_instr ge sp (Iexec i) a (Iexec i') ->
      wf_trans p b ->
      In a b ->
      truthy (is_ps i) p ->
      truthy (is_ps i') p.
  Proof using.
    inversion 1; subst; auto; intros;
    cbn [ is_ps ] in *.
    inv H0; constructor; [].
    apply H4 in H1. inv H2.
    apply predicate_use_eval_predf; auto.
  Qed.

  Lemma wf_trans_cons :
    forall x a b',
      wf_trans x (a :: b') ->
      wf_trans x b'.
  Proof using. inversion 1; subst; cbn in *; constructor; eauto. Qed.

  Lemma map_truthy_step:
    forall A B (ge: Genv.t A B) b' sp i x i' c,
      truthy (is_ps i) x ->
      wf_trans x b' ->
      SeqBB.step tge sp (Iexec i) b' (Iterm i' c) ->
      SeqBB.step tge sp (Iexec i) (map (map_if_convert x) b') (Iterm i' c).
  Proof using.
    induction b'; crush.
    inv H1.
    - econstructor.
      apply map_truthy_instr; eauto.
      eapply IHb'; auto.
      eapply wf_trans_stays_truthy; eauto. constructor; auto.
      apply wf_trans_cons with (a:=a); auto.
    - constructor; apply map_truthy_instr; auto.
  Qed.

  Lemma exec_if_conv :
    forall A B ge sp x0 pc' b' tb i i' x x1,
      step_list2 (@Gible.step_instr A B ge) sp (Iexec i) x0 (Iexec i') ->
      wf_trans x b' ->
      if_conv_replace pc' b' (x0 ++ RBexit x (RBgoto pc') :: x1) tb ->
      exists b rb,
        tb = b ++ (map (map_if_convert x) b') ++ rb
        /\ step_list2 (Gible.step_instr ge) sp (Iexec i) b (Iexec i').
  Proof using.
    induction x0; simplify.
    - inv H1. inv H. exists nil. exists b'0.
      split; [|constructor]. rewrite app_nil_l.
      f_equal. simplify. apply wf_transition_block_opt_prop in H0. rewrite H0.
      rewrite Pos.eqb_refl. auto.
    - inv H1. inv H.
      destruct i1; [|exfalso; eapply step_list2_false; eauto].
      exploit IHx0; eauto; simplify.
      exists (if_convert_block pc' b' a ++ x2). exists x3.
      split. rewrite app_assoc. auto.
      eapply step_list2_app; eauto.
      apply exec_if_conv3; auto.
  Qed.

  Lemma match_none_correct :
    forall t s1' stk f sp pc rs m pr rs' m' bb pr' cf stk' l,
      (fn_code f) ! pc = Some bb ->
      SeqBB.step ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' pr' m') cf t s1' ->
      Forall2 match_stackframe stk stk' ->
      exists b' s2',
        (plus step tge (State stk' (transf_function l f) sp pc rs pr m) t s2' \/
           star step tge (State stk' (transf_function l f) sp pc rs pr m) t s2'
           /\ ltof (option SeqBB.t) measure b' None) /\
          match_states b' s1' s2'.
  Proof.
    intros * H H0 H1 STK.
    pose proof (transf_spec_correct f pc l) as X; inv X.
    - apply sim_plus. rewrite H in H2. symmetry in H2.
      exploit step_cf_eq; eauto; simplify.
      do 3 econstructor. apply plus_one. econstructor; eauto.
      apply seqbb_eq; eauto. eauto.
    - simplify.
      exploit exec_rbexit_truthy; eauto; simplify.
      destruct (cf_wf_dec x b' cf pc'); subst; simplify.
      + inv H1.
        exploit exec_if_conv; eauto; simplify.
        apply sim_star. exists (Some b'). exists (State stk' (transf_function l f) sp pc rs pr m).
        simplify; try (unfold ltof; auto). apply star_refl.
        econstructor; auto.
        simplify. econstructor; eauto.
        unfold sem_extrap; simplify.
        destruct out_s. exfalso; eapply step_list_false; eauto.
        apply append. exists (mki rs' pr' m'). split.
        eapply step_list_2_eq; eauto.
        apply append2. eapply map_truthy_step; eauto.
        econstructor; eauto. constructor; auto.
      + exploit exec_if_conv2; eauto; simplify.
        exploit step_cf_eq; eauto; simplify.
        apply sim_plus. exists None. exists x4.
        split. apply plus_one. econstructor; eauto.
        apply append. exists (mki rs' pr' m'). split; auto.
        apply step_list_2_eq; auto.
        constructor. constructor; auto. auto.
  Qed.

  Lemma match_some_correct:
    forall t s1' s f sp pc rs m pr rs' m' bb pr' cf stk' b0 pc1 rs1 p0 m1 l,
      step ge (State s f sp pc rs pr m) t s1' ->
      (fn_code f) ! pc = Some bb ->
      SeqBB.step ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf) ->
      step_cf_instr ge (State s f sp pc rs' pr' m') cf t s1' ->
      Forall2 match_stackframe s stk' ->
      (fn_code f) ! pc = Some b0 ->
      sem_extrap (transf_function l f) pc1 sp (Iexec (mki rs pr m)) (Iexec (mki rs1 p0 m1)) b0 ->
      (forall b',
          f.(fn_code)!pc1 = Some b' ->
          exists tb, (transf_function l f).(fn_code)!pc1 = Some tb /\ if_conv_replace pc b0 b' tb) ->
      step ge (State s f sp pc1 rs1 p0 m1) E0 (State s f sp pc rs pr m) ->
      exists b' s2',
        (plus step tge (State stk' (transf_function l f) sp pc1 rs1 p0 m1) t s2' \/
           star step tge (State stk' (transf_function l f) sp pc1 rs1 p0 m1) t s2' /\
             ltof (option SeqBB.t) measure b' (Some b0)) /\ match_states b' s1' s2'.
  Proof.
    intros * H H0 H1 H2 STK IS_B EXTRAP IS_TB SIM.
    rewrite IS_B in H0; simplify.
    exploit step_cf_eq; eauto; simplify.
    apply sim_plus.
    exists None. exists x.
    split; auto.
    unfold sem_extrap in *.
    inv SIM.
    pose proof (IS_TB _ H13); simplify.
    apply plus_one.
    econstructor; eauto. eapply EXTRAP; auto. eapply seqbb_eq; eauto.
  Qed.

  Lemma transf_correct:
    forall s1 t s1',
      step ge s1 t s1' ->
      forall b s2, match_states b s1 s2 ->
        exists b' s2',
          (plus step tge s2 t s2' \/
             (star step tge s2 t s2' /\ ltof _ measure b' b))
          /\ match_states b' s1' s2'.
  Proof using TRANSL.
    inversion 1; subst; simplify;
      match goal with H: context[match_states] |- _ => inv H end.
    - eauto using match_some_correct.
    - eauto using match_none_correct.
    - apply sim_plus. remember (transf_function l f) as tf. symmetry in Heqtf. func_info.
      exists None. eexists. split.
      apply plus_one. constructor; eauto. rewrite <- H1. eassumption.
      rewrite <- H4. rewrite <- H2. econstructor; auto.
    - apply sim_plus. exists None. eexists. split.
      apply plus_one. constructor; eauto.
      constructor; auto.
   - apply sim_plus. remember (transf_function None f) as tf. symmetry in Heqtf. func_info.
      exists None. inv STK. inv H7. eexists. split. apply plus_one. constructor.
      econstructor; auto.
  Qed.

  Theorem transf_program_correct:
    forward_simulation (semantics prog) (semantics tprog).
  Proof using TRANSL.
    eapply (Forward_simulation
              (L1:=semantics prog)
              (L2:=semantics tprog)
              (ltof _ measure) match_states).
    constructor.
    - apply well_founded_ltof.
    - eauto using transf_initial_states.
    - intros; eapply transf_final_states; eauto.
    - eapply transf_correct.
    - apply senv_preserved.
  Qed.

End CORRECTNESS.
