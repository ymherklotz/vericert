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

#[local] Opaque decide_if_convert.
#[local] Opaque get_loops.
#[local] Opaque ifconv_list.

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

Lemma transf_spec_correct' :
  forall f pc b,
    f.(fn_code) ! pc = Some b ->
    exists b', (transf_function f).(fn_code) ! pc = Some b'
          /\ if_conv_block_spec f.(fn_code) b b'.
Proof. Admitted.

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

Lemma transf_spec_correct :
  forall f pc,
    if_conv_spec f.(fn_code) (transf_function f).(fn_code) pc.
Proof. Admitted.

Section CORRECTNESS.

  Context (prog tprog : program).

  Let ge : genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

  Definition sem_extrap f pc sp in_s in_s' block :=
    forall out_s block2,
      SeqBB.step tge sp in_s block out_s ->
      f.(fn_code) ! pc = Some block2 ->
      SeqBB.step tge sp in_s' block2 out_s.

  (* (EXT: sem_extrap tf pc0 sp (Iexec (mki rs p m)) (Iexec (mki rs0 p0 m0)) b)
     (STAR: star step ge (State stk f sp pc0 rs0 p0 m0) E0 (State stk f sp pc rs p m))
     (IS_B: exists b, f.(fn_code)!pc0 = Some b)
     (SPEC: forall b_o, f.(fn_code) ! pc = Some b_o -> if_conv_block_spec f.(fn_code) b_o b),
   *)

  Variant match_states : option SeqBB.t -> state -> state -> Prop :=
    | match_state_some :
      forall stk stk' f tf sp pc rs p m b pc0 rs0 p0 m0
             (TF: transf_function f = tf)
             (STK: Forall2 match_stackframe stk stk')
             (* This can be improved with a recursive relation for a more general structure of the
                if-conversion proof. *)
             (IS_B: f.(fn_code)!pc = Some b)
             (EXTRAP: sem_extrap tf pc0 sp (Iexec (mki rs p m)) (Iexec (mki rs0 p0 m0)) b)
             (SIM: step ge (State stk f sp pc0 rs0 p0 m0) E0 (State stk f sp pc rs p m)),
        match_states (Some b) (State stk f sp pc rs p m) (State stk' tf sp pc0 rs0 p0 m0)
    | match_state_none :
      forall stk stk' f tf sp pc rs p m
             (TF: transf_function f = tf)
             (STK: Forall2 match_stackframe stk stk'),
        match_states None (State stk f sp pc rs p m) (State stk' tf sp pc rs p m)
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
    unfold transf_function. destruct_match. auto. auto.
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
      exists s2, initial_state tprog s2 /\ match_states None s1 s2.
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
  Proof. intros; simplify. do 3 econstructor; eauto. Qed.

  Lemma sim_plus :
    forall s1 b t s,
      (exists b' s2, plus step tge s1 t s2 /\ match_states b' s s2) ->
      exists b' s2,
        (plus step tge s1 t s2 \/
           star step tge s1 t s2 /\ ltof _ measure b' b) /\
          match_states b' s s2.
  Proof. intros; simplify. do 3 econstructor; eauto. Qed.

  Lemma step_instr :
    forall sp s s' a,
      step_instr ge sp (Iexec s) a (Iexec s') ->
      step_instr tge sp (Iexec s) a (Iexec s').
  Proof.
    inversion 1; subst; econstructor; eauto.
    - now rewrite <- eval_op_eq.
    - now rewrite <- eval_addressing_eq.
    - now rewrite <- eval_addressing_eq.
  Qed.

  Lemma step_instr_term :
    forall sp s s' a cf,
      Gible.step_instr ge sp (Iexec s) a (Iterm s' cf) ->
      Gible.step_instr tge sp (Iexec s) a (Iterm s' cf).
  Proof. inversion 1; subst; constructor; auto. Qed.

  Lemma seqbb_eq :
    forall bb sp rs pr m rs' pr' m' cf,
      SeqBB.step ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf) ->
      SeqBB.step tge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf).
  Proof.
    induction bb; crush; inv H.
    - econstructor; eauto. apply step_instr; eassumption.
      destruct state'. eapply IHbb; eauto.
    - constructor; apply step_instr_term; auto.
  Qed.

  Lemma fn_all_eq :
    forall f tf,
      transf_function f = tf ->
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
      H: transf_function _ = _ |- _ =>
        let H2 := fresh "ALL_EQ" in
        pose proof (fn_all_eq _ _ H) as H2; simplify
    end.

  Lemma step_cf_eq :
    forall stk stk' f tf sp pc rs pr m cf s t,
      step_cf_instr ge (State stk f sp pc rs pr m) cf t s ->
      Forall2 match_stackframe stk stk' ->
      transf_function f = tf ->
      exists s', step_cf_instr tge (State stk' tf sp pc rs pr m) cf t s'
                 /\ match_states None s s'.
  Proof.
    inversion 1; subst; simplify;
      try solve [func_info; do 2 econstructor; econstructor; eauto].
    - do 2 econstructor. constructor; eauto. constructor; eauto. constructor; auto.
      constructor. auto.
    - do 2 econstructor. constructor; eauto.
      func_info.
      rewrite H2 in *. rewrite H12. auto. constructor; auto.
    - func_info. do 2 econstructor. econstructor; eauto. rewrite H2 in *.
      eauto. econstructor; auto.
  Qed.

  (*Lemma event0_trans :
    forall stk f sp pc rs' pr' m' cf t f0 sp0 pc0 rs0 pr0 m0 stack,
      step_cf_instr ge (State stk f sp pc rs' pr' m') cf t (State stack f0 sp0 pc0 rs0 pr0 m0) ->
      t = E0 /\ f = f0 /\ sp = sp0 /\ stk = stack.
  Proof.
    inversion 1; subst; crush.*)

  Lemma cf_dec :
    forall a pc, {a = RBgoto pc} + {a <> RBgoto pc}.
  Proof.
    destruct a; try solve [right; crush].
    intros. destruct (peq n pc); subst.
    left; auto.
    right. unfold not in *; intros. inv H. auto.
  Qed.

  Lemma exec_if_conv :
    forall bb sp rs pr m rs' pr' m' pc' b' tb,
      SeqBB.step ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') (RBgoto pc')) ->
      if_conv_replace pc' b' bb tb ->
      exists p b rb,
        tb = b ++ (map (map_if_convert p) b') ++ rb
        /\ SeqBB.step ge sp (Iexec (mki rs pr m)) b (Iexec (mki rs' pr' m')).
  Proof.
    Admitted.

  Lemma temp2:
    forall t s1' stk f sp pc rs m pr rs' m' bb pr' cf stk',
      (fn_code f) ! pc = Some bb ->
      SeqBB.step ge sp (Iexec (mki rs pr m)) bb (Iterm (mki rs' pr' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' pr' m') cf t s1' ->
      Forall2 match_stackframe stk stk' ->
      exists b' s2',
        (plus step tge (State stk' (transf_function f) sp pc rs pr m) t s2' \/
           star step tge (State stk' (transf_function f) sp pc rs pr m) t s2'
           /\ ltof (option SeqBB.t) measure b' None) /\
          match_states b' s1' s2'.
  Proof.
    intros * H H0 H1 STK.
    pose proof (transf_spec_correct f pc) as X; inv X.
    - apply sim_plus. rewrite H in H2. symmetry in H2.
      exploit step_cf_eq; eauto; simplify.
      do 3 econstructor. apply plus_one. econstructor; eauto.
      apply seqbb_eq; eauto. eauto.
    - simplify.
      destruct (cf_dec cf pc'); subst. inv H1.
      exploit exec_if_conv; eauto; simplify.
      exploit exec_rbexit_truthy; eauto; simplify.
      apply sim_star. exists (Some b'). exists (State stk' (transf_function f) sp pc rs pr m).
      simplify; try (unfold ltof; auto). apply star_refl.
      constructor; auto. unfold sem_extrap; simplify.

  Lemma step_cf_matches :
    forall b s cf t s' ts,
      step_cf_instr ge s cf t s' ->
      match_states b s ts ->
      exists b' ts', step_cf_instr tge ts cf t ts' /\ match_states b' s' ts'.
  Proof. Admitted.

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
    - admit.
    - eauto using temp2. Admitted.


    (* - *)
    (*   exploit temp; eauto; simplify. inv H3. *)
    (*   pose proof (transf_spec_correct _ _ _ H4); simplify. *)
    (*   exploit step_cf_matches; eauto. *)
    (*   econstructor; eauto. unfold sem_extrap; intros. *)
    (*   unfold sem_extrap in EXT. *)
    (*   rewrite H8 in H3; simplify. *)
    (*   do 2 econstructor. split. left. eapply plus_one. econstructor; eauto. *)
    (*   unfold sem_extrap in EXT. eapply EXT. eauto. admit. *)
    (*   instantiate (1 := State stack (transf_function f0) sp0 pc0 rs0 pr0 m0). *)
    (*   admit. constructor; eauto. admit. unfold sem_extrap. intros. admit. *)
    (*   eapply star_refl. intros. admit. *)
    (* - *)
    (*   simplify. inv H2. do 2 econstructor. split. admit. *)
    (*   econstructor; eauto. admit. admit. intros. *)
    (*   rewrite H3 in H2. inv H2. eauto *)

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
