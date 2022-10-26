(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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
Require Import vericert.hls.GiblePargen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.
Require Import vericert.common.Monad.

Module OptionExtra := MonadExtra(Option).
Import OptionExtra.

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

#[local] Opaque simplify.
#[local] Opaque deep_simplify.

Ltac destr := destruct_match; try discriminate; [].

(*|
==============
RTLPargenproof
==============

RTLBlock to abstract translation
================================

Correctness of translation from RTLBlock to the abstract interpretation language.
|*)

Definition is_regs i := match i with mk_instr_state rs _ _ => rs end.
Definition is_mem i := match i with mk_instr_state _ _ m => m end.
Definition is_ps i := match i with mk_instr_state _ p _ => p end.

Inductive state_lessdef : instr_state -> instr_state -> Prop :=
  state_lessdef_intro :
    forall rs1 rs2 ps1 ps2 m1,
      (forall x, rs1 !! x = rs2 !! x) ->
      (forall x, ps1 !! x = ps2 !! x) ->
      state_lessdef (mk_instr_state rs1 ps1 m1) (mk_instr_state rs2 ps2 m1).

Lemma state_lessdef_refl x : state_lessdef x x.
Proof. destruct x; constructor; auto. Qed.

Lemma state_lessdef_symm x y : state_lessdef x y -> state_lessdef y x.
Proof. destruct x; destruct y; inversion 1; subst; simplify; constructor; auto. Qed.

Lemma state_lessdef_trans :
  forall a b c,
    state_lessdef a b ->
    state_lessdef b c ->
    state_lessdef a c.
Proof.
  inversion 1; inversion 1; subst; simplify.
  constructor; eauto; intros. rewrite H0. auto.
Qed.

#[global] Instance Equivalence_state_lessdef : Equivalence state_lessdef :=
  { Equivalence_Reflexive := state_lessdef_refl;
    Equivalence_Symmetric := state_lessdef_symm;
    Equivalence_Transitive := state_lessdef_trans;
  }.

Definition check_dest i r' :=
  match i with
  | RBop p op rl r => (r =? r')%positive
  | RBload p chunk addr rl r => (r =? r')%positive
  | _ => false
  end.

Lemma check_dest_dec i r : {check_dest i r = true} + {check_dest i r = false}.
Proof. destruct (check_dest i r); tauto. Qed.

Fixpoint check_dest_l l r :=
  match l with
  | nil => false
  | a :: b => check_dest a r || check_dest_l b r
  end.

Lemma check_dest_l_forall :
  forall l r,
  check_dest_l l r = false ->
  Forall (fun x => check_dest x r = false) l.
Proof. induction l; crush. Qed.

Lemma check_dest_l_dec i r : {check_dest_l i r = true} + {check_dest_l i r = false}.
Proof. destruct (check_dest_l i r); tauto. Qed.

Lemma match_states_list :
  forall A (rs: Regmap.t A) rs',
  (forall r, rs !! r = rs' !! r) ->
  forall l, rs ## l = rs' ## l.
Proof. induction l; crush. Qed.

Lemma PTree_matches :
  forall A (v: A) res rs rs',
  (forall r, rs !! r = rs' !! r) ->
  forall x, (Regmap.set res v rs) !! x = (Regmap.set res v rs') !! x.
Proof.
  intros; destruct (Pos.eq_dec x res); subst;
  [ repeat rewrite Regmap.gss by auto
  | repeat rewrite Regmap.gso by auto ]; auto.
Qed.

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
    unfold schedule_oracle, check_control_flow_instr.
    simplify; repeat destruct_match; crush.
  Admitted.

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

  Lemma ge_preserved_lem:
    ge_preserved ge tge.
  Proof using TRANSL.
    unfold ge_preserved.
    eauto with rtlgp.
  Qed.
  Hint Resolve ge_preserved_lem : rtlgp.

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

  Lemma eval_predf_negate :
    forall ps p,
      eval_predf ps (negate p) = negb (eval_predf ps p).
  Proof.
    unfold eval_predf; intros. rewrite negate_correct. auto.
  Qed.

  Lemma is_truthy_negate :
    forall ps p pred,
      truthy ps p ->
      falsy ps (combine_pred (Some (negate (Option.default T p))) pred).
  Proof.
    inversion 1; subst; simplify.
    - destruct pred; constructor; auto.
    - destruct pred; constructor.
      rewrite eval_predf_Pand. rewrite eval_predf_negate. rewrite H0. auto.
      rewrite eval_predf_negate. rewrite H0. auto.
  Qed.

  Lemma sem_pexpr_negate :
    forall A ctx p b,
      sem_pexpr ctx p b ->
      @sem_pexpr A ctx (¬ p) (negb b).
  Proof.
    induction p; crush.
    - destruct_match. destruct b0; crush. inv Heqp0.
      constructor. inv H. rewrite negb_involutive. auto.
      constructor. inv H. auto.
    - inv H. constructor.
    - inv H. constructor.
    - inv H. eapply IHp1 in H2. eapply IHp2 in H4. rewrite negb_andb.
      constructor; auto.
    - inv H. rewrite negb_orb. constructor; auto.
  Qed.

  Lemma sem_pexpr_evaluable :
    forall A ctx f_p ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p, exists b, @sem_pexpr A ctx (from_pred_op f_p p) b.
  Proof.
    induction p; crush.
    - destruct_match. inv Heqp0. destruct b. econstructor. eauto.
      econstructor. eapply sem_pexpr_negate. eauto.
    - econstructor. constructor.
    - econstructor. constructor.
    - econstructor. constructor; eauto.
    - econstructor. constructor; eauto.
  Qed.

  Lemma sem_pexpr_eval1 :
    forall A ctx f_p ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        eval_predf ps p = false ->
        @sem_pexpr A ctx (from_pred_op f_p p) false.
  Proof.
    induction p; crush.
    - destruct_match. inv Heqp0.
      destruct b.
      + cbn in H0. rewrite <- H0.
        rewrite Pos2Nat.id. eauto.
      + replace false with (negb true) by auto.
        apply sem_pexpr_negate. cbn in H0.
        apply negb_true_iff in H0. rewrite negb_involutive in H0.
        rewrite <- H0. rewrite Pos2Nat.id.
        eauto.
     - constructor.
     - rewrite eval_predf_Pand in H0.
       apply andb_false_iff in H0. inv H0. eapply IHp1 in H1.
       pose proof (sem_pexpr_evaluable _ _ _ _ H p2) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace false with (false && x) by auto.
       constructor; auto.
       eapply IHp2 in H1.
       pose proof (sem_pexpr_evaluable _ _ _ _ H p1) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace false with (x && false) by eauto with bool.
       constructor; auto.
     - rewrite eval_predf_Por in H0.
       apply orb_false_iff in H0. inv H0.
       replace false with (false || false) by auto.
       constructor; auto.
  Qed.

  Lemma sem_pexpr_eval2 :
    forall A ctx f_p ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        eval_predf ps p = true ->
        @sem_pexpr A ctx (from_pred_op f_p p) true.
  Proof.
    induction p; crush.
    - destruct_match. inv Heqp0.
      destruct b.
      + cbn in H0. rewrite <- H0.
        rewrite Pos2Nat.id. eauto.
      + replace true with (negb false) by auto.
        apply sem_pexpr_negate. cbn in H0.
        apply negb_true_iff in H0.
        rewrite <- H0. rewrite Pos2Nat.id.
        eauto.
     - constructor.
     - rewrite eval_predf_Pand in H0.
       apply andb_true_iff in H0. inv H0.
       replace true with (true && true) by auto.
       constructor; auto.
     - rewrite eval_predf_Por in H0.
       apply orb_true_iff in H0. inv H0. eapply IHp1 in H1.
       pose proof (sem_pexpr_evaluable _ _ _ _ H p2) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace true with (true || x) by auto.
       constructor; auto.
       eapply IHp2 in H1.
       pose proof (sem_pexpr_evaluable _ _ _ _ H p1) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace true with (x || true) by eauto with bool.
       constructor; auto.
  Qed.

  Lemma sem_pexpr_eval :
    forall A ctx f_p ps b,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        eval_predf ps p = b ->
        @sem_pexpr A ctx (from_pred_op f_p p) b.
  Proof.
    intros; destruct b; eauto using sem_pexpr_eval1, sem_pexpr_eval2.
  Qed.

  Lemma sem_pred_expr_NEapp :
    forall A f_p ctx a b v,
      sem_pred_expr f_p sem_value ctx a v ->
      @sem_pred_expr A _ _ f_p sem_value ctx (NE.app a b) v.
  Proof.
    induction a; crush.
    - inv H. constructor; auto.
    - inv H. constructor; eauto.
      eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma sem_pred_expr_NEapp2 :
    forall A B C sem f_p ctx a b v ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
      (forall x, NE.In x a -> eval_predf ps (fst x) = false) ->
      sem_pred_expr f_p sem ctx b v ->
      @sem_pred_expr A B C f_p sem ctx (NE.app a b) v.
  Proof.
    induction a; crush.
    - assert (IN: NE.In a (NE.singleton a)) by constructor.
      specialize (H0 _ IN). destruct a.
      eapply sem_pred_expr_cons_false; eauto. cbn [fst] in *.
      eapply sem_pexpr_eval; eauto.
    - assert (NE.In a (NE.cons a a0)) by (constructor; tauto).
      apply H0 in H2.
      destruct a. cbn [fst] in *.
      eapply sem_pred_expr_cons_false.
      eapply sem_pexpr_eval; eauto. eapply IHa; eauto.
      intros. eapply H0. constructor; tauto.
  Qed.

  Lemma sem_pred_expr_map_not :
    forall A p ps y x0,
      eval_predf ps p = false ->
      NE.In x0 (NE.map (fun x => (p ∧ fst x, snd x)) y) ->
      eval_predf ps (@fst _ A x0) = false.
  Proof.
    induction y; crush.
    - inv H0. simplify. rewrite eval_predf_Pand. rewrite H. auto.
    - inv H0. inv H2. cbn -[eval_predf]. rewrite eval_predf_Pand.
      rewrite H. auto. eauto.
  Qed.

  Lemma sem_pred_expr_map_Pand :
    forall A B C sem ctx f_p ps x v p,
      (forall x : positive, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      eval_predf ps p = true ->
      sem_pred_expr f_p sem ctx x v ->
      @sem_pred_expr A B C f_p sem ctx
        (NE.map (fun x0 => (p ∧ fst x0, snd x0)) x) v.
  Proof.
    induction x; crush.
    inv H1. simplify. constructor; eauto.
    simplify. replace true with (true && true) by auto.
    constructor; auto.
    eapply sem_pexpr_eval; eauto.
    inv H1. simplify. constructor; eauto.
    simplify. replace true with (true && true) by auto.
    constructor; auto.
    eapply sem_pexpr_eval; eauto.
    eapply sem_pred_expr_cons_false. cbn.
    replace false with (true && false) by auto. constructor; auto.
    eapply sem_pexpr_eval; eauto. eauto.
  Qed.

  Lemma sem_pred_expr_app_predicated :
    forall A B C sem ctx f_p y x v p ps,
      sem_pred_expr f_p sem ctx x v ->
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) (ps !! x)) ->
      eval_predf ps p = true ->
      @sem_pred_expr A B C f_p sem ctx (app_predicated p y x) v.
  Proof.
    intros * SEM PS EVAL. unfold app_predicated.
    eapply sem_pred_expr_NEapp2; eauto.
    intros. eapply sem_pred_expr_map_not; eauto.
    rewrite eval_predf_negate. rewrite EVAL. auto.
    eapply sem_pred_expr_map_Pand; eauto.
  Qed.

  Lemma sem_pred_expr_prune_predicated :
    forall A B C sem ctx f_p y x v,
      sem_pred_expr f_p sem ctx x v ->
      prune_predicated x = Some y ->
      @sem_pred_expr A B C f_p sem ctx y v.
  Proof.
    intros * SEM PRUNE. unfold prune_predicated in *.
    Admitted.

  Inductive sem_ident {B A: Type} (c: @ctx B) (a: A): A -> Prop :=
  | sem_ident_intro : sem_ident c a a.

  Lemma sem_pred_expr_pred_ret :
    forall G A (ctx: @Abstr.ctx G) (i: A) ps,
      sem_pred_expr ps sem_ident ctx (pred_ret i) i.
  Proof. intros; constructor; constructor. Qed.

  Lemma sem_pred_expr_ident :
    forall G A B ps (ctx: @Abstr.ctx G) (l: predicated A) (s: @Abstr.ctx G -> A -> B -> Prop) l_,
      sem_pred_expr ps sem_ident ctx l l_ ->
      forall (v: B),
        s ctx l_ v ->
        sem_pred_expr ps s ctx l v.
  Proof.
    induction 1.
    - intros. constructor; auto. inv H0. auto.
    - intros. apply sem_pred_expr_cons_false; auto.
    - intros. inv H0. constructor; auto.
  Qed.

  Lemma sem_pred_expr_ident2 :
    forall G A B ps (ctx: @Abstr.ctx G) (l: predicated A) (s: @Abstr.ctx G -> A -> B -> Prop) (v: B),
        sem_pred_expr ps s ctx l v ->
        exists l_, sem_pred_expr ps sem_ident ctx l l_ /\ s ctx l_ v.
  Proof.
    induction 1.
    - exists e; split; auto. constructor; auto. constructor.
    - inversion_clear IHsem_pred_expr as [x IH].
      inversion_clear IH as [SEM EVALS].
      exists x; split; auto. apply sem_pred_expr_cons_false; auto.
    - exists e; split; auto; constructor; auto; constructor.
  Qed.

  Fixpoint of_elist (e: expression_list): list expression :=
    match e with
    | Econs a b => a :: of_elist b
    | Enil => nil
    end.

  Fixpoint to_elist (e: list expression): expression_list :=
    match e with
    | a :: b => Econs a (to_elist b)
    | nil => Enil
    end.

  Lemma sem_pred_expr_merge :
    forall G (ctx: @Abstr.ctx G) args ps l,
      Forall2 (sem_pred_expr ps sem_ident ctx) args l ->
      sem_pred_expr ps sem_ident ctx (merge args) (to_elist l).
  Proof. Admitted.

  Lemma sem_val_list_elist :
    forall G (ctx: @Abstr.ctx G) l j,
      sem_val_list ctx (to_elist l) j ->
      Forall2 (sem_value ctx) l j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_val_list_elist2 :
    forall G (ctx: @Abstr.ctx G) l j,
      Forall2 (sem_value ctx) l j ->
      sem_val_list ctx (to_elist l) j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_val_list_elist3 :
    forall G (ctx: @Abstr.ctx G) l j,
      sem_val_list ctx l j ->
      Forall2 (sem_value ctx) (of_elist l) j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_val_list_elist4 :
    forall G (ctx: @Abstr.ctx G) l j,
      Forall2 (sem_value ctx) (of_elist l) j ->
      sem_val_list ctx l j.
  Proof. induction l; intros; cbn in *; inversion H; constructor; eauto. Qed.

  Lemma sem_pred_expr_predicated_map :
    forall A B C pr (f: C -> B) ctx (pred: predicated C) (pred': C),
      sem_pred_expr pr sem_ident ctx pred pred' ->
      @sem_pred_expr A _ _ pr sem_ident ctx (predicated_map f pred) (f pred').
  Proof.
    induction pred; unfold predicated_map; intros.
    - inv H. inv H3. constructor; eauto. constructor.
    - inv H. inv H5. constructor; eauto. constructor.
      eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma NEapp_NEmap :
    forall A B (f: A -> B) a b,
      NE.map f (NE.app a b) = NE.app (NE.map f a) (NE.map f b).
  Proof. induction a; crush. Qed.

  Lemma sem_pred_expr_predicated_prod :
    forall A B C pr ctx (a: predicated C) (b: predicated B) a' b',
      sem_pred_expr pr sem_ident ctx a a' ->
      sem_pred_expr pr sem_ident ctx b b' ->
      @sem_pred_expr A _ _ pr sem_ident ctx (predicated_prod a b) (a', b').
  Proof.
    induction a; intros.
    - inv H. inv H4. unfold predicated_prod.
      generalize dependent b. induction b; intros.
      + cbn. destruct_match. inv Heqp. inv H0. inv H6.
        constructor. simplify. replace true with (true && true) by auto.
        eapply sem_pexpr_Pand; eauto. constructor.
      + inv H0. inv H6. cbn. constructor; cbn.
        replace true with (true && true) by auto.
        constructor; auto. constructor.
        eapply sem_pred_expr_cons_false; eauto.
        cbn.
        replace false with (true && false) by auto.
        constructor; auto.
    - unfold predicated_prod. simplify.
      rewrite NEapp_NEmap.

  Lemma sem_pred_expr_seq_app :
    forall G A B (f: predicated (A -> B))
        ps (ctx: @ctx G) l f_ l_,
      sem_pred_expr ps sem_ident ctx l l_ ->
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (seq_app f l) (f_ l_).
  Proof. Admitted.

  Lemma sem_pred_expr_map :
    forall A B C (ctx: @ctx A) ps (f: B -> C) y v,
      sem_pred_expr ps sem_ident ctx y v ->
      sem_pred_expr ps sem_ident ctx (NE.map (fun x => (fst x, f (snd x))) y) (f v).
  Proof.
    induction y; crush. inv H. constructor; crush. inv H3. constructor.
    inv H. inv H5. constructor; eauto. constructor.
    eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma sem_pred_expr_flap :
    forall G A B C (f: predicated (A -> B -> C))
        ps (ctx: @ctx G) l f_,
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (flap f l) (f_ l).
  Proof.
    induction f. unfold flap2; intros. inv H. inv H3.
    constructor; eauto. constructor.
    intros. inv H. cbn.
    constructor; eauto. inv H5. constructor.
    eapply sem_pred_expr_cons_false; eauto.
   Qed.

  Lemma sem_pred_expr_flap2 :
    forall G A B C (f: predicated (A -> B -> C))
        ps (ctx: @ctx G) l1 l2 f_,
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (flap2 f l1 l2) (f_ l1 l2).
  Proof.
    induction f. unfold flap2; intros. inv H. inv H3.
    constructor; eauto. constructor.
    intros. inv H. cbn.
    constructor; eauto. inv H5. constructor.
    eapply sem_pred_expr_cons_false; eauto.
  Qed.

  Lemma sem_pred_expr_seq_app_val :
    forall G A B V (s: @Abstr.ctx G -> B -> V -> Prop)
        (f: predicated (A -> B))
        ps ctx l v f_ l_,
      sem_pred_expr ps sem_ident ctx l l_ ->
      sem_pred_expr ps sem_ident ctx f f_ ->
      s ctx (f_ l_) v ->
      sem_pred_expr ps s ctx (seq_app f l) v.
  Proof.
    intros. eapply sem_pred_expr_ident; [|eassumption].
    eapply sem_pred_expr_seq_app; eauto.
  Qed.

  Fixpoint Eapp a b :=
    match a with
    | Enil => b
    | Econs ax axs => Econs ax (Eapp axs b)
    end.

  Lemma Eapp_right_nil :
    forall a, Eapp a Enil = a.
  Proof. induction a; cbn; try rewrite IHa; auto. Qed.

  Lemma Eapp_left_nil :
    forall a, Eapp Enil a = a.
  Proof. auto. Qed.

  Lemma sem_pred_expr_cons_pred_expr :
    forall A (ctx: @ctx A) pr s s' a e,
      sem_pred_expr pr sem_ident ctx s s' ->
      sem_pred_expr pr sem_ident ctx a e ->
      sem_pred_expr pr sem_ident ctx (cons_pred_expr a s) (Econs e s').
  Proof.
    intros. unfold cons_pred_expr.
    replace (Econs e s') with ((uncurry Econs) (e, s')) by auto.
    eapply sem_pred_expr_predicated_map.
    eapply sem_pred_expr_predicated_prod; eauto.
  Qed.

  Lemma sem_pred_expr_fold_right :
    forall A pr ctx s a a' s',
      sem_pred_expr pr sem_ident ctx s s' ->
      Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a') ->
      @sem_pred_expr A _ _ pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s').
  Proof.
    induction a; crush. inv H0. inv H5. destruct a'; crush. destruct a'; crush.
    inv H3. apply sem_pred_expr_cons_pred_expr; auto.
    inv H0. destruct a'; crush. inv H3.
    apply sem_pred_expr_cons_pred_expr; auto.
  Qed.

  Lemma sem_pred_expr_fold_right2 :
    forall A pr ctx s a a' s',
      sem_pred_expr pr sem_ident ctx s s' ->
      @sem_pred_expr A _ _ pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s') ->
      Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a').
  Proof.
    induction a. Admitted.

  Lemma NEof_list_some :
    forall A a a' (e: A),
      NE.of_list a = Some a' ->
      NE.of_list (e :: a) = Some (NE.cons e a').
  Proof.
    induction a; [crush|].
    intros.
    cbn in H. destruct a0. inv H. auto.
    destruct_match; [|discriminate].
    inv H. specialize (IHa n a ltac:(trivial)).
    cbn. destruct_match. unfold NE.of_list in IHa.
    fold (@NE.of_list A) in IHa. rewrite IHa in Heqo0. inv Heqo0. auto.
    unfold NE.of_list in IHa. fold (@NE.of_list A) in IHa. rewrite IHa in Heqo0. inv Heqo0.
  Qed.

  Lemma NEof_list_contra :
    forall A b (a: A),
      ~ NE.of_list (a :: b) = None.
  Proof.
    induction b; try solve [crush].
    intros.
    specialize (IHb a).
    enough (X: exists x, NE.of_list (a :: b) = Some x).
    inversion_clear X as [x X'].
    erewrite NEof_list_some; eauto; discriminate.
    destruct (NE.of_list (a :: b)) eqn:?; [eauto|contradiction].
  Qed.

  Lemma NEof_list_exists :
    forall A b (a: A),
      exists x, NE.of_list (a :: b) = Some x.
  Proof.
    intros. pose proof (NEof_list_contra _ b a).
    destruct (NE.of_list (a :: b)); try contradiction.
    eauto.
  Qed.

  Lemma NEof_list_exists2 :
    forall A b (a c: A),
      exists x,
        NE.of_list (c :: a :: b) = Some (NE.cons c x)
        /\ NE.of_list (a :: b) = Some x.
  Proof.
    intros. pose proof (NEof_list_exists _ b a).
    inversion_clear H as [x B].
    econstructor; split; eauto.
    eapply NEof_list_some; eauto.
  Qed.

  Lemma NEof_list_to_list :
    forall A (x: list A) y,
      NE.of_list x = Some y ->
      NE.to_list y = x.
  Proof.
    induction x; [crush|].
    intros. destruct x; [crush|].
    pose proof (NEof_list_exists2 _ x a0 a).
    inversion_clear H0 as [x0 [HN1 HN2]]. rewrite HN1 in H. inv H.
    cbn. f_equal. eauto.
  Qed.

  Lemma sem_pred_expr_merge2 :
    forall A (ctx: @ctx A) pr l l',
      sem_pred_expr pr sem_ident ctx (merge l) l' ->
      Forall2 (sem_pred_expr pr sem_ident ctx) l (of_elist l').
  Proof.
    induction l; crush.
    - unfold merge in *; cbn in *.
      inv H. inv H5. constructor.
    - unfold merge in H.
      pose proof (NEof_list_exists _ l a) as Y.
      inversion_clear Y as [x HNE]. rewrite HNE in H.
      erewrite <- (NEof_list_to_list _ (a :: l)) by eassumption.
      apply sem_pred_expr_fold_right2 with (s := (NE.singleton (T, Enil))) (s' := Enil).
      repeat constructor.
      rewrite Eapp_right_nil. auto.
  Qed.

  Lemma sem_merge_list :
    forall A ctx f rs ps m args,
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_val_list ctx
        (merge (list_translation args f)) (rs ## args).
  Proof.
    induction args; crush. cbn. constructor; constructor.
    unfold merge. specialize (IHargs H).
    eapply sem_pred_expr_ident2 in IHargs.
    inversion_clear IHargs as [l_ [HSEM HVAL]].
    destruct_match; [|exfalso; eapply NEof_list_contra; eauto].
    destruct args; cbn -[NE.of_list] in *.
    - unfold merge in *. simplify.
      inv H. inv H6. specialize (H a).
      eapply sem_pred_expr_ident2 in H.
      inversion_clear H as [l_2 [HSEM2 HVAL2]].
      unfold cons_pred_expr.
      eapply sem_pred_expr_ident.
      eapply sem_pred_expr_predicated_map.
      eapply sem_pred_expr_predicated_prod. eassumption.
      constructor. constructor. constructor.
      constructor. eauto. constructor.
    - pose proof (NEof_list_exists2 _ (list_translation args f) (f #r (Reg r)) (f #r (Reg a))) as Y.
      inversion_clear Y as [x [Y1 Y2]]. rewrite Heqo in Y1. inv Y1.
      inversion_clear H as [? ? ? ? ? ? REG PRED MEM EXIT].
      inversion_clear REG as [? ? ? REG'].
      inversion_clear PRED as [? ? ? PRED'].
      pose proof (REG' a) as REGa. pose proof (REG' r) as REGr.
      exploit sem_pred_expr_ident2; [exact REGa|].
      intro REGI'; inversion_clear REGI' as [a' [SEMa SEMa']].
      exploit sem_pred_expr_ident2; [exact REGr|].
      intro REGI'; inversion_clear REGI' as [r' [SEMr SEMr']].
      apply sem_pred_expr_ident with (l_ := Econs a' l_); [|constructor; auto].
      replace (Econs a' l_) with (Eapp (Econs a' l_) Enil) by (now apply Eapp_right_nil).
      apply sem_pred_expr_fold_right. repeat constructor.
      cbn. constructor; eauto.
      erewrite NEof_list_to_list; eauto.
      eapply sem_pred_expr_merge2; auto.
  Qed.

  Lemma sem_pred_expr_list_translation :
    forall G ctx args f i,
      @sem G ctx f (i, None) ->
      exists l,
        Forall2 (sem_pred_expr (forest_preds f) sem_ident ctx) (list_translation args f) l
        /\ sem_val_list ctx (to_elist l) ((is_rs i)##args).
  Proof.
    induction args; intros.
    - exists nil; cbn; split; auto; constructor.
    - exploit IHargs; try eassumption; intro EX.
      inversion_clear EX as [l [FOR SEM]].
      destruct i as [rs' m' ps'].
      inversion_clear H as [? ? ? ? ? ? REGSET PREDSET MEM EXIT].
      inversion_clear REGSET as [? ? ? REG].
      pose proof (REG a).
      exploit sem_pred_expr_ident2; eauto; intro IDENT.
      inversion_clear IDENT as [l_ [SEMP SV]].
      exists (l_ :: l). split. constructor; auto.
      cbn; constructor; auto.
  Qed.

  Lemma sem_update_Iop :
    forall A op rs args m v f ps ctx,
      Op.eval_operation (ctx_ge ctx) (ctx_sp ctx) op rs ## args (is_mem (ctx_is ctx)) = Some v ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_value ctx
        (seq_app (pred_ret (Eop op)) (merge (list_translation args f))) v.
  Proof.
    intros * EVAL SEM.
    exploit sem_pred_expr_list_translation; try eassumption.
    intro H; inversion_clear H as [x [HS HV]].
    eapply sem_pred_expr_seq_app_val.
    - cbn in *; eapply sem_pred_expr_merge; eauto.
    - apply sem_pred_expr_pred_ret.
    - econstructor; [eauto|]; auto.
  Qed.

  Lemma sem_update_Iload :
    forall A rs args m v f ps ctx addr a0 chunk,
      Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr rs ## args = Some a0 ->
      Mem.loadv chunk m a0 = Some v ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_value ctx
        (seq_app (seq_app (pred_ret (Eload chunk addr)) (merge (list_translation args f))) (f #r Mem)) v.
  Proof.
    intros * EVAL MEM SEM.
    exploit sem_pred_expr_list_translation; try eassumption.
    intro H; inversion_clear H as [x [HS HV]].
    inversion SEM as [? ? ? ? ? ? REG PRED HMEM EXIT]; subst.
    exploit sem_pred_expr_ident2; [eapply HMEM|].
    intros H; inversion_clear H as [x' [HS' HV']].
    eapply sem_pred_expr_seq_app_val; eauto.
    { eapply sem_pred_expr_seq_app; eauto.
      - eapply sem_pred_expr_merge; eauto.
      - apply sem_pred_expr_pred_ret.
    }
    econstructor; eauto.
  Qed.

  Lemma storev_valid_pointer1 :
    forall chunk m m' s d b z,
      Mem.storev chunk m s d = Some m' ->
      Mem.valid_pointer m b z = true ->
      Mem.valid_pointer m' b z = true.
  Proof using.
    intros. unfold Mem.storev in *. destruct_match; try discriminate; subst.
    apply Mem.valid_pointer_nonempty_perm. apply Mem.valid_pointer_nonempty_perm in H0.
    eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma storev_valid_pointer2 :
    forall chunk m m' s d b z,
      Mem.storev chunk m s d = Some m' ->
      Mem.valid_pointer m' b z = true ->
      Mem.valid_pointer m b z = true.
  Proof using.
    intros. unfold Mem.storev in *. destruct_match; try discriminate; subst.
    apply Mem.valid_pointer_nonempty_perm. apply Mem.valid_pointer_nonempty_perm in H0.
    eapply Mem.perm_store_2; eauto.
  Qed.

  Definition valid_mem m m' :=
    forall b z, Mem.valid_pointer m b z = Mem.valid_pointer m' b z.

  Lemma storev_valid_pointer :
    forall chunk m m' s d,
      Mem.storev chunk m s d = Some m' ->
      valid_mem m m'.
  Proof using.
    unfold valid_mem. symmetry.
    intros. destruct (Mem.valid_pointer m b z) eqn:?;
                     eauto using storev_valid_pointer1.
    apply not_true_iff_false.
    apply not_true_iff_false in Heqb0.
    eauto using storev_valid_pointer2.
  Qed.

  Lemma storev_cmpu_bool :
    forall m m' c v v0,
      valid_mem m m' ->
      Val.cmpu_bool (Mem.valid_pointer m) c v v0 = Val.cmpu_bool (Mem.valid_pointer m') c v v0.
  Proof using.
    unfold valid_mem.
    intros. destruct v, v0; crush.
    { destruct_match; crush.
      destruct_match; crush.
      destruct_match; crush.
      apply orb_true_iff in H1.
      inv H1. rewrite H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush.
      destruct_match; auto. simplify.
      apply orb_true_iff in H1.
      inv H1. rewrite <- H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite <- H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush. }

    { destruct_match; crush.
      destruct_match; crush.
      destruct_match; crush.
      apply orb_true_iff in H1.
      inv H1. rewrite H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush.
      destruct_match; auto. simplify.
      apply orb_true_iff in H1.
      inv H1. rewrite <- H in H2. rewrite H2 in Heqb1.
      simplify. rewrite H0 in Heqb1. crush.
      rewrite <- H in H2. rewrite H2 in Heqb1.
      rewrite H0 in Heqb1. crush. }

    { destruct_match; auto. destruct_match; auto; crush.
      { destruct_match; crush.
        { destruct_match; crush.
          setoid_rewrite H in H0; eauto.
          setoid_rewrite H in H1; eauto.
          rewrite H0 in Heqb. rewrite H1 in Heqb; crush.
        }
        { destruct_match; crush.
          setoid_rewrite H in Heqb0; eauto.
          rewrite H0 in Heqb0. rewrite H1 in Heqb0; crush. } }
      { destruct_match; crush.
        { destruct_match; crush.
          setoid_rewrite H in H0; eauto.
          setoid_rewrite H in H1; eauto.
          rewrite H0 in Heqb0. rewrite H1 in Heqb0; crush.
        }
        { destruct_match; crush.
          setoid_rewrite H in Heqb0; eauto.
          rewrite H0 in Heqb0. rewrite H1 in Heqb0; crush. } } }
  Qed.

  Lemma storev_eval_condition :
    forall m m' c rs,
      valid_mem m m' ->
      Op.eval_condition c rs m = Op.eval_condition c rs m'.
  Proof using.
    intros. destruct c; crush.
    destruct rs; crush.
    destruct rs; crush.
    destruct rs; crush.
    eapply storev_cmpu_bool; eauto.
    destruct rs; crush.
    destruct rs; crush.
    eapply storev_cmpu_bool; eauto.
  Qed.

  Lemma eval_operation_valid_pointer :
    forall A B (ge: Genv.t A B) sp op args m m' v,
      valid_mem m m' ->
      Op.eval_operation ge sp op args m' = Some v ->
      Op.eval_operation ge sp op args m = Some v.
  Proof.
    intros * VALID OP. destruct op; auto.
    - destruct cond; auto; cbn in *.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
    - destruct c; auto; cbn in *.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
      + repeat destruct_match; auto. setoid_rewrite <- storev_cmpu_bool in OP; eauto.
  Qed.

  Lemma bb_memory_consistency_eval_operation :
    forall A B (ge: Genv.t A B) sp state i state' args op v,
      step_instr ge sp (Iexec state) i (Iexec state') ->
      Op.eval_operation ge sp op args (is_mem state) = Some v ->
      Op.eval_operation ge sp op args (is_mem state') = Some v.
  Proof.
    inversion_clear 1; intro EVAL; auto.
    cbn in *.
    eapply eval_operation_valid_pointer. unfold valid_mem. symmetry.
    eapply storev_valid_pointer; eauto.
    auto.
  Qed.

  Lemma truthy_dflt :
    forall ps p,
      truthy ps p -> eval_predf ps (dfltp p) = true.
  Proof. intros. destruct p; cbn; inv H; auto. Qed.

  Lemma sem_update_Istore :
    forall A rs args m v f ps ctx addr a0 chunk m' v',
      Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr rs ## args = Some a0 ->
      Mem.storev chunk m a0 v' = Some m' ->
      sem_value ctx v v' ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_mem ctx
        (seq_app (seq_app (pred_ret (Estore v chunk addr))
          (merge (list_translation args f))) (f #r Mem)) m'.
  Proof. Admitted.
  (*   intros * EVAL MEM SEM. *)
  (*   exploit sem_pred_expr_list_translation; try eassumption. *)
  (*   intro H; inversion_clear H as [x [HS HV]]. *)
  (*   inversion SEM as [? ? ? ? ? ? REG PRED HMEM EXIT]; subst. *)
  (*   exploit sem_pred_expr_ident2; [eapply HMEM|]. *)
  (*   intros H; inversion_clear H as [x' [HS' HV']]. *)
  (*   eapply sem_pred_expr_seq_app; eauto. *)
  (*   { eapply sem_pred_expr_seq_app; eauto. *)
  (*     - eapply sem_pred_expr_merge; eauto. *)
  (*     - apply sem_pred_expr_pred_ret. *)
  (*     - constructor. *)
  (*   } *)
  (*   econstructor; eauto. *)
  (* Qed. *)

  Lemma sem_update_Iop_top:
    forall A f p p' f' rs m pr op res args p0 v state,
      Op.eval_operation (ctx_ge state) (ctx_sp state) op rs ## args m = Some v ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBop p0 op args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state (rs # res <- v) pr m, None).
    Proof.
      intros * EVAL_OP TRUTHY VALID SEM UPD EVAL_PRED.
      pose proof SEM as SEM2.
      inversion UPD as [PRUNE]. unfold Option.bind in PRUNE.
      destr. inversion_clear PRUNE.
      rename Heqo into PRUNE.
      inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
      cbn [is_ps] in *. constructor.
      + constructor; intro x. inversion_clear REG as [? ? ? REG']. specialize (REG' x).
        destruct f as [fr fp fe]. cbn [forest_preds set_forest] in *.
        destruct (peq x res); subst.
        * rewrite forest_reg_gss in *. rewrite Regmap.gss in *.
          eapply sem_pred_expr_prune_predicated; eauto.
          eapply sem_pred_expr_app_predicated; [| |eauto].
          replace fp with (forest_preds {| forest_regs := fr; forest_preds := fp; forest_exit := fe |}) by auto.
          eapply sem_update_Iop; eauto. cbn in *.
          eapply eval_operation_valid_pointer; eauto.
          inversion_clear SEM2 as [? ? ? ? ? ? REG2 PRED2 MEM2 EXIT2].
          inversion_clear PRED2; eauto.
          cbn -[eval_predf]. rewrite eval_predf_Pand.
          rewrite EVAL_PRED. rewrite truthy_dflt; auto.
        * rewrite forest_reg_gso. rewrite Regmap.gso; auto.
          unfold not in *; intros. apply n0. inv H; auto.
      + constructor; intros. inv PRED. rewrite forest_reg_pred. auto.
      + rewrite forest_reg_gso; auto; discriminate.
      + auto.
  Qed.

  Lemma sem_update_Iload_top:
    forall A f p p' f' rs m pr res args p0 v state addr a chunk,
      Op.eval_addressing (ctx_ge state) (ctx_sp state) addr rs ## args = Some a ->
      Mem.loadv chunk m a = Some v ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBload p0 chunk addr args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state (rs # res <- v) pr m, None).
    Proof.
      intros * EVAL_OP LOAD TRUTHY VALID SEM UPD EVAL_PRED.
      pose proof SEM as SEM2.
      inversion UPD as [PRUNE]. unfold Option.bind in PRUNE. destr.
      inversion_clear PRUNE.
      rename Heqo into PRUNE.
      inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
      cbn [is_ps] in *. constructor.
      + constructor; intro x. inversion_clear REG as [? ? ? REG']. specialize (REG' x).
        destruct f as [fr fp fe]. cbn [forest_preds set_forest] in *.
        destruct (peq x res); subst.
        * rewrite forest_reg_gss in *. rewrite Regmap.gss in *.
          eapply sem_pred_expr_prune_predicated; eauto.
          eapply sem_pred_expr_app_predicated; [| |eauto].
          replace fp with (forest_preds {| forest_regs := fr; forest_preds := fp; forest_exit := fe |}) by auto.
          eapply sem_update_Iload; eauto.
          inversion_clear PRED; eauto.
          cbn -[eval_predf]. rewrite eval_predf_Pand.
          rewrite EVAL_PRED. rewrite truthy_dflt; auto.
        * rewrite forest_reg_gso. rewrite Regmap.gso; auto.
          unfold not in *; intros. apply n0. inv H; auto.
      + constructor; intros. inv PRED. rewrite forest_reg_pred. auto.
      + rewrite forest_reg_gso; auto; discriminate.
      + auto.
  Qed.

  Lemma sem_update_Istore_top:
    forall A f p p' f' rs m pr res args p0 state addr a chunk m',
      Op.eval_addressing (ctx_ge state) (ctx_sp state) addr rs ## args = Some a ->
      Mem.storev chunk m a rs !! res = Some m' ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBstore p0 chunk addr args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state rs pr m', None).
  Proof.
    intros * EVAL_OP STORE TRUTHY VALID SEM UPD EVAL_PRED.
    pose proof SEM as SEM2.
    inversion UPD as [PRUNE]. unfold Option.bind in PRUNE. destr.
    inversion_clear PRUNE.
    rename Heqo into PRUNE.
    inversion_clear SEM as [? ? ? ? ? ? REG PRED MEM EXIT].
    cbn [is_ps] in *. constructor.
    + constructor; intros. inv REG. rewrite forest_reg_gso; eauto. discriminate.
    + constructor; intros. inv PRED. rewrite forest_reg_pred. auto.
    + destruct f as [fr fp fm]; cbn -[seq_app] in *.
      rewrite forest_reg_gss.
      exploit sem_pred_expr_ident2; [exact MEM|]; intro HSEM_;
        inversion_clear HSEM_ as [x [HSEM1 HSEM2]].
      eapply sem_pred_expr_prune_predicated; eauto.
      eapply sem_pred_expr_app_predicated.
      eapply sem_pred_expr_seq_app_val; [solve [eauto]| |].
      eapply sem_pred_expr_seq_app. admit.
      eapply sem_pred_expr_flap2.
      eapply sem_pred_expr_seq_app. admit.
      eapply sem_pred_expr_pred_ret.
    + auto.
  Admitted.

  Lemma sem_update_instr :
    forall f i' i'' a sp p i p' f',
      step_instr ge sp (Iexec i') a (Iexec i'') ->
      valid_mem (is_mem i) (is_mem i') ->
      sem (mk_ctx i sp ge) f (i', None) ->
      update (p, f) a = Some (p', f') ->
      eval_predf (is_ps i') p = true ->
      sem (mk_ctx i sp ge) f' (i'', None).
  Proof.
    inversion 1; subst; clear H; intros VALID SEM UPD EVAL_PRED; pose proof SEM as SEM2.
    - inv UPD; auto.
    - eauto using sem_update_Iop_top.
    - eauto using sem_update_Iload_top.
    - eauto using sem_update_Istore_top.
    - admit.
    - admit.
  Admitted.

  Lemma Pand_true_left :
    forall ps a b,
      eval_predf ps a = false ->
      eval_predf ps (a ∧ b) = false.
  Proof.
    intros.
    rewrite eval_predf_Pand. now rewrite H.
  Qed.

  Lemma Pand_true_right :
    forall ps a b,
      eval_predf ps b = false ->
      eval_predf ps (a ∧ b) = false.
  Proof.
    intros.
    rewrite eval_predf_Pand. rewrite H.
    eauto with bool.
  Qed.

  Lemma eval_predf_simplify :
    forall ps x,
      eval_predf ps (simplify x) = eval_predf ps x.
  Proof. Admitted.

  Lemma sem_update_instr_term :
    forall f i' i'' sp i cf p p' p'' f',
      sem (mk_ctx i sp ge) f (i', None) ->
      step_instr ge sp (Iexec i') (RBexit p cf) (Iterm i'' cf) ->
      update (p', f) (RBexit p cf) = Some (p'', f') ->
      eval_predf (is_ps i') p' = true ->
      sem (mk_ctx i sp ge) f' (i'', Some cf)
           /\ eval_predf (is_ps i') p'' = false.
  Proof.
    intros. inv H0. simpl in *.
    unfold Option.bind in *. destruct_match; try discriminate.
    apply truthy_dflt in H6. inv H1.
    assert (eval_predf (Gible.is_ps i'') (¬ dfltp p) = false).
    { rewrite eval_predf_negate. now rewrite negb_false_iff. }
    apply Pand_true_left with (b := p') in H0.
    rewrite <- eval_predf_simplify in H0. split; auto.
    unfold "<-e". destruct i''.
    inv H. constructor; auto. admit. admit. simplify.
  Admitted.

  Lemma step_instr_lessdef_term :
    forall sp a i i' ti cf,
      step_instr ge sp (Iexec i) a (Iterm i' cf) ->
      state_lessdef i ti ->
      exists ti', step_instr ge sp (Iexec ti) a (Iterm ti' cf) /\ state_lessdef i' ti'.
  Proof. Admitted.

  Lemma combined_falsy :
    forall i o1 o,
      falsy i o1 ->
      falsy i (combine_pred o o1).
  Proof.
    inversion 1; subst; crush. destruct o; simplify.
    constructor. rewrite eval_predf_Pand. rewrite H0. crush.
    constructor. auto.
  Qed.

  Lemma state_lessdef_sem :
    forall i sp f i' ti cf,
      sem (mk_ctx i sp ge) f (i', cf) ->
      state_lessdef i ti ->
      exists ti', sem (mk_ctx ti sp ge) f (ti', cf) /\ state_lessdef i' ti'.
  Proof. Admitted.

  (* #[local] Opaque update. *)

  Lemma mfold_left_update_Some :
    forall xs x v,
      mfold_left update xs x = Some v ->
      exists y, x = Some y.
  Proof. Admitted.

  Lemma step_instr_term_exists :
    forall A B ge sp v x v2 cf,
      @step_instr A B ge sp (Iexec v) x (Iterm v2 cf) ->
      exists p, x = RBexit p cf.
  Proof using. inversion 1; eauto. Qed.

  Lemma abstr_fold_falsy :
    forall A i sp ge f i' cf p f' ilist p',
      @sem A (mk_ctx i sp ge) f (i', cf) ->
      mfold_left update ilist (Some (p, f)) = Some (p', f') ->
      eval_predf (is_ps i') p = false ->
      sem (mk_ctx i sp ge) f' (i', cf).
  Proof. Admitted.

  Lemma eval_predf_update_true :
    forall i i' curr_p next_p f f_next instr sp,
      update (curr_p, f) instr = Some (next_p, f_next) ->
      step_instr ge sp (Iexec i) instr (Iexec i') ->
      eval_predf (is_ps i) curr_p = true ->
      eval_predf (is_ps i') next_p = true.
  Proof.
    intros * UPD STEP EVAL. destruct instr; cbn [update] in UPD;
      try solve [unfold Option.bind in *; try destr; inv UPD; inv STEP; auto].
    - unfold Option.bind in *. destr. inv UPD. inv STEP; auto. cbn [is_ps] in *.
      admit.
    - unfold Option.bind in *. destr. inv UPD. inv STEP. inv H3. admit.
  Admitted. (* This only needs the addition of the property that any setpreds will not contain the
  predicate in the name. *)

  Lemma eval_predf_lessdef :
    forall p a b,
      state_lessdef a b ->
      eval_predf (is_ps a) p = eval_predf (is_ps b) p.
  Proof using.
    induction p; crush.
    - inv H. simpl. unfold eval_predf. simpl.
      repeat destr. inv Heqp0. rewrite H1. auto.
    - rewrite !eval_predf_Pand.
      erewrite IHp1 by eassumption.
      now erewrite IHp2 by eassumption.
    - rewrite !eval_predf_Por.
      erewrite IHp1 by eassumption.
      now erewrite IHp2 by eassumption.
  Qed.

  Lemma abstr_fold_correct :
    forall sp x i i' i'' cf f p f' curr_p,
      SeqBB.step ge sp (Iexec i') x (Iterm i'' cf) ->
      sem (mk_ctx i sp ge) f (i', None) ->
      eval_predf (is_ps i') curr_p = true ->
      mfold_left update x (Some (curr_p, f)) = Some (p, f') ->
      forall ti,
        state_lessdef i ti ->
        exists ti', sem (mk_ctx ti sp ge) f' (ti', Some cf)
               /\ state_lessdef i'' ti'.
  Proof.
    induction x as [| x xs IHx ]; intros; cbn -[update] in *; inv H; cbn [fst snd] in *.
    - (* inductive case *)
      exploit mfold_left_update_Some; eauto; intros Hexists;
        inversion Hexists as [[curr_p_inter f_inter] EXEQ]; clear Hexists.
        exploit eval_predf_update_true; eauto; intros EVALTRUE.
      rewrite EXEQ in H2. eapply IHx in H2; eauto; cbn [fst snd] in *.
      eapply sem_update_instr; eauto.
    - (* terminal case *)
      exploit mfold_left_update_Some; eauto; intros Hexists;
        inversion Hexists as [[curr_p_inter f_inter] EXEQ]; clear Hexists. rewrite EXEQ in H2.
      exploit state_lessdef_sem; eauto; intros H; inversion H as [v [Hi LESSDEF]]; clear H.
      exploit step_instr_lessdef_term; eauto; intros H; inversion H as [v2 [Hi2 LESSDEF2]]; clear H.
      exploit step_instr_term_exists; eauto; inversion 1 as [? ?]; subst; clear H.
      erewrite eval_predf_lessdef in H1 by eassumption.
      exploit sem_update_instr_term; eauto; intros [A B].
      exists v2. split. inv Hi2.
      eapply abstr_fold_falsy; try eassumption. auto.
  Qed.

  Lemma sem_regset_empty :
    forall A ctx, @sem_regset A ctx empty (ctx_rs ctx).
  Proof using.
    intros; constructor; intros.
    constructor; auto. constructor.
    constructor.
  Qed.

  Lemma sem_predset_empty :
    forall A ctx, @sem_predset A ctx empty (ctx_ps ctx).
  Proof using.
    intros; constructor; intros.
    constructor; auto. constructor.
  Qed.

  Lemma sem_empty :
    forall A ctx, @sem A ctx empty (ctx_is ctx, None).
  Proof using.
    intros. destruct ctx. destruct ctx_is.
    constructor; try solve [constructor; constructor; crush].
    eapply sem_regset_empty.
    eapply sem_predset_empty.
  Qed.

  Lemma abstr_sequence_correct :
    forall sp x i i'' cf x',
      SeqBB.step ge sp (Iexec i) x (Iterm i'' cf) ->
      abstract_sequence x = Some x' ->
      forall ti,
        state_lessdef i ti ->
        exists ti', sem (mk_ctx ti sp ge) x' (ti', Some cf)
               /\ state_lessdef i'' ti'.
  Proof.
    unfold abstract_sequence. intros. unfold Option.map in H0.
    destruct_match; try easy.
    destruct p; simplify.
    eapply abstr_fold_correct; eauto.
    simplify. eapply sem_empty. auto.
  Qed.

  Lemma abstr_check_correct :
    forall sp i i' a b cf ti,
      check a b = true ->
      sem (mk_ctx i sp ge) a (i', cf) ->
      state_lessdef i ti ->
      exists ti', sem (mk_ctx ti sp ge) b (ti', cf)
             /\ state_lessdef i' ti'.
  Proof. Admitted.

  Lemma abstr_seq_reverse_correct :
    forall sp x i i' ti cf x',
      abstract_sequence x = Some x' ->
      sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
      state_lessdef i ti ->
     exists ti', SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf)
             /\ state_lessdef i' ti'.
  Proof. Admitted.

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
    exploit abstr_check_correct; eauto. apply state_lessdef_refl. simplify.
    exploit abstr_seq_reverse_correct; eauto. apply state_lessdef_refl. simplify.
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
  Proof. Admitted.

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
