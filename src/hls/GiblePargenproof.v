(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2023 Yann Herklotz <yann@yannherklotz.com>
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

Module Import OptionExtra := MonadExtra(Option).

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

Correctness of translation from RTLBlock to the abstract interpretation
language.
|*)

Definition is_regs i := match i with mk_instr_state rs _ _ => rs end.
Definition is_mem i := match i with mk_instr_state _ _ m => m end.
Definition is_ps i := match i with mk_instr_state _ p _ => p end.

Definition evaluable {A B C} (sem: ctx -> B -> C -> Prop) (ctx: @ctx A) p := exists b, sem ctx p b.

Definition p_evaluable {A} := @evaluable A _ _ sem_pexpr.

Definition evaluable_expr {A} := @evaluable A _ _ sem_pred.

Definition all_evaluable {A B} (ctx: @ctx A) f_p (l: predicated B) :=
  forall p y, NE.In (p, y) l -> p_evaluable ctx (from_pred_op f_p p).

Definition all_evaluable2 {A B C} (ctx: @ctx A) (sem: Abstr.ctx -> B -> C -> Prop) (l: predicated B) :=
  forall p y, NE.In (p, y) l -> evaluable sem ctx y.

Definition pred_forest_evaluable {A} (ctx: @ctx A) (ps: PTree.t pred_pexpr) :=
  forall i p, ps ! i = Some p -> p_evaluable ctx p.

Definition forest_evaluable {A} (ctx: @ctx A) (f: forest) :=
  pred_forest_evaluable ctx f.(forest_preds).

(* Lemma all_evaluable2_NEmap : *)
(*   forall G A (ctx: @ctx G) (f: (pred_op * A) -> (pred_op * pred_expression)) (x: predicated A), *)
(*     all_evaluable2 ctx sem_pred (NE.map f x). *)
(* Proof. *)
(*   induction x. *)

Lemma all_evaluable_cons :
  forall A B pr ctx b a,
    all_evaluable ctx pr (NE.cons a b) ->
    @all_evaluable A B ctx pr b.
Proof.
  unfold all_evaluable; intros.
  enough (NE.In (p, y) (NE.cons a b)); eauto.
  constructor; tauto.
Qed.

Lemma all_evaluable2_cons :
  forall A B C sem ctx b a,
    all_evaluable2 ctx sem (NE.cons a b) ->
    @all_evaluable2 A B C ctx sem b.
Proof.
  unfold all_evaluable2; intros.
  enough (NE.In (p, y) (NE.cons a b)); eauto.
  constructor; tauto.
Qed.

Lemma all_evaluable_cons2 :
  forall A B pr ctx b a p,
    @all_evaluable A B ctx pr (NE.cons (p, a) b) ->
    p_evaluable ctx (from_pred_op pr p).
Proof.
  unfold all_evaluable; intros.
  eapply H. constructor; eauto.
Qed.

Lemma all_evaluable2_cons2 :
  forall A B C sem ctx b a p,
    @all_evaluable2 A B C ctx sem (NE.cons (p, a) b) ->
    evaluable sem ctx a.
Proof.
  unfold all_evaluable; intros.
  eapply H. constructor; eauto.
Qed.

Lemma all_evaluable_cons3 :
  forall A B pr ctx b p a,
    all_evaluable ctx pr b ->
    p_evaluable ctx (from_pred_op pr p) ->
    @all_evaluable A B ctx pr (NE.cons (p, a) b).
Proof.
  unfold all_evaluable; intros. inv H1. inv H3. inv H1. auto.
  eauto.
Qed.

Lemma all_evaluable_singleton :
  forall A B pr ctx b p,
    @all_evaluable A B ctx pr (NE.singleton (p, b)) ->
    p_evaluable ctx (from_pred_op pr p).
Proof.
  unfold all_evaluable; intros. eapply H. constructor.
Qed.

Lemma get_forest_p_evaluable :
  forall A (ctx: @ctx A) f r,
    forest_evaluable ctx f ->
    p_evaluable ctx (f #p r).
Proof.
  intros. unfold "#p", get_forest_p'.
  destruct_match. unfold forest_evaluable in *.
  unfold pred_forest_evaluable in *. eauto.
  unfold p_evaluable, evaluable. eexists.
  constructor. constructor.
Qed.

Lemma set_forest_p_evaluable :
  forall A (ctx: @ctx A) f r p,
    forest_evaluable ctx f ->
    p_evaluable ctx p ->
    forest_evaluable ctx (f #p r <- p).
Proof.
  unfold forest_evaluable, pred_forest_evaluable; intros.
  destruct (peq i r); subst.
  - rewrite forest_pred_gss2 in H1. now inv H1.
  - rewrite forest_pred_gso2 in H1 by auto; eauto.
Qed.

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

Lemma check_dest_dec i r :
  {check_dest i r = true} + {check_dest i r = false}.
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

Lemma check_dest_l_dec i r :
  {check_dest_l i r = true} + {check_dest_l i r = false}.
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
    forall A B C sem f_p ctx a b v,
      sem_pred_expr f_p sem ctx a v ->
      @sem_pred_expr A B C f_p sem ctx (NE.app a b) v.
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

  Lemma sem_pred_expr_NEapp3 :
    forall A B C sem f_p ctx (a b: predicated B) v,
      (forall x, NE.In x a -> sem_pexpr ctx (from_pred_op f_p (fst x)) false) ->
      sem_pred_expr f_p sem ctx b v ->
      @sem_pred_expr A B C f_p sem ctx (NE.app a b) v.
  Proof.
    induction a; crush.
    - assert (IN: NE.In a (NE.singleton a)) by constructor.
      specialize (H _ IN). destruct a.
      eapply sem_pred_expr_cons_false; eauto.
    - assert (NE.In a (NE.cons a a0)) by (constructor; tauto).
      apply H in H1.
      destruct a. cbn [fst] in *.
      eapply sem_pred_expr_cons_false; auto.
      eapply IHa; eauto.
      intros. eapply H. constructor; tauto.
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
    forall A B C pr ctx (a: predicated C) (b: predicated B) a' b'
      (EVALUABLE: all_evaluable ctx pr b),
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
      + apply all_evaluable_cons in EVALUABLE. inv H0. inv H6. cbn. constructor; cbn.
        replace true with (true && true) by auto.
        constructor; auto. constructor.
        eapply sem_pred_expr_cons_false; eauto. cbn.
        replace false with (true && false) by auto.
        constructor; auto.
    - unfold predicated_prod. simplify.
      rewrite NEapp_NEmap.
      inv H. eapply sem_pred_expr_NEapp.
      { induction b; crush.
        destruct a. inv H0. constructor.
        replace true with (true && true) by auto.
        eapply sem_pexpr_Pand; auto. inv H6. inv H7.
        constructor.

        eapply all_evaluable_cons in EVALUABLE.
        destruct a. inv H0. constructor.
        replace true with (true && true) by auto.
        constructor; auto. inv H8. inv H6. constructor.

        specialize (IHb EVALUABLE H8). eapply sem_pred_expr_cons_false; auto.
        replace false with (true && false) by auto.
        constructor; auto.
      }
      { exploit IHa. eauto. eauto. apply H0. intros.
        unfold predicated_prod in *.
        eapply sem_pred_expr_NEapp3; eauto; [].
        clear H. clear H0.
        induction b.
        { intros. inv H. destruct a. simpl. apply all_evaluable_singleton in EVALUABLE.
          inversion_clear EVALUABLE.
          replace false with (false && x) by auto. constructor; auto. }
        { intros. inv H. inv H1. destruct a. simpl.
          eapply all_evaluable_cons2 in EVALUABLE.
          inversion_clear EVALUABLE.
          replace false with (false && x) by auto. constructor; auto.
          eapply all_evaluable_cons in EVALUABLE.
          eauto.
        }
      }
  Qed.

  Lemma sem_pred_expr_seq_app :
    forall G A B (f: predicated (A -> B))
        ps (ctx: @ctx G) l f_ l_
      (EVALUABLE: all_evaluable ctx ps l),
      sem_pred_expr ps sem_ident ctx l l_ ->
      sem_pred_expr ps sem_ident ctx f f_ ->
      sem_pred_expr ps sem_ident ctx (seq_app f l) (f_ l_).
  Proof.
    unfold seq_app; intros.
    remember (fun x : (A -> B) * A => fst x (snd x)) as app.
    replace (f_ l_) with (app (f_, l_)) by (rewrite Heqapp; auto).
    eapply sem_pred_expr_predicated_map. eapply sem_pred_expr_predicated_prod; auto.
  Qed.

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
        ps ctx l v f_ l_
      (EVALUABLE: all_evaluable ctx ps l),
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
    forall A (ctx: @ctx A) pr s s' a e
        (ALLEVAL: all_evaluable ctx pr s),
      sem_pred_expr pr sem_ident ctx s s' ->
      sem_pred_expr pr sem_ident ctx a e ->
      sem_pred_expr pr sem_ident ctx (cons_pred_expr a s) (Econs e s').
  Proof.
    intros. unfold cons_pred_expr.
    replace (Econs e s') with ((uncurry Econs) (e, s')) by auto.
    eapply sem_pred_expr_predicated_map.
    eapply sem_pred_expr_predicated_prod; eauto.
  Qed.


  Lemma evaluable_singleton :
    forall A B ctx fp r,
      @all_evaluable A B ctx fp (NE.singleton (T, r)).
  Proof.
    unfold all_evaluable, evaluable; intros.
    inv H. simpl. exists true. constructor.
  Qed.

Lemma evaluable_negate :
  forall G (ctx: @ctx G) p,
    p_evaluable ctx p ->
    p_evaluable ctx (¬ p).
Proof.
  induction p; intros.
  - destruct p. cbn in *. inv H.
    exists (negb x). constructor. inv H0.
    rewrite negb_if. now rewrite negb_involutive.
  - repeat econstructor.
  - repeat econstructor.
  - cbn. exploit IHp1. inv H. inv H0. econstructor. eauto.
    intros. exploit IHp2. inv H. inv H1. econstructor. eauto.
    intros.  inv H0. inv H1. econstructor. econstructor; eauto.
  - cbn. exploit IHp1. inv H. inv H0. econstructor. eauto.
    intros. exploit IHp2. inv H. inv H1. econstructor. eauto.
    intros.  inv H0. inv H1. econstructor. econstructor; eauto.
Qed.

Lemma predicated_evaluable :
  forall G (ctx: @ctx G) ps (p: pred_op),
    pred_forest_evaluable ctx ps ->
    p_evaluable ctx (from_pred_op ps p).
Proof.
  unfold pred_forest_evaluable; intros. induction p; intros; cbn.
  - repeat destruct_match; subst; unfold get_forest_p'.
    destruct_match. eapply H; eauto. econstructor. constructor. constructor.
    eapply evaluable_negate.
    destruct_match. eapply H; eauto. econstructor. constructor. constructor.
  - repeat econstructor.
  - repeat econstructor.
  - inv IHp1. inv IHp2. econstructor. constructor; eauto.
  - inv IHp1. inv IHp2. econstructor. constructor; eauto.
Qed.

Lemma predicated_evaluable_all :
  forall A G (ctx: @ctx G) ps (p: predicated A),
    pred_forest_evaluable ctx ps ->
    all_evaluable ctx ps p.
Proof.
  unfold all_evaluable; intros.
  eapply predicated_evaluable. eauto.
Qed.

Lemma predicated_evaluable_all_list :
  forall A G (ctx: @ctx G) ps (p: list (predicated A)),
    pred_forest_evaluable ctx ps ->
    Forall (all_evaluable ctx ps) p.
Proof.
  induction p.
  - intros. constructor.
  - intros. constructor; eauto. apply predicated_evaluable_all; auto.
Qed.

Hint Resolve evaluable_singleton : core.
Hint Resolve predicated_evaluable : core.
Hint Resolve predicated_evaluable_all : core.
Hint Resolve predicated_evaluable_all_list : core.

  Lemma sem_pred_expr_fold_right :
    forall A pr ctx s a a' s'
        (PRED: pred_forest_evaluable ctx pr),
      sem_pred_expr pr sem_ident ctx s s' ->
      Forall2 (sem_pred_expr pr sem_ident ctx) (NE.to_list a) (of_elist a') ->
      @sem_pred_expr A _ _ pr sem_ident ctx (NE.fold_right cons_pred_expr s a) (Eapp a' s').
  Proof.
    induction a; crush. inv H0. inv H5. destruct a'; crush. destruct a'; crush.
    inv H3. eapply sem_pred_expr_cons_pred_expr; eauto.
    inv H0. destruct a'; crush. inv H3.
    eapply sem_pred_expr_cons_pred_expr; eauto.
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

  Lemma sem_pred_expr_merge :
    forall G (ctx: @Abstr.ctx G) ps l args,
      Forall2 (sem_pred_expr ps sem_ident ctx) args l ->
      sem_pred_expr ps sem_ident ctx (merge args) (to_elist l).
  Proof.
    induction l; intros.
    - inv H. cbn; repeat constructor.
    - inv H. cbn. unfold merge. Admitted.

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
    forall A ctx f rs ps m args
      (EVALF: forest_evaluable ctx f),
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_val_list ctx
        (merge (list_translation args f)) (rs ## args).
  Proof.
    induction args; crush. cbn. constructor; constructor.
    unfold merge. specialize (IHargs EVALF H).
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
      eapply sem_pred_expr_predicated_prod; [eapply evaluable_singleton|eassumption|repeat constructor].
      repeat constructor; auto.
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
      apply sem_pred_expr_fold_right; eauto.
      repeat constructor.
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

Lemma evaluable_and_true :
  forall G (ctx: @ctx G) ps p,
    p_evaluable ctx (from_pred_op ps p) ->
    p_evaluable ctx (from_pred_op ps (p ∧ T)).
Proof.
  intros. unfold evaluable in *. inv H. exists (x && true). cbn.
  constructor; auto. constructor.
Qed.

Lemma NEin_map :
  forall A B p y (f: A -> B) a,
    NE.In (p, y) (predicated_map f a) ->
    exists x, NE.In (p, x) a /\ y = f x.
Proof.
  induction a; intros.
  - inv H. destruct a. econstructor. split; eauto. constructor.
  - inv H. inv H1. inv H. destruct a. cbn in *. econstructor; econstructor; eauto.
    constructor; tauto.
    specialize (IHa H). inv IHa. inv H0.
    econstructor; econstructor; eauto. constructor; tauto.
Qed.

Lemma NEin_map2 :
  forall A B (f: A -> B) a p y,
    NE.In (p, y) a ->
    NE.In (p, f y) (predicated_map f a).
Proof.
  induction a; crush.
  inv H. constructor.
  inv H. inv H1.
  - constructor; auto.
  - constructor; eauto.
Qed.

Lemma all_evaluable_predicated_map :
  forall A B G (ctx: @ctx G) ps (f: A -> B) p,
    all_evaluable ctx ps p ->
    all_evaluable ctx ps (predicated_map f p).
Proof.
  induction p.
  - unfold all_evaluable; intros.
    exploit NEin_map; eauto; intros. inv H1. inv H2.
    eapply H; eauto.
  - intros. cbn.
    eapply all_evaluable_cons3. eapply IHp. eapply all_evaluable_cons; eauto.
    cbn. destruct a. cbn in *. eapply all_evaluable_cons2; eauto.
Qed.

Lemma all_evaluable_predicated_map2 :
  forall A B G (ctx: @ctx G) ps (f: A -> B) p,
    all_evaluable ctx ps (predicated_map f p) ->
    all_evaluable ctx ps p.
Proof.
  induction p.
  - unfold all_evaluable in *; intros.
    eapply H. eapply NEin_map2; eauto.
  - intros. cbn. destruct a.
    cbn in H. pose proof H. eapply all_evaluable_cons in H; eauto.
    eapply all_evaluable_cons2 in H0; eauto.
    unfold all_evaluable. specialize (IHp H).
    unfold all_evaluable in IHp.
    intros. inv H1. inv H3. inv H1; eauto.
    specialize (IHp _ _ H1). eauto.
Qed.

Lemma all_evaluable_map_and :
  forall A B G (ctx: @ctx G) ps (a: NE.non_empty ((pred_op * A) * (pred_op * B))),
    (forall p1 x p2 y,
       NE.In ((p1, x), (p2, y)) a ->
            p_evaluable ctx (from_pred_op ps p1)
            /\ p_evaluable ctx (from_pred_op ps p2)) ->
    all_evaluable ctx ps (NE.map (fun x => match x with ((a, b), (c, d)) => (Pand a c, (b, d)) end) a).
Proof.
  induction a.
  - intros. cbn. repeat destruct_match. inv Heqp.
    unfold all_evaluable; intros. inv H0.
    unfold evaluable.
    exploit H. constructor.
    intros [Ha Hb]. inv Ha. inv Hb.
    exists (x && x0). constructor; auto.
  - intros. unfold all_evaluable; cbn; intros. inv H0. inv H2.
    + repeat destruct_match. inv Heqp0. inv H0.
      specialize (H p2 a1 p3 b ltac:(constructor; eauto)).
      inv H. inv H0. inv H1. exists (x && x0).
      constructor; eauto.
    + eapply IHa; intros. eapply H. econstructor. right. eauto.
      eauto.
Qed.

Lemma all_evaluable_map_add :
  forall A B G (ctx: @ctx G) ps (a: pred_op * A) (b: predicated B) p1 x p2 y,
    p_evaluable ctx (from_pred_op ps (fst a)) ->
    all_evaluable ctx ps b ->
    NE.In (p1, x, (p2, y)) (NE.map (fun x : pred_op * B => (a, x)) b) ->
    p_evaluable ctx (from_pred_op ps p1) /\ p_evaluable ctx (from_pred_op ps p2).
Proof.
  induction b; intros.
  - cbn in *. inv H1. unfold all_evaluable in *. specialize (H0 _ _ ltac:(constructor)).
    auto.
  - cbn in *. inv H1. inv H3.
    + inv H1. unfold all_evaluable in H0. specialize (H0 _ _ ltac:(constructor; eauto)); auto.
    + eapply all_evaluable_cons in H0. specialize (IHb _ _ _ _ H H0 H1). auto.
Qed.

Lemma NEin_NEapp5 :
  forall A (a: A) x y,
    NE.In a (NE.app x y) ->
    NE.In a x \/ NE.In a y.
Proof.
  induction x; crush.
  - inv H. inv H1. left. constructor. tauto.
  - inv H. inv H1. left. constructor; tauto.
    exploit IHx; eauto; intros. inv H0.
    left. constructor; tauto. tauto.
Qed.

Lemma all_evaluable_non_empty_prod :
  forall A B G (ctx: @ctx G) ps p1 x p2 y (a: predicated A) (b: predicated B),
    all_evaluable ctx ps a ->
    all_evaluable ctx ps b ->
    NE.In ((p1, x), (p2, y)) (NE.non_empty_prod a b) ->
    p_evaluable ctx (from_pred_op ps p1)
    /\ p_evaluable ctx (from_pred_op ps p2).
Proof.
  induction a; intros.
  - cbn in *. eapply all_evaluable_map_add; eauto. destruct a; cbn in *. eapply H; constructor.
  - cbn in *. eapply NEin_NEapp5 in H1. inv H1. eapply all_evaluable_map_add; eauto.
    destruct a; cbn in *. eapply all_evaluable_cons2; eauto.
    eapply all_evaluable_cons in H. eauto.
Qed.

Lemma all_evaluable_predicated_prod :
  forall A B G (ctx: @ctx G) ps (a: predicated A) (b: predicated B),
    all_evaluable ctx ps a ->
    all_evaluable ctx ps b ->
    all_evaluable ctx ps (predicated_prod a b).
Proof.
  intros. unfold all_evaluable; intros.
  unfold predicated_prod in *. exploit all_evaluable_map_and.
  2: { eauto. }
  intros. 2: { eauto. }
Admitted. (* Requires simple lemma to prove, but this lemma is not needed. *)

Lemma cons_pred_expr_evaluable :
  forall G (ctx: @ctx G) ps a b,
    all_evaluable ctx ps a ->
    all_evaluable ctx ps b ->
    all_evaluable ctx ps (cons_pred_expr a b).
Proof.
  unfold cons_pred_expr; intros.
  apply all_evaluable_predicated_map.
  now apply all_evaluable_predicated_prod.
Qed.

Lemma fold_right_all_evaluable :
  forall G (ctx: @ctx G) ps n,
    Forall (all_evaluable ctx ps) (NE.to_list n) ->
    all_evaluable ctx ps (NE.fold_right cons_pred_expr (NE.singleton (T, Enil)) n).
Proof.
  induction n; cbn in *; intros.
  - unfold cons_pred_expr. eapply all_evaluable_predicated_map. eapply all_evaluable_predicated_prod.
    inv H. auto. unfold all_evaluable; intros. inv H0. exists true. constructor.
  - inv H. specialize (IHn H3). now eapply cons_pred_expr_evaluable.
Qed.

Lemma merge_all_evaluable :
  forall G (ctx: @ctx G) ps,
    pred_forest_evaluable ctx ps ->
    forall f args,
      all_evaluable ctx ps (merge (list_translation args f)).
Proof.
  intros. eapply predicated_evaluable_all. eauto.
Qed.

(*|
Here we can finally assume that everything in the forest is evaluable, which
will allow us to prove that translating the list of register accesses will also
all be evaluable.
|*)

  Lemma sem_update_Iop :
    forall A op rs args m v f ps ctx
      (EVALF: forest_evaluable ctx f),
      Op.eval_operation (ctx_ge ctx) (ctx_sp ctx) op rs ## args (is_mem (ctx_is ctx)) = Some v ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_value ctx
        (seq_app (pred_ret (Eop op)) (merge (list_translation args f))) v.
  Proof.
    intros * EVALF EVAL SEM.
    exploit sem_pred_expr_list_translation; try eassumption.
    intro H; inversion_clear H as [x [HS HV]].
    eapply sem_pred_expr_seq_app_val.
    - eapply merge_all_evaluable; eauto.
    - cbn in *; eapply sem_pred_expr_merge; eauto.
    - apply sem_pred_expr_pred_ret.
    - econstructor; [eauto|]; auto.
  Qed.

  Lemma sem_update_Iload :
    forall A rs args m v f ps ctx addr a0 chunk
      (EVALF: forest_evaluable ctx f),
      Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr rs ## args = Some a0 ->
      Mem.loadv chunk m a0 = Some v ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_value ctx
        (seq_app (seq_app (pred_ret (Eload chunk addr)) (merge (list_translation args f))) (f #r Mem)) v.
  Proof.
    intros * EVALF EVAL MEM SEM.
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

  #[global] Program Instance valid_mem_Equivalence : Equivalence valid_mem.
  Next Obligation. unfold valid_mem; auto. Qed. (* Reflexivity *)
  Next Obligation. unfold valid_mem; auto. Qed. (* Symmetry *)
  Next Obligation. unfold valid_mem; eauto. Qed. (* Transitity *)

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
    forall A rs args m v f ps ctx addr a0 chunk m' v'
      (EVALF: forest_evaluable ctx f),
      Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr rs ## args = Some a0 ->
      Mem.storev chunk m a0 v' = Some m' ->
      sem_value ctx v v' ->
      sem ctx f ((mk_instr_state rs ps m), None) ->
      @sem_pred_expr A _ _ (forest_preds f) sem_mem ctx
        (seq_app (seq_app (pred_ret (Estore v chunk addr))
          (merge (list_translation args f))) (f #r Mem)) m'.
  Proof.
    intros * EVALF EVAL STOREV SEMVAL SEM.
    exploit sem_merge_list; try eassumption.
    intro MERGE. exploit sem_pred_expr_ident2; eauto.
    intro TMP; inversion_clear TMP as [x [HS HV]].
    inversion_clear SEM as [? ? ? ? ? ? REG PRED HMEM EXIT].
    exploit sem_pred_expr_ident2; [eapply HMEM|].
    intros TMP; inversion_clear TMP as [x' [HS' HV']].
    eapply sem_pred_expr_ident.
    eapply sem_pred_expr_seq_app; eauto.
    eapply sem_pred_expr_seq_app; eauto.
    eapply sem_pred_expr_pred_ret.
    econstructor; eauto.
  Qed.

  Lemma sem_update_Iop_top:
    forall A f p p' f' rs m pr op res args p0 v state
      (EVALF: forest_evaluable state f),
      Op.eval_operation (ctx_ge state) (ctx_sp state) op rs ## args m = Some v ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBop p0 op args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state (rs # res <- v) pr m, None).
    Proof.
      intros * EVALF EVAL_OP TRUTHY VALID SEM UPD EVAL_PRED.
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
    forall A f p p' f' rs m pr res args p0 v state addr a chunk
      (EVALF: forest_evaluable state f),
      Op.eval_addressing (ctx_ge state) (ctx_sp state) addr rs ## args = Some a ->
      Mem.loadv chunk m a = Some v ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBload p0 chunk addr args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state (rs # res <- v) pr m, None).
    Proof.
      intros * EVALF EVAL_OP LOAD TRUTHY VALID SEM UPD EVAL_PRED.
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

  Lemma exists_sem_pred :
    forall A B C (ctx: @ctx A) s pr r v,
      @sem_pred_expr A B C pr s ctx r v ->
      exists r',
        NE.In r' r /\ s ctx (snd r') v.
  Proof.
    induction r; crush.
    - inv H. econstructor. split. constructor. auto.
    - inv H.
      + econstructor. split. constructor. left; auto. auto.
      + exploit IHr; eauto. intros HH. inversion_clear HH as [x HH']. inv HH'.
        econstructor. split. constructor. right. eauto. auto.
  Qed.

  Lemma sem_update_Istore_top:
    forall A f p p' f' rs m pr res args p0 state addr a chunk m'
      (EVALF: forest_evaluable state f),
      Op.eval_addressing (ctx_ge state) (ctx_sp state) addr rs ## args = Some a ->
      Mem.storev chunk m a rs !! res = Some m' ->
      truthy pr p0 ->
      valid_mem (is_mem (ctx_is state)) m ->
      sem state f ((mk_instr_state rs pr m), None) ->
      update (p, f) (RBstore p0 chunk addr args res) = Some (p', f') ->
      eval_predf pr p = true ->
      @sem A state f' (mk_instr_state rs pr m', None).
  Proof.
    intros * EVALF EVAL_OP STORE TRUTHY VALID SEM UPD EVAL_PRED.
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
      inv REG. specialize (H res).
      pose proof H as HRES.
      eapply sem_pred_expr_ident2 in HRES.
      inversion_clear HRES as [r2 [HRES1 HRES2]].
      apply exists_sem_pred in H. inversion_clear H as [r' [HNE HVAL]].
      exploit sem_merge_list. eauto. eapply SEM2. instantiate (2 := args). intro HSPE. eapply sem_pred_expr_ident2 in HSPE.
      inversion_clear HSPE as [l_ [HSPE1 HSPE2]].
      eapply sem_pred_expr_prune_predicated; eauto.
      eapply sem_pred_expr_app_predicated.
      eapply sem_pred_expr_seq_app_val; [solve [eapply predicated_evaluable_all; eauto]|solve [eauto]| |].
      eapply sem_pred_expr_seq_app; [solve [eapply predicated_evaluable_all; eauto]|solve [eauto]|].
      eapply sem_pred_expr_flap2.
      eapply sem_pred_expr_seq_app; [solve [eapply predicated_evaluable_all; eauto]|solve [eauto]|].
      eapply sem_pred_expr_pred_ret. econstructor. eauto. 3: { eauto. }
      eauto. auto. eauto. inv PRED. eauto.
      rewrite eval_predf_Pand. rewrite EVAL_PRED.
      rewrite truthy_dflt. auto. auto.
    + auto.
  Qed.

  Lemma sem_update_instr :
    forall f i' i'' a sp p i p' f'
      (EVALF: forest_evaluable (mk_ctx i sp ge) f),
      step_instr ge sp (Iexec i') a (Iexec i'') ->
      valid_mem (is_mem i) (is_mem i') ->
      sem (mk_ctx i sp ge) f (i', None) ->
      update (p, f) a = Some (p', f') ->
      eval_predf (is_ps i') p = true ->
      sem (mk_ctx i sp ge) f' (i'', None).
  Proof.
    inversion 2; subst; clear H; intros VALID SEM UPD EVAL_PRED; pose proof SEM as SEM2.
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
  Proof.
    induction xs; intros.
    { cbn in *. inv H. eauto. }
    cbn in *. unfold Option.bind in *. exploit IHxs; eauto.
    intros. simplify. destruct x; crush.
    eauto.
  Qed.

  Lemma step_instr_term_exists :
    forall A B ge sp v x v2 cf,
      @step_instr A B ge sp (Iexec v) x (Iterm v2 cf) ->
      exists p, x = RBexit p cf.
  Proof using. inversion 1; eauto. Qed.

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

  Lemma forest_evaluable_regset :
    forall A f (ctx: @ctx A) n x,
      forest_evaluable ctx f ->
      forest_evaluable ctx f #r x <- n.
  Proof.
    unfold forest_evaluable, pred_forest_evaluable; intros.
    eapply H. eauto.
  Qed.

  Lemma evaluable_impl :
    forall A (ctx: @ctx A) a b,
      p_evaluable ctx a ->
      p_evaluable ctx b ->
      p_evaluable ctx (a → b).
  Proof.
    unfold evaluable.
    inversion_clear 1 as [b1 SEM1].
    inversion_clear 1 as [b2 SEM2].
    econstructor. constructor;
    eauto using sem_pexpr_negate.
  Qed.

  Lemma parts_evaluable :
    forall A (ctx: @ctx A) b p0,
      evaluable sem_pred ctx p0 ->
      evaluable sem_pexpr ctx (Plit (b, p0)).
  Proof.
    intros. unfold evaluable in *. inv H.
    destruct b. do 2 econstructor. eauto.
    exists (negb x). constructor. rewrite negb_involutive. auto.
  Qed.

  Lemma p_evaluable_Pand :
    forall A (ctx: @ctx A) a b,
      p_evaluable ctx a ->
      p_evaluable ctx b ->
      p_evaluable ctx (a ∧ b).
  Proof.
    intros. inv H. inv H0.
    econstructor. econstructor; eauto.
  Qed.

  Lemma from_predicated_evaluable :
    forall A (ctx: @ctx A) f b a,
      pred_forest_evaluable ctx f ->
      all_evaluable2 ctx sem_pred a ->
      p_evaluable ctx (from_predicated b f a).
  Proof.
    induction a.
    cbn. destruct_match; intros.
    eapply evaluable_impl.
    eauto using predicated_evaluable.
    unfold all_evaluable2 in H0. unfold p_evaluable.
    eapply parts_evaluable. eapply H0. econstructor.

    intros. cbn. destruct_match.
    eapply p_evaluable_Pand.
    eapply all_evaluable2_cons2 in H0.
    eapply evaluable_impl.
    eauto using predicated_evaluable.
    unfold all_evaluable2 in H0. unfold p_evaluable.
    eapply parts_evaluable. eapply H0.
    eapply all_evaluable2_cons in H0. eauto.
  Qed.

  Lemma all_evaluable_pred_ret :
    forall A B G (ctx: @ctx G) (sem: @Abstr.ctx G -> A -> B -> Prop)
        (a: A) (b: B),
      sem ctx a b ->
      all_evaluable2 ctx sem (pred_ret a).
  Admitted.

  Lemma eval_predf_seq_app_evaluable :
    forall A B G (ctx: @ctx G) (sem: @Abstr.ctx G -> A -> B -> Prop) (l: predicated A) a,
      all_evaluable2 ctx sem l ->
      all_evaluable2 ctx sem (seq_app a l).
  Proof.
    intros. unfold seq_app. Admitted.

  Lemma eval_predf_update_evaluable :
    forall A (ctx: @ctx A) curr_p next_p f f_next instr,
      update (curr_p, f) instr = Some (next_p, f_next) ->
      forest_evaluable ctx f ->
      p_evaluable ctx (from_pred_op (forest_preds f) curr_p) ->
      forest_evaluable ctx f_next.
  Proof.
    destruct instr; intros; cbn -[seq_app pred_ret merge list_translation] in *.
    - inversion H; subst; auto.
    - unfold Option.bind in *. destruct_match; try easy.
      inversion_clear H. eapply forest_evaluable_regset; auto.
    - unfold Option.bind in *. destruct_match; try easy.
      inversion_clear H. eapply forest_evaluable_regset; auto.
    - unfold Option.bind in *. destruct_match; try easy.
      inversion_clear H. eapply forest_evaluable_regset; auto.
    - unfold Option.bind in *. destruct_match; crush.
      unfold forest_evaluable, pred_forest_evaluable.
      intros. cbn -[seq_app pred_ret merge list_translation] in *.
      destruct (peq i p); subst; [rewrite PTree.gss in H; inversion_clear H
        | rewrite PTree.gso in H by auto; eapply H0; eassumption].
      eapply evaluable_impl.
      eapply p_evaluable_Pand; auto.
      eapply from_predicated_evaluable; auto.
      admit.
    - unfold Option.bind in *. destruct_match; try easy.
      inversion_clear H. eapply forest_evaluable_regset; auto.
  Admitted.

  Lemma sem_update_valid_mem :
    forall i i' i'' curr_p next_p f f_next instr sp,
      update (curr_p, f) instr = Some (next_p, f_next) ->
      step_instr ge sp (Iexec i') instr (Iexec i'') ->
      sem (mk_ctx i sp ge) f (i', None) ->
      valid_mem (is_mem i') (is_mem i'').
  Proof. Admitted.

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

  Lemma abstr_fold_evaluable :
    forall A (ctx: @ctx A) x f f' curr_p p,
      mfold_left update x (Some (curr_p, f)) = Some (p, f') ->
      forest_evaluable ctx f ->
      forest_evaluable ctx f'.
  Proof.
    induction x as [| x xs IHx ].
    - cbn in *; inversion 1; auto.
    - intros.
      replace (mfold_left update (x :: xs) (Some (curr_p, f)) = Some (p, f'))
      with (mfold_left update xs (update (curr_p, f) x) = Some (p, f')) in H by auto.
      exploit mfold_left_update_Some. eassumption.
      inversion_clear 1 as [y SOME]. destruct y. rewrite SOME in H.
      eapply IHx; [eassumption|].
      eauto using eval_predf_update_evaluable.
  Qed.

(*|
``abstr_fold_falsy``: This lemma states that when we are at the end of an
execution, the values in the register map do not continue to change.  This
should mean that we can show the forest is still evaluable if it was evaluable
at any point at the end of the execution.
|*)

  Lemma abstr_fold_falsy :
    forall A i sp ge f res p f' ilist p',
      @sem A (mk_ctx i sp ge) f res ->
      forest_evaluable (mk_ctx i sp ge) f ->
      mfold_left update ilist (Some (p, f)) = Some (p', f') ->
      eval_predf (is_ps (fst res)) p = false ->
      sem (mk_ctx i sp ge) f' res /\ forest_evaluable (mk_ctx i sp ge) f'.
  Proof. Admitted.

  (* Lemma abstr_fold_falsy_evaluable : *)
  (*   forall sp x i i' i'' cf f p f' curr_p *)
  (*       (FEVAL: forest_evaluable (mk_ctx i sp ge) f) *)
  (*       (VALID: valid_mem (is_mem i) (is_mem i')), *)
  (*     SeqBB.step ge sp (Iexec i') x (Iterm i'' cf) -> *)
  (*     sem (mk_ctx i sp ge) f (i', Some cf) -> *)
  (*     mfold_left update x (Some (curr_p, f)) = Some (p, f') -> *)
  (*     eval_predf (is_ps i') curr_p = false -> *)

  Lemma forest_evaluable_lessdef :
    forall A (ge: Genv.t A unit) sp st st' f,
      forest_evaluable (mk_ctx st sp ge) f ->
      state_lessdef st st' ->
      forest_evaluable (mk_ctx st' sp ge) f.
  Proof. Admitted. (* easy *)

  Lemma abstr_fold_correct :
    forall sp x i i' i'' cf f p f' curr_p
        (FEVAL: forest_evaluable (mk_ctx i sp ge) f)
        (VALID: valid_mem (is_mem i) (is_mem i')),
      SeqBB.step ge sp (Iexec i') x (Iterm i'' cf) ->
      sem (mk_ctx i sp ge) f (i', None) ->
      eval_predf (is_ps i') curr_p = true ->
      mfold_left update x (Some (curr_p, f)) = Some (p, f') ->
      forall ti,
        state_lessdef i ti ->
        exists ti', sem (mk_ctx ti sp ge) f' (ti', Some cf)
               /\ state_lessdef i'' ti'
               /\ forest_evaluable (mk_ctx i sp ge) f'
               /\ valid_mem (is_mem i) (is_mem i'').
  Proof.
    induction x as [| x xs IHx ]; intros; cbn -[update] in *; inv H; cbn [fst snd] in *.
    - (* inductive case *)
      exploit mfold_left_update_Some; eauto; intros Hexists;
        inversion Hexists as [[curr_p_inter f_inter] EXEQ]; clear Hexists.
        exploit eval_predf_update_true; (* TODO: Needs an extra property about setpred (global, static) *)
        eauto; intros EVALTRUE.
      rewrite EXEQ in H2. eapply IHx in H2; cbn [fst snd] in *.
      eauto.
      eapply eval_predf_update_evaluable; eauto. (* TODO *)
      transitivity (is_mem i'); auto.
      eapply sem_update_valid_mem; eauto. (* TODO *)
      eauto.
      eapply sem_update_instr; eauto. eauto. eauto. (* MAIN TODO *)
    - (* terminal case *)
      exploit mfold_left_update_Some; eauto; intros Hexists;
        inversion Hexists as [[curr_p_inter f_inter] EXEQ]; clear Hexists. rewrite EXEQ in H2.
      exploit state_lessdef_sem; (* TODO *)
      eauto; intros H; inversion H as [v [Hi LESSDEF]]; clear H.
      exploit step_instr_lessdef_term; (* TODO *)
      eauto; intros H; inversion H as [v2 [Hi2 LESSDEF2]]; clear H.
      exploit step_instr_term_exists; eauto; inversion 1 as [? ?]; subst; clear H.
      erewrite eval_predf_lessdef in H1 by eassumption.
      exploit sem_update_instr_term; (* TODO *)
      eauto; intros [A B].
      exists v2.
      exploit abstr_fold_falsy. (* TODO *)
      apply A.
      eapply forest_evaluable_lessdef; (* TODO *)
      try eassumption.
      eapply eval_predf_update_evaluable. (* TODO *)
      eassumption. eassumption. auto.
      eassumption. cbn. inversion Hi2; subst. auto. intros.
      inversion_clear H as [Hsem Hforest]. split. auto. split. auto.
      split. eapply forest_evaluable_lessdef; (* TODO *)
      try eassumption.
      symmetry. auto. inversion H7; subst. auto.
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
    destruct p as [p TMP]; simplify.
    exploit abstr_fold_correct; eauto; crush.
    { apply sem_empty. }
    exists x0. auto.
  Qed.

  Lemma abstr_check_correct :
    forall sp i i' a b cf ti,
      check a b = true ->
      sem (mk_ctx i sp ge) a (i', cf) ->
      state_lessdef i ti ->
      exists ti', sem (mk_ctx ti sp ge) b (ti', cf)
             /\ state_lessdef i' ti'.
  Proof.

(*|
Proof Sketch:

Two abstract states can be equivalent, without it being obvious that they can
actually both be executed assuming one can be executed.  One will therefore have
to add a few more assumptions to makes it possible to execute the other.
|*)

  Admitted.

  Lemma abstr_seq_reverse_correct :
    forall sp x i i' ti cf x',
      abstract_sequence x = Some x' ->
      sem (mk_ctx i sp ge) x' (i', (Some cf)) ->
      state_lessdef i ti ->
     exists ti', SeqBB.step ge sp (Iexec ti) x (Iterm ti' cf)
             /\ state_lessdef i' ti'.
  Proof.

(*|
Proof Sketch:

We do an induction over the list of instructions ``x``.  This is trivial for the
empty case and then for the inductive case we know that there exists an
execution that matches the abstract execution, so we need to know that adding
another instructions to it will still mean that the execution will result in the
same value.

Arithmetic operations will be a problem because we will have to show that these
can be executed.  However, this should mostly be a problem in the abstract state
comparison, because there two abstract states can be equal without one being
evaluable.
|*)

  Admitted.

(*|
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
