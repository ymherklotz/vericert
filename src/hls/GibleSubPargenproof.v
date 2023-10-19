(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.micromega.Lia.

Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require compcert.backend.Registers.
Require Import compcert.common.Linking.
Require Import compcert.common.Memory.
Require compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import vericert.common.IntegerExtra.
Require Import vericert.common.Vericertlib.
Require Import vericert.common.ZExtra.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.GibleSubPar.
Require Import vericert.hls.GibleSubPargen.
Require Import vericert.hls.Predicate.
Require Import vericert.common.Errormonad.
Import ErrorMonad.
Import ErrorMonadExtra.

Require Import Lia.

  Inductive match_stackframe : GiblePar.stackframe -> GibleSubPar.stackframe -> Prop :=
  | match_stackframe_init : forall r f tf sp n rs ps
    (TF: transl_function f = OK tf),
    match_stackframe (GiblePar.Stackframe r f sp n rs ps) 
                     (Stackframe r tf sp n rs ps).

  Variant match_states : GiblePar.state -> GibleSubPar.state -> Prop :=
    | match_state :
      forall stk stk' f tf sp pc rs m ps
        (HSTACK: Forall2 match_stackframe stk stk')
        (TF: transl_function f = OK tf),
        match_states (GiblePar.State stk f sp pc rs ps m)
                     (State stk' tf sp pc rs ps m)
    | match_callstate :
      forall cs cs' f tf args m
        (TF: transl_fundef f = OK tf)
        (STK: Forall2 match_stackframe cs cs'),
        match_states (GiblePar.Callstate cs f args m) (Callstate cs' tf args m)
    | match_returnstate :
      forall cs cs' v m
        (STK: Forall2 match_stackframe cs cs'),
        match_states (GiblePar.Returnstate cs v m) (Returnstate cs' v m).

  Definition match_prog (p: GiblePar.program) (tp: GibleSubPar.program) :=
    Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Section CORRECTNESS.

  Context (prog : GiblePar.program).
  Context (tprog : GibleSubPar.program).

  Let ge : GiblePar.genv := Globalenvs.Genv.globalenv prog.
  Let tge : GibleSubPar.genv := Globalenvs.Genv.globalenv tprog.

  Context (TRANSL : match_prog prog tprog).

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof using TRANSL. intros; eapply (Genv.senv_transf_partial TRANSL). Qed.
  #[local] Hint Resolve senv_preserved : rtlbg.

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
  Proof (Genv.find_funct_ptr_transf_partial TRANSL).

  Lemma sig_transl_function:
    forall (f: GiblePar.fundef) (tf: GibleSubPar.fundef),
      transl_fundef f = OK tf ->
      GibleSubPar.funsig tf = GiblePar.funsig f.
  Proof using.
    unfold transl_fundef. unfold transf_partial_fundef.
    intros. destruct_match. unfold Errors.bind in *. destruct_match; try discriminate.
    inv H. cbn. unfold transl_function in Heqr; unfold bind in *.
    repeat (destruct_match; try discriminate). inv Heqr. auto.
    inv H; auto.
  Qed.

  Lemma stacksize_equal: 
    forall f f0,
      transl_function f = OK f0 ->
      f0.(fn_stacksize) = f.(GiblePar.fn_stacksize).
  Proof.
    unfold transl_function, bind; intros. destruct_match; [|discriminate].
    inv H. auto.
  Qed.

  Lemma entrypoint_equal: 
    forall f f0,
      transl_function f = OK f0 ->
      f0.(fn_entrypoint) = f.(GiblePar.fn_entrypoint).
  Proof.
    unfold transl_function, bind; intros. destruct_match; [|discriminate].
    inv H. auto.
  Qed.

  Lemma params_equal: 
    forall f f0,
      transl_function f = OK f0 ->
      f0.(fn_params) = f.(GiblePar.fn_params).
  Proof.
    unfold transl_function, bind; intros. destruct_match; [|discriminate].
    inv H. auto.
  Qed.

  Lemma mfold_left_error:
    forall A B f l m, @mfold_left A B f l (Error m) = Error m.
  Proof. now induction l. Qed.

  Lemma mfold_left_cons:
    forall A B f a l x y, 
      @mfold_left A B f (a :: l) x = OK y ->
      exists x' y', @mfold_left A B f l (OK y') = OK y /\ f x' a = OK y' /\ x = OK x'.
  Proof.
    intros.
    destruct x; [|now rewrite mfold_left_error in H].
    cbn in H.
    replace (fold_left (fun (a : mon A) (b : B) => bind (fun a' : A => f a' b) a) l (f a0 a) = OK y) with
      (mfold_left f l (f a0 a) = OK y) in H by auto.
    destruct (f a0 a) eqn:?; [|now rewrite mfold_left_error in H].
    eauto.
  Qed.

  Lemma step_cf_instr_pc_ind :
    forall s f sp rs' pr' m' pc pc' cf t state,
      GiblePar.step_cf_instr ge (GiblePar.State s f sp pc rs' pr' m') cf t state ->
      GiblePar.step_cf_instr ge (GiblePar.State s f sp pc' rs' pr' m') cf t state.
  Proof. destruct cf; intros; inv H; econstructor; eauto. Qed.

  Lemma step_list_inter_not_term :
    forall A step_i sp i cf l i' cf',
      @step_list_inter A step_i sp (Iterm i cf) l (Iterm i' cf') ->
      i = i' /\ cf = cf'.
  Proof. now inversion 1. Qed.

  Lemma step_list_inter_not_exec :
    forall A step_i sp i cf l i',
      ~ @step_list_inter A step_i sp (Iterm i cf) l (Iexec i').
  Proof. now inversion 1. Qed.

  Lemma step_instr_seq_with_exit:
    forall sp a rs pr m rs' pr' m' pc,
      ParBB.step_instr_seq ge sp
        (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) a
        (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      SubParBB.step_instr_seq tge sp
        (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) (a ++ ((RBexit None (RBgoto pc) :: nil) :: nil))
        (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} (RBgoto pc)).
  Proof.
    induction a; intros.
    - cbn in *. inv H. eapply exec_RBterm. repeat econstructor.
    - cbn in *. inv H. destruct i1. destruct i. econstructor; eauto.
  Admitted.

  Lemma step_instr_seq_with_exit':
    forall sp a rs pr m rs' pr' m' pc cf,
      ParBB.step_instr_seq ge sp
        (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) a
        (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      SubParBB.step_instr_seq tge sp
        (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) (a ++ ((RBexit None (RBgoto pc) :: nil) :: nil))
        (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf).
  Proof.
    induction a; intros.
    - cbn in *. inv H. 
  Admitted.

  Lemma transl_spec_not_in':
    forall bb pc fresh code_start fresh' code_end pc' y,
      transl_block (fresh, code_start) (pc', bb) = OK (fresh', code_end) ->
      code_start ! pc = Some y ->
      code_end ! pc = Some y.
  Proof.
    induction bb; unfold transl_block; intros; cbn in *.
    - inv H; auto.
    - remember (
           match code_start ! pc' with
           | Some _ => Error (msg "GibleSubPargen: Overlapping blocks in translation")
           | None =>
               OK (fresh, (Pos.succ fresh, PTree.set pc' (a ++ (RBexit None (RBgoto fresh) :: nil) :: nil) code_start))
           end) as trans. setoid_rewrite <- Heqtrans in H.
      replace (fold_left
           (fun (a : mon (positive * (positive * code))) (b : SubParBB.t) =>
            bind (fun a' : positive * (positive * code) => transl_block' a' b) a) bb trans) with
            (mfold_left transl_block' bb trans) in H by auto.
      destruct trans; [|rewrite mfold_left_error in H; cbn in *; inversion H].
      repeat (destruct_match; try discriminate; []).
      inversion Heqtrans as []. rewrite H1 in H.
      exploit IHbb; eauto.
      destruct (peq pc pc').
      + subst. rewrite Heqo in H0. discriminate.
      + rewrite PTree.gso by auto; auto.
  Qed.

  Lemma transl_spec_not_in:
    forall l pc fresh code_start fresh' code_end y,
      mfold_left transl_block l (OK (fresh, code_start)) = OK (fresh', code_end) ->
      code_start ! pc = Some y -> 
      code_end ! pc = Some y.
  Proof.
    induction l; cbn in *; [inversion 1; auto|].
    intros * HFOLD HNOT.
    remember (transl_block (fresh, code_start) a) as tblock.
    replace (fold_left
            (fun (a : mon (positive * code)) (b : positive * ParBB.t) =>
             bind (fun a' : positive * code => transl_block a' b) a) l tblock) with
             (mfold_left transl_block l tblock) in HFOLD by auto.
    destruct tblock; [|rewrite mfold_left_error in HFOLD; discriminate].
    symmetry in Heqtblock. destruct p, a. eapply transl_spec_not_in' in Heqtblock; eauto.
  Qed.

  Lemma transl_plus_correct:
    forall f sp bb pc pc' fresh fresh' code code' s rs pr m rs' pr' m' cf t state0 s' tf,
      ParBB.step (Smallstep.globalenv (GiblePar.semantics prog)) sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |})
           bb (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      GiblePar.step_cf_instr (Smallstep.globalenv (GiblePar.semantics prog)) (GiblePar.State s f sp pc rs' pr' m') cf t
           state0 ->
      mfold_left transl_block' bb (OK (pc, (fresh, code))) = OK (pc', (fresh', code')) ->
      (forall x y, code' ! x = Some y -> (fn_code tf) ! x = Some y) ->
      match_states (GiblePar.State s f sp pc rs pr m) (State s' tf sp pc rs pr m) ->
      exists s2' : Smallstep.state (semantics tprog),
        Smallstep.plus (Smallstep.step (semantics tprog)) (Smallstep.globalenv (semantics tprog)) (State s' tf sp pc rs pr m) t s2' /\
        match_states state0 s2'.
  Proof. 
    induction bb; [inversion 1|].
    intros. exploit mfold_left_cons; eauto. 
    intros (ytemp & (pc_mid & (fresh_mid & code_mid)) & HFOLD & HTRANSL & HOK).
    inv HOK. inv H.
    - destruct state'. exploit IHbb. eauto. eapply step_cf_instr_pc_ind; eauto.
      eauto. eauto. inv H3. econstructor; eauto.
      intros (s2' & HPLUS & HMATCH).
      unfold transl_block' in HTRANSL. repeat (destruct_match; try discriminate; []).
      inv HTRANSL.
      exploit transl_spec_not_in'. unfold transl_block. 
      rewrite HFOLD. cbn. eauto. rewrite PTree.gss. eauto.
      intros. eapply H2 in H.
      econstructor. split.
      eapply Smallstep.plus_left'. econstructor. eauto. cbn. eapply step_instr_seq_with_exit.
      eauto. econstructor. eauto. eauto. eauto.
    - cbn in HTRANSL. repeat (destruct_match; try discriminate). inv HTRANSL.
      exploit transl_spec_not_in'. unfold transl_block. rewrite HFOLD. cbn. eauto.
      rewrite PTree.gss. eauto. intros. eapply H2 in H.
      econstructor. split.
      + apply Smallstep.plus_one. econstructor; eauto.
        eapply step_instr_seq_with_exit'; eauto.
  Admitted.

  Lemma transl_spec':
    forall l fresh fresh' code_start code_end pc bb,
      mfold_left transl_block l (OK (fresh, code_start)) = OK (fresh', code_end) ->
      In (pc, bb) l ->
      exists (code0 code' : code) (fresh fresh' : positive),
        transl_block (fresh, code0) (pc, bb) = OK (fresh', code') /\
        (forall (x : positive) (y : SubParBB.t), code' ! x = Some y -> code_end ! x = Some y).
  Proof.
    induction l; [inversion 2|].
    intros * HFOLD HIN.
    cbn in *.
    remember (transl_block (fresh, code_start) a) as HTRANSL.
    replace (fold_left
            (fun (a : mon (positive * code)) (b : positive * ParBB.t) =>
             bind (fun a' : positive * code => transl_block a' b) a) l HTRANSL) with
      (mfold_left transl_block l HTRANSL) in HFOLD by auto.
    destruct HTRANSL;
      [|erewrite mfold_left_error in HFOLD; discriminate].
    destruct p as [fresh_mid code_mid].
    symmetry in HeqHTRANSL.
    inv HIN; eauto.
    exists code_start, code_mid, fresh, fresh_mid; split; auto.
    intros. eapply transl_spec_not_in; eauto.
  Qed.

  Lemma transl_spec:
    forall f tf pc bb,
      transl_function f = OK tf ->
      f.(GiblePar.fn_code) ! pc = Some bb ->
      exists code code' fresh fresh',
        transl_block (fresh, code) (pc, bb) = OK (fresh', code')
        /\ (forall x y, code' ! x = Some y -> tf.(fn_code) ! x = Some y).
  Proof.
    unfold transl_function, bind; intros. destruct_match; [|discriminate].
    inversion_clear H as []. cbn -[transl_block] in *.
    destruct p.
    eapply transl_spec'; eauto.
    now apply PTree.elements_correct.
  Qed.

  Lemma transl_plus_step:
    forall (s1 : Smallstep.state (GiblePar.semantics prog)) (t : Events.trace)
      (s1' : Smallstep.state (GiblePar.semantics prog)),
      Smallstep.step (GiblePar.semantics prog) (Smallstep.globalenv (GiblePar.semantics prog)) s1 t s1' ->
      forall s2 : Smallstep.state (semantics tprog),
      match_states s1 s2 ->
      exists s2' : Smallstep.state (semantics tprog),
        Smallstep.plus (Smallstep.step (semantics tprog)) (Smallstep.globalenv (semantics tprog)) s2 t s2' /\
        match_states s1' s2'.
  Proof.
    induction 1.
    - inversion 1; subst. exploit transl_spec; eauto. 
      intros (code0 & code' & fresh & fresh' & HFOLD & HIN).
      unfold transl_block in HFOLD.
      unfold map in HFOLD. repeat (destruct_match; try discriminate). destruct p. destruct p0.
      inv HFOLD. eapply transl_plus_correct; eauto.
    - eauto. intros * HMATCH. inv HMATCH. cbn in TF. unfold Errors.bind in TF. destruct_match; [|discriminate].
        inv TF. econstructor. split.
      + apply Smallstep.plus_one. econstructor. erewrite stacksize_equal by eauto. eauto.
      + erewrite params_equal by eauto. erewrite entrypoint_equal by eauto. now econstructor.
    - cbn in *. intros * HMATCH. inv HMATCH. cbn in *. inv TF.
      econstructor. split.
      + apply Smallstep.plus_one. econstructor. eapply Events.external_call_symbols_preserved; eauto.
        eapply senv_preserved.
      + now constructor.
    - cbn in *. intros * HMATCH. inv HMATCH. inv STK. inv H1.
      econstructor; split.
      + apply Smallstep.plus_one. econstructor.
      + now constructor.
  Qed.

  Lemma transl_initial_states:
    forall S,
      GiblePar.initial_state prog S ->
      exists R, GibleSubPar.initial_state tprog R /\ match_states S R.
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
      match_states S R -> GiblePar.final_state S r -> GibleSubPar.final_state R r.
  Proof. intros. inv H0. inv H. inv STK. constructor. Qed.

  Theorem transl_program_correct:
    Smallstep.forward_simulation (GiblePar.semantics prog) (semantics tprog).
  Proof using TRANSL.
    eapply Smallstep.forward_simulation_plus.
    - apply senv_preserved.
    - apply transl_initial_states.
    - apply transl_final_states.
    - apply transl_plus_step.
  Qed.

End CORRECTNESS.
