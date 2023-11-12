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

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.common.Smallstep.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.DHTL.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.
Require Import vericert.hls.DMemorygen.
Require Import vericert.hls.ClockMemory.

Local Open Scope positive.
Local Open Scope assocmap.

Inductive match_assocmaps : assocmap -> assocmap -> Prop :=
  match_assocmap: forall rs rs',
    (forall r, rs!r = rs'!r) ->
    match_assocmaps rs rs'.

Inductive match_reg_assocs : reg_associations -> reg_associations -> Prop :=
  match_reg_association:
    forall rab rab' ran ran',
      match_assocmaps rab rab' ->
      match_assocmaps ran ran' ->
      match_reg_assocs (mkassociations rab ran) (mkassociations rab' ran').

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr'
      (MATCH_ASSOC: match_assocmaps asr asr'),
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r (transf_module m) pc asr' asa).

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa'
           (ASSOC: match_assocmaps asr asr')
           (ASSOC': match_arrs asa asa')
           (STACK: Forall2 match_stackframes res res'),
      match_states (State res m st asr asa)
                   (State res' (transf_module m) st asr' asa')
| match_returnstate :
    forall res res' i
           (STACKS: Forall2 match_stackframes res res'),
      match_states (Returnstate res i) (Returnstate res' i)
| match_initial_call :
    forall m,
      match_states (Callstate nil m nil)
                   (Callstate nil (transf_module m) nil).

Lemma match_assocmaps_refl:
  forall a, match_assocmaps a a.
Proof.
  intros; constructor; auto.
Qed.

Lemma match_assocmaps_symm:
  forall a b, match_assocmaps a b -> match_assocmaps b a.
Proof.
  inversion 1; constructor; congruence.
Qed.

Lemma match_assocmaps_trans:
  forall a b c, match_assocmaps a b -> match_assocmaps b c -> match_assocmaps a c.
Proof.
  inversion 1; inversion 1; constructor; congruence.
Qed.

Lemma match_reg_assocs_trans:
  forall a b c, match_reg_assocs a b -> match_reg_assocs b c -> match_reg_assocs a c.
Proof.
  inversion 1; inversion 1; constructor; subst;
  eapply match_assocmaps_trans; eauto.
Qed.

Lemma match_assocs_refl:
  forall a, match_reg_assocs a a.
Proof.
  intros; destruct a; constructor; subst; apply match_assocmaps_refl.
Qed.

Lemma match_reg_assocs_symm:
  forall a b, match_reg_assocs a b -> match_reg_assocs b a.
Proof.
  inversion 1; constructor; apply match_assocmaps_symm; auto.
Qed.

Definition match_prog (p: program) (tp: program) :=
  Linking.match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. unfold transf_program, match_prog.
  apply Linking.match_transform_program.
Qed.

Lemma match_assocmaps_inv :
  forall a b, match_assocmaps a b -> forall x, b ! x = a ! x.
Proof. inversion 1. auto. Qed.

Lemma match_assocmaps_inv_map :
  forall a b, match_assocmaps a b -> forall x n, b # (x, n) = a # (x, n).
Proof. 
  inversion 1; subst; intros.
  unfold find_assocmap, AssocMapExt.get_default.
  now rewrite H0.
Qed.

Lemma match_assocmaps_merge :
  forall asr' tasr',
    match_reg_assocs asr' tasr' ->
    match_assocmaps (Verilog.merge_regs (assoc_nonblocking asr') (assoc_blocking asr'))
                          (Verilog.merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr')).
Proof.
  inversion 1; subst.
  inv H0. inv H1. econstructor; intros; cbn.
  unfold merge_regs. unfold AssocMapExt.merge. rewrite !PTree.gcombine by auto.
  rewrite H2. now rewrite H0.
Qed.

Lemma match_assocmaps_merge2 :
  forall a ta b tb,
    match_assocmaps a ta ->
    match_assocmaps b tb ->
    match_assocmaps (Verilog.merge_regs a b) (Verilog.merge_regs ta tb).
Proof.
  inversion 1. inversion 1. subst.
  econstructor; intros. unfold merge_regs, AssocMapExt.merge.
  rewrite !PTree.gcombine by auto. rewrite H0. rewrite H4. auto.
Qed.

Lemma match_assocmaps_set :
  forall asr asr',
    match_assocmaps asr asr' ->
    forall r v, match_assocmaps (AssocMap.set r v asr) (AssocMap.set r v asr').
Proof.
  intros. econstructor; intros. destruct (peq r r0); subst.
  - rewrite !AssocMap.gss; auto.
  - inv H. rewrite !AssocMap.gso by auto. eauto.
Qed.

Lemma expr_runp_same :
  forall f rs1 ar1 c v,
    expr_runp f rs1 ar1 c v ->
    forall trs1,
      match_assocmaps rs1 trs1 ->
      expr_runp f trs1 ar1 c v.
Proof.
  induction 1; intros.
  - econstructor.
  - econstructor. erewrite match_assocmaps_inv_map; eauto.
  - exploit IHexpr_runp; eauto; intros. econstructor; eauto.
  - exploit IHexpr_runp1; eauto; exploit IHexpr_runp2; eauto; intros.
    econstructor; eauto.
  - exploit IHexpr_runp; eauto; intros. econstructor; eauto.
  - exploit IHexpr_runp1; eauto; exploit IHexpr_runp2; eauto; intros.
    econstructor; eauto.
  - exploit IHexpr_runp1; eauto; exploit IHexpr_runp2; eauto; intros.
    eapply erun_Vternary_false; eauto.
  - exploit IHexpr_runp; eauto; intros. econstructor; eauto.
    erewrite match_assocmaps_inv_map; eauto. rewrite H0. now rewrite H1.
Qed.

Lemma match_states_same :
  forall f rs1 ar1 c rs2 ar2,
    stmnt_runp f rs1 ar1 c rs2 ar2 ->
    forall trs1,
      match_reg_assocs rs1 trs1 ->
      exists trs2,
        stmnt_runp f trs1 ar1 c trs2 ar2
        /\ match_reg_assocs rs2 trs2.
Proof.
  induction 1.
  - econstructor; split; eauto; constructor.
  - intros. exploit IHstmnt_runp1; eauto; simplify. 
    exploit IHstmnt_runp2; eauto; simplify.
    econstructor; split.
    + econstructor; eauto.
    + auto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H2; subst; exploit expr_runp_same; eauto; intros.
    eexists; split; eauto; econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H2; subst; exploit expr_runp_same; eauto; intros.
    eexists; split; eauto; eapply stmnt_runp_Vcond_false; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H3. subst. exploit expr_runp_same; [eapply H| |]; eauto; intros.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    eexists; split; eauto. econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H3. subst. exploit expr_runp_same; [eapply H| |]; eauto; intros.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    eexists; split; eauto. eapply stmnt_runp_Vcase_match; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H1. subst. exploit expr_runp_same; [eapply H| |]; eauto; intros.
    eexists; split; eauto. eapply stmnt_runp_Vcase_default; eauto.
  - inv H; intros.
    inversion H. subst. exploit expr_runp_same; eauto; intros.
    econstructor; split; intros. econstructor; eauto. econstructor.
    econstructor; cbn; eauto.
    econstructor; intros.
    destruct (peq r r0); subst.
    + now rewrite !AssocMap.gss.
    + rewrite !AssocMap.gso by auto. inv H1; eauto.
  - inv H; intros.
    inversion H. subst. exploit expr_runp_same; eauto; intros.
    econstructor; split; intros. econstructor; eauto. econstructor.
    econstructor; cbn; eauto.
    econstructor; intros.
    destruct (peq r r0); subst.
    + now rewrite !AssocMap.gss.
    + rewrite !AssocMap.gso by auto. inv H2; eauto.
  - inv H; intros. inversion H; subst.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    exploit expr_runp_same; [eapply H6| |]; eauto; intros.
    eexists; split; eauto. econstructor; eauto. econstructor; eauto.
  - inv H; intros. inversion H; subst.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    exploit expr_runp_same; [eapply H6| |]; eauto; intros.
    eexists; split; eauto. econstructor; eauto. econstructor; eauto.
Qed.

Lemma exec_ram_same :
  forall rs1 ar1 c rs2 ar2,
    exec_ram rs1 ar1 c rs2 ar2 ->
    forall trs1,
      match_reg_assocs rs1 trs1 ->
      exists trs2,
        exec_ram trs1 ar1 c trs2 ar2
        /\ match_reg_assocs rs2 trs2.
Proof.
  induction 1; intros.
  - eexists; split; eauto.
    apply exec_ram_Some_idle. inv H0. cbn in *; setoid_rewrite match_assocmaps_inv_map; eauto.
  - inv H6; eexists; split; cbn in *.
    + eapply exec_ram_Some_write. eapply H. eauto. all: cbn in *.
      now erewrite match_assocmaps_inv_map by eauto.
      all: now erewrite match_assocmaps_inv by eauto.
    + unfold nonblock_reg; cbn. constructor; auto.
      now apply match_assocmaps_set.
  - inv H5; eexists; split; cbn in *.
    + eapply exec_ram_Some_read; eauto; cbn in *.
      now erewrite match_assocmaps_inv_map by eauto.
      all: now erewrite match_assocmaps_inv by eauto.
    + unfold nonblock_reg; cbn. constructor; auto.
      now repeat apply match_assocmaps_set.
  - eexists; split; cbn in *; eauto. econstructor.
Qed.

  Lemma expr_interchangeable:
    forall e r v a ar f v',
      check_excluded r e = true ->
      expr_runp f a ar e v ->
      expr_runp f (AssocMap.set r v' a) ar e v.
  Proof. 
    induction e; intros; cbn in *; simplify; try rewrite negb_true_iff in *;
    repeat match goal with | H: _ =? _ = false |- _ => apply Pos.eqb_neq in H end; inv H0; try solve [econstructor; eauto].
    - econstructor; now rewrite assocmap_gso by auto.
    - econstructor; eauto; now rewrite assocmap_gso by auto.
  Qed.

  Lemma expr_interchangeable2:
    forall e r v a ar f v',
      check_excluded r e = true ->
      expr_runp f (AssocMap.set r v' a) ar e v ->
      expr_runp f a ar e v.
  Proof. 
    induction e; intros; cbn in *; simplify; try rewrite negb_true_iff in *;
    repeat match goal with | H: _ =? _ = false |- _ => apply Pos.eqb_neq in H end; inv H0; try solve [econstructor; eauto].
    - econstructor; now rewrite assocmap_gso by auto.
    - econstructor; eauto; now rewrite assocmap_gso by auto.
  Qed.

  Lemma expr_interchangeable3:
    forall e r t asr iv v arr v',
      check_excluded r e = true ->
      expr_runp t asr (arr_assocmap_set r (valueToNat iv) v arr) e v' ->
      expr_runp t asr arr e v'.
  Proof.
    induction e; intros; cbn in *; simplify; try rewrite negb_true_iff in *;
    repeat match goal with | H: _ =? _ = false |- _ => apply Pos.eqb_neq in H end; inv H0; try solve [econstructor; eauto].
    econstructor; eauto. unfold arr_assocmap_lookup in *. unfold arr_assocmap_set in *.
    destruct (arr ! r0) eqn:?; auto. rewrite AssocMap.gso in H9 by auto. auto.
  Qed.

  Lemma transf_maps_correct:
    forall t asr asa s asr' asa',
      stmnt_runp t (mkassociations asr empty_assocmap) asa s asr' asa' ->
      (forall r e1 e0 r0 e3, s <> (Vseq (Vseq Vskip (Vblock (Vvari r e1) e0)) (Vblock (Vvar r0) e3))) ->
      forall tasr,
        match_reg_assocs (mkassociations asr empty_assocmap) (mkassociations tasr empty_assocmap) ->
        exists tasr', stmnt_runp t (mkassociations tasr empty_assocmap) asa (transf_maps s) tasr' asa'
                      /\ match_assocmaps (Verilog.merge_regs (assoc_nonblocking asr') (assoc_blocking asr'))
                      (Verilog.merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr')).
  Proof.
    intros * ? HNEQ **. destruct s; try solve [exploit match_states_same; eauto; simplify;
      exploit match_assocmaps_merge; eauto].
    cbn in *. 
    repeat (destruct_match; try solve [exploit match_states_same; eauto; simplify;
      exploit match_assocmaps_merge; eauto]).
    - simplify.
      inv H. inv H11. inv H10. inv H14; inv H10. inv H15; inv H10.
      inv H14.
      eexists; split. econstructor. econstructor. econstructor.
      2: { econstructor. econstructor. econstructor. unfold block_reg in *; cbn in *. eapply expr_interchangeable; eauto.
           eapply expr_runp_same; eauto. inv H0; auto. eauto. }
      unfold block_reg in *; cbn in *. eapply expr_interchangeable2; eauto.
      eapply expr_runp_same; eauto. eapply match_assocmaps_set; eauto.
      inv H0; auto.
      econstructor; intros. cbn.
      unfold merge_regs, AssocMapExt.merge. inv H0; subst; cbn.
      rewrite !PTree.gcombine by auto.
      rewrite negb_true_iff in *.
      apply Pos.eqb_neq in H4. apply Pos.eqb_neq in H2. apply Pos.eqb_neq in H5.
      destruct (peq r r2); subst.
      + rewrite !AssocMap.gss by auto. rewrite !AssocMap.gso by auto. auto.
      + rewrite !AssocMap.gso by auto.
        destruct (peq r r1); subst.
        ** rewrite !AssocMap.gss. rewrite !AssocMap.gso by auto. auto.
        ** rewrite !AssocMap.gso by auto. inv H8. rewrite H. auto.
    - subst. exfalso; eapply HNEQ; eauto.
  Qed.

  Lemma transf_maps_correct2:
    forall t asr asa s asr' asa',
      stmnt_runp t (mkassociations asr empty_assocmap) asa s asr' asa' ->
      (forall r e1 e0 r0 e3, s <> (Vseq (Vseq Vskip (Vblock (Vvari r e1) e0)) (Vblock (Vvar r0) e3))) ->
      forall tasr,
        match_reg_assocs (mkassociations asr empty_assocmap) (mkassociations tasr empty_assocmap) ->
        exists tasr', stmnt_runp t (mkassociations tasr empty_assocmap) asa (transf_maps s) tasr' asa'
                      /\ match_assocmaps (Verilog.merge_regs (assoc_nonblocking asr') (assoc_blocking asr'))
                      (Verilog.merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr')).
  Proof.

  Lemma transf_maps_correct2:
    forall t asr asa r e1 e0 r0 e3 asr' asa' st l,
      stmnt_runp t (mkassociations asr empty_assocmap) (mkassociations asa (empty_stack st l)) 
        (Vseq (Vseq Vskip (Vblock (Vvari r e1) e0)) (Vblock (Vvar r0) e3)) asr' asa' ->
      forall tasr,
        match_reg_assocs (mkassociations asr empty_assocmap) (mkassociations tasr empty_assocmap) ->
        exists tasr' tasa', stmnt_runp t (mkassociations tasr empty_assocmap) (mkassociations asa (empty_stack st l)) 
                        (transf_maps (Vseq (Vseq Vskip (Vblock (Vvari r e1) e0)) (Vblock (Vvar r0) e3))) tasr' tasa'
                      /\ match_assocmaps (Verilog.merge_regs (assoc_nonblocking asr') (assoc_blocking asr'))
                      (Verilog.merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr'))
                      /\ Verilog.merge_arrs (assoc_nonblocking tasa') (assoc_blocking tasa') 
                         = Verilog.merge_arrs (assoc_nonblocking asa') (assoc_blocking asa').
  Proof.
    intros; cbn in *. inv H0. clear H6.
    inv H. inv H6. inv H5. inv H9; inv H5. inv H10; inv H5. cbn in *. destruct_match; cbn in *;
    repeat (kill_bools; match goal with | H: _ /\ _ |- _ => inv H end).
    - rewrite negb_true_iff in *. apply Pos.eqb_neq in H0. do 2 eexists; split; [|split].
      + econstructor. econstructor. econstructor. cbn. eapply expr_interchangeable3; eauto.
        eapply expr_runp_same; eauto.
        eapply stmnt_runp_Vnonblock_arr. econstructor. 
        cbn. eapply expr_interchangeable; eauto. eapply expr_runp_same; eauto.
        cbn. eapply expr_interchangeable; eauto. eapply expr_runp_same; eauto.
      + cbn. eapply match_assocmaps_merge2; eauto. apply match_assocmaps_refl.
        now apply match_assocmaps_set.
      + cbn. unfold merge_arrs.

Section CORRECTNESS.

  Context (prog tprog: program).
  Context (TRANSL: match_prog prog tprog).

  Let ge : genv := Genv.globalenv prog.
  Let tge : genv := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.
  #[local] Hint Resolve symbols_preserved : mgen.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  #[local] Hint Resolve function_ptr_translated : mgen.

  Lemma functions_translated:
    forall (v: Values.val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transf_fundef f = tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  #[local] Hint Resolve functions_translated : mgen.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof (Genv.senv_transf TRANSL).
  #[local] Hint Resolve senv_preserved : mgen.

  Theorem transf_step_correct:
    forall (S1 : state) t S2,
      step ge S1 t S2 ->
      forall R1,
        match_states S1 R1 ->
        exists R2, step tge R1 t R2 /\ match_states S2 R2.
  Proof. 
    induction 1.
    - inversion 1; subst. exploit transf_maps_correct; eauto. econstructor. eauto.
      apply match_assocmaps_refl. intros ((btasr' & ntasr') & HSTMNT & HMATCH).
      exploit exec_ram_same; eauto. econstructor; eauto. apply match_assocmaps_refl.
      intros ((btrs2 & ntrs2) & HEXEC & HMATCH2).
      econstructor. split. econstructor; cbn.
      1-3: now erewrite match_assocmaps_inv by eauto.
      rewrite PTree.gmap1. rewrite H2. cbn. auto. eassumption.
      eassumption. eauto. eauto. eapply match_assocmaps_merge in HMATCH2.
      erewrite match_assocmaps_inv; eauto. eauto.
      econstructor; auto. eapply match_assocmaps_merge in HMATCH2. eauto.
    - inversion 1; subst. econstructor; split.
      apply step_finish; cbn. now erewrite match_assocmaps_inv by eauto.
      erewrite match_assocmaps_inv by eauto. eassumption.
      econstructor; auto.
    - inversion 1; subst; intros. econstructor; split.
      apply step_call. econstructor; auto. inv H.
      repeat apply match_assocmaps_set. cbn. 
      apply match_assocmaps_refl.
    - inversion 1; subst. inv STACKS. inv H0. destruct y.  
      eexists; split. eapply step_return. eauto. inv H2.
      constructor; auto. repeat apply match_assocmaps_set. auto.
  Qed.
  #[local] Hint Resolve transf_step_correct : mgen.

  Lemma transf_initial_states :
    forall s1 : state,
      initial_state prog s1 ->
      exists s2 : state,
        initial_state tprog s2 /\ match_states s1 s2.
  Proof using TRANSL.
    simplify. inv H.
    exploit function_ptr_translated. eauto. intros.
    inv H. inv H3.
    econstructor. econstructor. econstructor.
    eapply (Genv.init_mem_match TRANSL); eauto.
    setoid_rewrite (Linking.match_program_main TRANSL).
    rewrite symbols_preserved. eauto.
    eauto.
    econstructor.
  Qed.
  #[local] Hint Resolve transf_initial_states : mgen.

  Lemma transf_final_states :
    forall (s1 : state)
           (s2 : state)
           (r : Int.int),
      match_states s1 s2 ->
      final_state s1 r ->
      final_state s2 r.
  Proof using TRANSL.
    intros. inv H0. inv H. inv STACKS. unfold valueToInt. constructor. auto.
  Qed.
  #[local] Hint Resolve transf_final_states : mgen.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (semantics prog) (semantics tprog).
  Proof using TRANSL.
    eapply Smallstep.forward_simulation_step; eauto with mgen.
    apply senv_preserved. intros. eapply transf_final_states; eauto.
  Qed.

End CORRECTNESS.
