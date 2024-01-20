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

Inductive match_arr_sizes : assocmap_arr -> reg -> nat -> Prop :=
| match_arr_sizes_intro : forall arr stk stk_arr len,
  arr ! stk = Some stk_arr ->
  arr_length stk_arr = len ->
  match_arr_sizes arr stk len.

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr' asa'
      (STK_ASSOC: match_assocmaps asr asr')
      (STK_ARR_ASSOC: match_arrs asa asa')
      (STK_ARR_SIZE1: match_empty_size m asa)
      (STK_ARR_SIZE2: match_empty_size m asa'),
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r (transf_module m) pc asr' asa').

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa'
           (ASSOC: match_assocmaps asr asr')
           (ARR_ASSOC: match_arrs asa asa')
           (ARR_SIZE1: match_empty_size m asa)
           (ARR_SIZE2: match_empty_size m asa')
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

  (* Lemma transf_maps_correct': *)
  (*   forall t asr asa s asr' asa', *)
  (*     stmnt_runp t (mkassociations asr empty_assocmap) asa s asr' asa' -> *)
  (*     (forall r e1 e0 r0 e3, s <> (Vseq (Vseq Vskip (Vblock (Vvari r e1) e0)) (Vblock (Vvar r0) e3))) -> *)
  (*     forall tasr, *)
  (*       match_reg_assocs (mkassociations asr empty_assocmap) (mkassociations tasr empty_assocmap) -> *)
  (*       exists tasr', stmnt_runp t (mkassociations tasr empty_assocmap) asa (transf_maps s) tasr' asa' *)
  (*                     /\ match_assocmaps (Verilog.merge_regs (assoc_nonblocking asr') (assoc_blocking asr')) *)
  (*                     (Verilog.merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr')). *)
  (* Proof. *)
  (*   intros * ? HNEQ **. destruct s; try solve [exploit match_states_same; eauto; simplify; *)
  (*     exploit match_assocmaps_merge; eauto]. *)
  (*   cbn in *.  *)
  (*   repeat (destruct_match; try solve [exploit match_states_same; eauto; simplify; *)
  (*     exploit match_assocmaps_merge; eauto]). *)
  (*   - simplify. *)
  (*     inv H. inv H11. inv H10. inv H14; inv H10. inv H15; inv H10. *)
  (*     inv H14. *)
  (*     eexists; split. econstructor. econstructor. econstructor. *)
  (*     2: { econstructor. econstructor. econstructor. unfold block_reg in *; cbn in *. eapply expr_interchangeable; eauto. *)
  (*          eapply expr_runp_same; eauto. inv H0; auto. eauto. } *)
  (*     unfold block_reg in *; cbn in *. eapply expr_interchangeable2; eauto. *)
  (*     eapply expr_runp_same; eauto. eapply match_assocmaps_set; eauto. *)
  (*     inv H0; auto. *)
  (*     econstructor; intros. cbn. *)
  (*     unfold merge_regs, AssocMapExt.merge. inv H0; subst; cbn. *)
  (*     rewrite !PTree.gcombine by auto. *)
  (*     rewrite negb_true_iff in *. *)
  (*     apply Pos.eqb_neq in H4. apply Pos.eqb_neq in H2. apply Pos.eqb_neq in H5. *)
  (*     destruct (peq r r2); subst. *)
  (*     + rewrite !AssocMap.gss by auto. rewrite !AssocMap.gso by auto. auto. *)
  (*     + rewrite !AssocMap.gso by auto. *)
  (*       destruct (peq r r1); subst. *)
  (*       ** rewrite !AssocMap.gss. rewrite !AssocMap.gso by auto. auto. *)
  (*       ** rewrite !AssocMap.gso by auto. inv H8. rewrite H. auto. *)
  (*   - subst. exfalso; eapply HNEQ; eauto. *)
  (* Qed. *)

Lemma expr_runp_same :
  forall f rs ar e v,
    expr_runp f rs ar e v ->
    forall trs tar,
      match_assocmaps rs trs ->
      match_arrs ar tar ->
      expr_runp f trs tar e v.
Proof.
  induction 1.
  - intros. econstructor.
  - intros. econstructor. inv H0. symmetry.
    apply find_assoc_get.
    apply H2.
  - intros. econstructor. apply IHexpr_runp; eauto.
    inv H2.
    unfold arr_assocmap_lookup in *.
    destruct (stack ! r) eqn:?; [|discriminate].
    inv H0.
    eapply H3 in Heqo. inv Heqo. inv H0.
    unfold arr in *. rewrite H2. inv H5.
    rewrite H0. auto.
  - intros. econstructor; eauto.
  - intros. econstructor; eauto.
  - intros. econstructor; eauto.
  - intros. eapply erun_Vternary_false. apply IHexpr_runp1; eauto.
    apply IHexpr_runp2; eauto. auto.
  - intros. econstructor. apply IHexpr_runp; eauto. eauto. eauto.
    erewrite match_assocmaps_inv_map; eauto. rewrite H0. now rewrite H1.
Qed.

Lemma stmnt_runp_same :
  forall f rs1 ar1 c rs2 ar2,
    stmnt_runp f rs1 ar1 c rs2 ar2 ->
      forall trs1 tar1,
        match_reg_assocs rs1 trs1 ->
        match_arr_assocs ar1 tar1 ->
        exists trs2 tar2,
          stmnt_runp f trs1 tar1 c trs2 tar2
          /\ match_reg_assocs rs2 trs2
          /\ match_arr_assocs ar2 tar2.
Proof.
  induction 1.
  - do 2 eexists; split; [|split]; eauto; constructor.
  - intros. exploit IHstmnt_runp1; eauto; simplify.
    exploit IHstmnt_runp2; eauto; simplify.
    do 2 econstructor; split; [|split]; eauto.
    econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H2; inversion H3; subst; exploit expr_runp_same; eauto; intros.
    do 2 eexists; split; eauto; econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H2; inversion H3; subst; exploit expr_runp_same; eauto; intros.
    do 2 eexists; split; eauto; eapply stmnt_runp_Vcond_false; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H3; inversion H4. subst. exploit expr_runp_same; [eapply H| | |]; eauto; intros.
    exploit expr_runp_same; [eapply H0| | |]; eauto; intros.
    do 2 eexists; split; eauto. econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H3; inversion H4; subst. exploit expr_runp_same; [eapply H| | |]; eauto; intros.
    exploit expr_runp_same; [eapply H0| | |]; eauto; intros.
    do 2 eexists; split; eauto. eapply stmnt_runp_Vcase_match; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H1; inversion H2. subst. exploit expr_runp_same; [eapply H| | |]; eauto; intros.
    do 2 eexists; split; eauto. eapply stmnt_runp_Vcase_default; eauto.
  - inv H; intros.
    inversion H; inversion H1; subst. exploit expr_runp_same; eauto; intros.
    do 2 econstructor; split; [|split]; intros. econstructor; eauto. econstructor.
    econstructor; cbn; eauto.
    econstructor; intros.
    destruct (peq r r0); subst.
    + now rewrite !AssocMap.gss.
    + rewrite !AssocMap.gso by auto. inv H2; eauto.
    + eauto.
  - inv H; intros.
    inversion H; inversion H1; subst. exploit expr_runp_same; eauto; intros.
    do 2 econstructor; split; [|split]; intros. econstructor; eauto. econstructor.
    econstructor; cbn; eauto.
    econstructor; intros.
    destruct (peq r r0); subst.
    + now rewrite !AssocMap.gss.
    + rewrite !AssocMap.gso by auto. inv H3; eauto.
    + eauto.
  - inv H; intros. inversion H; inversion H1; subst.
    exploit expr_runp_same; [eapply H0| | |]; eauto; intros.
    exploit expr_runp_same; [eapply H6| | |]; eauto; intros.
    do 2 eexists; split; [|split]; eauto.
    econstructor; eauto. econstructor; eauto.
    eapply match_arr_assocs_block; eauto.
  - inv H; intros. inversion H; inversion H1; subst.
    exploit expr_runp_same; [eapply H0| | |]; eauto; intros.
    exploit expr_runp_same; [eapply H6| | |]; eauto; intros.
    do 2 eexists; split; [|split]; eauto.
    econstructor; eauto. econstructor; eauto.
    eapply match_arr_assocs_nonblock; eauto.
Qed.

Lemma exec_ram_same :
  forall rs1 ar1 c rs2 ar2,
    exec_ram rs1 ar1 c rs2 ar2 ->
    forall trs1 tar1,
      match_reg_assocs rs1 trs1 ->
      match_arr_assocs ar1 tar1 ->
      exists trs2 tar2,
        exec_ram trs1 tar1 c trs2 tar2
        /\ match_reg_assocs rs2 trs2
        /\ match_arr_assocs ar2 tar2.
Proof.
  induction 1; intros.
  - do 2 eexists; split; [|split]; eauto.
    apply exec_ram_Some_idle. inv H0. cbn in *; setoid_rewrite match_assocmaps_inv_map; eauto.
  - inv H6; do 2 eexists; split; [|split]; cbn in *.
    + eapply exec_ram_Some_write. eapply H. eauto. all: cbn in *.
      now erewrite match_assocmaps_inv_map by eauto.
      all: try (erewrite match_assocmaps_inv by eauto; eauto).
    + unfold nonblock_reg; cbn. constructor; auto.
      now apply match_assocmaps_set.
    + eapply match_arr_assocs_nonblock; eauto.
  - inv H5; do 2 eexists; split; [|split]; cbn in *.
    + eapply exec_ram_Some_read; eauto; cbn in *.
      now erewrite match_assocmaps_inv_map by eauto.
      all: (try (erewrite match_assocmaps_inv by eauto; eauto)).
      eapply match_arrs_read; eauto. inv H6; eauto.
    + unfold nonblock_reg; cbn. constructor; auto.
      now repeat apply match_assocmaps_set.
    + eauto.
  - do 2 eexists; split; [|split]; cbn in *; eauto. econstructor.
Qed.

Lemma match_reg_assocs_empty :
  forall ars ars',
    match_assocmaps ars ars' ->
    match_reg_assocs (mkassociations ars empty_assocmap) (mkassociations ars' empty_assocmap).
Proof.
  intros; constructor; auto.
  apply match_assocmaps_refl.
Qed.

Lemma match_arr_assocs_empty :
  forall ars ars',
    match_arrs ars ars' ->
    forall st l, match_arr_assocs (mkassociations ars (empty_stack st l)) 
                   (mkassociations ars' (empty_stack st l)).
Proof.
  intros; constructor; auto. apply match_arrs_equiv.
Qed.

Lemma match_empty_size_empty_stack:
  forall m, match_empty_size m (empty_stack (mod_stk m) (mod_stk_len m)).
Proof.
  unfold match_empty_size; intros.
  apply match_arrs_size_equiv.
Qed.

Lemma match_arrs_trans :
  forall asa1 asa2 asa3, 
    match_arrs asa1 asa2 -> match_arrs asa2 asa3 -> match_arrs asa1 asa3.
Proof.
  inversion 1. inversion 1; subst.
  econstructor; eauto.
  intros. eapply H0 in H2. simplify. eapply H5 in H2; simplify.
  econstructor; split; eauto. split; congruence.
Qed.


  Lemma arr_assocmap_set_gss :
    forall r i v asa ar,
      asa ! r = Some ar ->
      (arr_assocmap_set r i v asa) ! r = Some (array_set i (Some v) ar).
  Proof.
    unfold arr_assocmap_set.
    intros. rewrite H. rewrite PTree.gss. auto.
  Qed.

  Lemma arr_assocmap_set_gso :
    forall r x i v asa ar,
      asa ! x = Some ar ->
      r <> x ->
      (arr_assocmap_set r i v asa) ! x = asa ! x.
  Proof.
    unfold arr_assocmap_set. intros. 
    destruct (asa!r) eqn:?; auto; now rewrite PTree.gso by auto.
  Qed.

  Lemma arr_assocmap_set_gs2 :
    forall r x i v asa,
      asa ! x = None ->
      (arr_assocmap_set r i v asa) ! x = None.
  Proof.
    unfold arr_assocmap_set. intros. 
    destruct (peq r x); subst; [now rewrite H|].
    destruct (asa!r) eqn:?; auto.
    now rewrite PTree.gso by auto.
  Qed.

  Lemma arr_assocmap_set_gs2' :
    forall r x i v asa,
      (arr_assocmap_set r i v asa) ! x = None ->
      asa ! x = None.
  Proof.
    unfold arr_assocmap_set. intros. destruct_match; auto.
    destruct (peq r x); subst.
    - rewrite PTree.gss in H. inv H.
    - now rewrite PTree.gso in H by auto.
  Qed.

Lemma transf_maps_correct:
  forall t asr asa s asr' asa' m,
    stmnt_runp t (mkassociations asr empty_assocmap) (mkassociations asa (empty_stack (mod_stk m) (mod_stk_len m))) s asr' asa' ->
    forall tasr tasa,
      match_assocmaps asr tasr ->
      match_arrs asa tasa ->
      match_empty_size m asa ->
      match_empty_size m tasa ->
      exists tasr' tasa',
        stmnt_runp t (mkassociations tasr empty_assocmap) (mkassociations tasa (empty_stack (mod_stk m) (mod_stk_len m)))
          (transf_maps (mod_stk m) s) tasr' tasa'
        /\ match_assocmaps (Verilog.merge_regs (assoc_nonblocking asr') (assoc_blocking asr'))
                           (Verilog.merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr'))
        /\ match_arrs (Verilog.merge_arrs (assoc_nonblocking asa') (assoc_blocking asa'))
                      (Verilog.merge_arrs (assoc_nonblocking tasa') (assoc_blocking tasa')).
Proof.
  intros * HSTMNT * HMATCH_ASSOC HMATCH_ARR HMATCH_SIZE1 HMATCH_SIZE2. 
  pose proof (match_reg_assocs_empty _ _ ltac:(eauto)) as HREG_ASSOCS;
    pose proof (match_arr_assocs_empty _ _ ltac:(eauto)) as HARR_ASSOCS;
    exploit stmnt_runp_same; eauto; intros (trs2 & tar2 & HSTMNT' & HMATCH_REG' & HMATCH_ARR');
    pose proof (match_assocmaps_merge _ _ ltac:(eauto)) as HMATCH_MERGE_REG;
    pose proof (match_empty_size_empty_stack m);
    exploit match_arrs_size_stmnt_preserved; try exact HSTMNT'; eauto; cbn; 
    intros (HMATCH_SZ_BLOCK' & HMATCH_SZ_NONBLOCK');
    exploit match_arrs_size_stmnt_preserved; try exact HSTMNT; eauto; cbn; 
    intros (HMATCH_SZ_BLOCK & HMATCH_SZ_NONBLOCK);
    pose proof (match_empty_size_match _ _ _ HMATCH_SZ_BLOCK HMATCH_SZ_NONBLOCK) as MATCH_SIZE;
    inversion HMATCH_ARR' as [basa' btar2 nasa' ntar2 HMATCH_ARR'1 HMATCH_ARR'2]; subst; cbn in *;
    pose proof (match_arrs_merge _ _ _ _ MATCH_SIZE HMATCH_ARR'2 HMATCH_ARR'1) as MATCH_MERGE.
  unfold transf_maps. repeat destruct_match; eauto; 
  repeat (kill_bools; match goal with | H: _ /\ _ |- _ => inv H end);
  try rewrite negb_true_iff in *;
  repeat match goal with | H: _ =? _ = false |- _ => apply Pos.eqb_neq in H
                         | H: _ =? _ = true |- _ => apply Pos.eqb_eq in H end; subst.
  - rename H3 into NE1, H4 into NE2, H5 into NE3, H0 into CHECK1, H6 into CHECK2.
    inv HSTMNT'. inv H5. inv H6. inv H8; [|inv H7]. inv H5. inv H10; inv H7.
    inv H11. cbn in *.
    do 2 eexists; split; [|split].
    + econstructor. econstructor. econstructor. cbn. eapply expr_interchangeable2; eauto.
      econstructor. econstructor. econstructor; cbn. eapply expr_interchangeable; eauto.
      eassumption.
    + cbn. eapply match_assocmaps_trans; eauto. econstructor; intros.
      unfold merge_regs, AssocMapExt.merge, empty_assocmap. rewrite !PTree.gcombine by auto.
      destruct (peq r r0); subst.
      * rewrite !PTree.gss. rewrite PTree.gso by auto. now rewrite !PTree.gempty.
      * repeat (rewrite !PTree.gso by auto; symmetry). setoid_rewrite PTree.gso at 2; auto.
        destruct (peq r r1); subst.
        -- rewrite PTree.gss. rewrite PTree.gempty. rewrite PTree.gss. auto.
        -- rewrite !PTree.gso by auto. auto.
    + auto.
  - rename H3 into NE1, H4 into CHECK3, H2 into CHECK1, H5 into CHECK2.
    inv HSTMNT'. inv H5. inv H6. inv H8; [|inv H7]. inv H5. inv H10; inv H7.
    cbn in *.
    do 2 eexists; split; [|split].
    + econstructor. econstructor. econstructor. cbn. eapply expr_interchangeable3; eauto.
      eapply stmnt_runp_Vnonblock_arr. econstructor. cbn. eapply expr_interchangeable; eauto.
      eapply expr_interchangeable; eauto.
    + cbn. eapply match_assocmaps_trans; eauto. econstructor; intros. auto.
    + cbn. eapply match_arrs_trans; eauto.
      econstructor; intros.
      * eapply merge_arr_empty' in H0; [|eapply match_empty_assocmap_set; eauto].
        destruct (peq s (mod_stk m)); subst.
        -- exploit arrs_present; eauto; simplify. erewrite arr_assocmap_set_gss in H0; eauto.
           inv H0. clear MATCH_MERGE.
           eexists; split; [|split].
           ** unfold merge_arrs. rewrite AssocMap.gcombine by auto.
              unfold merge_arr. rewrite H2.
              erewrite arr_assocmap_set_gss; eauto.
              unfold empty_stack. rewrite PTree.gss. eauto.
           ** intros.
              inv HMATCH_SIZE2. eapply H1 in H2. simplify.
              unfold empty_stack in H2. rewrite AssocMap.gss in H2. inv H2.
              case_eq ((addr <? arr_length x)%nat); intros.
              ++ pose proof (Nat.ltb_spec0 addr (arr_length x)). rewrite H2 in H5. inv H5.
                 destruct (Nat.eq_dec addr (valueToNat iv)); subst.
                 --- rewrite array_get_error_set_bound by auto.
                     erewrite combine_lookup_second; eauto.
                     now rewrite array_get_error_set_bound by lia.
                 --- rewrite array_gso by auto. 
                     erewrite combine_array_set; eauto.
                     rewrite array_gso by auto. 
                     rewrite arr_repeat_length in H6.
                     now rewrite combine_none2 by auto.
              ++ pose proof (Nat.ltb_spec0 addr (arr_length x)). rewrite H2 in H5. inv H5.
                 assert ((addr >= arr_length x)%nat) by lia.
                 pose proof (@arr_repeat_length (option value) (mod_stk_len m) None).
                 pose proof (array_set_len x (valueToNat iv) (Some rhsval0)).
                 assert (arr_length (array_set (valueToNat iv) (Some rhsval0) x) = arr_length (arr_repeat None (mod_stk_len m))) by eauto.
                 exploit (@combine_length (option value)); eauto; intros.
                 instantiate (1 := merge_cell) in H13.
                 setoid_rewrite array_get_error_bound_gt; auto. 
                 rewrite combine_length; eauto. 
                 erewrite <- array_set_len; eauto.
                 rewrite arr_repeat_length; eauto. lia.
           ** inv HMATCH_SIZE2. eapply H1 in H2.
              unfold empty_stack in H2. rewrite AssocMap.gss in H2. inv H2.
              inv H5. inv H2.
              erewrite <- array_set_len; eauto.
              rewrite combine_length; eauto.
        -- unfold merge_arrs. rewrite AssocMap.gcombine.
           destruct (tasa ! s) eqn:?.
           ** inv HMATCH_SIZE2. eapply H2 in Heqo. simplify. unfold empty_stack in H6.
              rewrite PTree.gso in H6 by auto. now rewrite PTree.gempty in H6.
           ** now rewrite arr_assocmap_set_gs2 in H0 by auto.
           ** auto.
      * unfold merge_arrs in *. rewrite AssocMap.gcombine in * by auto. unfold empty_stack in *.
        destruct (peq s (mod_stk m)); subst.
        -- rewrite AssocMap.gss in H0.
           inv HMATCH_SIZE2; eauto. unfold empty_stack in *. 
           assert ((AssocMap.set (mod_stk m) (arr_repeat None (mod_stk_len m)) (AssocMap.empty arr)) ! (mod_stk m) = Some (arr_repeat None (mod_stk_len m))) by (now rewrite AssocMap.gss by auto).
           eapply H1 in H5. clear MATCH_MERGE; simplify.
           now (erewrite arr_assocmap_set_gss in H0; eauto).
        -- destruct (tasa ! s) eqn:?.
           ** inv HMATCH_SIZE2; eauto. eapply H2 in Heqo.
              clear MATCH_MERGE. simplify. unfold empty_stack in *.
              rewrite AssocMap.gso in H6 by auto. now rewrite AssocMap.gempty in H6.
           ** rewrite arr_assocmap_set_gs2; auto. rewrite AssocMap.gso by auto.
              now rewrite AssocMap.gempty.
Qed.

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
    - inversion 1; subst.
      exploit transf_maps_correct; eauto. simplify.
      exploit exec_ram_same; eauto. econstructor; eauto. eapply match_assocmaps_refl.
      econstructor; eauto. eapply match_arrs_equiv.
      simplify.
      destruct x, x0, x1, x2. cbn in *.
      econstructor; split.
      + econstructor; cbn.
        1-3: now erewrite match_assocmaps_inv by eauto.
        rewrite PTree.gmap1. rewrite H2. cbn. eauto. eassumption.
        eassumption. eauto. eauto. inv H10.
        erewrite match_assocmaps_inv; eauto. eapply match_assocmaps_merge2; eauto.
        eauto.
     + exploit match_arrs_size_stmnt_preserved; try eapply H3; eauto; cbn.
       eapply match_empty_size_empty_stack. simplify.
       exploit match_arrs_size_ram_preserved2; try eapply H4; eauto.
       eapply match_empty_size_empty_stack. 
       eapply match_empty_size_merge; eauto. simplify.
       exploit match_arrs_size_stmnt_preserved; eauto; cbn.
       eapply match_empty_size_empty_stack. simplify.
       exploit match_arrs_size_ram_preserved2; eauto.
       eapply match_empty_size_empty_stack. 
       eapply match_empty_size_merge; eauto. simplify.
       econstructor. inv H10; eapply match_assocmaps_merge2; eauto.
       inv H14. eapply match_arrs_merge; eauto. eapply match_empty_size_match; eauto.
       eapply match_empty_size_merge; eauto.
       eapply match_empty_size_merge; eauto.
       eauto.
    - inversion 1; subst. econstructor; split.
      apply step_finish; cbn. now erewrite match_assocmaps_inv by eauto.
      erewrite match_assocmaps_inv by eauto. eassumption.
      econstructor; auto.
    - inversion 1; subst; intros. econstructor; split.
      apply step_call. econstructor; auto. inv H.
      repeat apply match_assocmaps_set. cbn.
      apply match_assocmaps_refl.
      cbn. apply match_arrs_equiv.
      apply match_empty_size_empty_stack.
      cbn; apply match_empty_size_empty_stack.
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
