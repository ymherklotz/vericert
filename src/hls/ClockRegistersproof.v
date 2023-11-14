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
Require Import vericert.hls.ClockRegisters.

Import Errors.
Require Import vericert.common.Errormonad.
Import Errormonad.ErrorMonadExtra.
Import ErrorMonad.

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
    forall r m pc asr asa asr' tm
      (STK_ASSOC: match_assocmaps asr asr')
      (TRANSF: transf_module m = OK tm),
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r tm pc asr' asa).

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa tm
           (ASSOC: match_assocmaps asr asr')
           (TRANSF: transf_module m = OK tm)
           (STACK: Forall2 match_stackframes res res'),
      match_states (State res m st asr asa)
                   (State res' tm st asr' asa)
| match_returnstate :
    forall res res' i
           (STACKS: Forall2 match_stackframes res res'),
      match_states (Returnstate res i) (Returnstate res' i)
| match_initial_call :
    forall m tm
      (TRANSF: transf_module m = OK tm),
      match_states (Callstate nil m nil)
                   (Callstate nil tm nil).

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
  Linking.match_program (fun cu f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. unfold transf_program, match_prog.
  eapply Linking.match_transform_partial_program; auto.
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

Lemma transf_module_eq :
  forall m dm, 
    transf_module m = OK dm ->
    dm.(mod_params) = m.(mod_params)
    /\ dm.(mod_entrypoint) = m.(mod_entrypoint)
    /\ dm.(mod_st) = m.(mod_st)
    /\ dm.(mod_stk) = m.(mod_stk)
    /\ dm.(mod_stk_len) = m.(mod_stk_len)
    /\ dm.(mod_finish) = m.(mod_finish)
    /\ dm.(mod_return) = m.(mod_return)
    /\ dm.(mod_start) = m.(mod_start)
    /\ dm.(mod_reset) = m.(mod_reset)
    /\ dm.(mod_clk) = m.(mod_clk)
    /\ dm.(mod_scldecls) = m.(mod_scldecls)
    /\ dm.(mod_arrdecls) = m.(mod_arrdecls)
    /\ dm.(mod_ram) = m.(mod_ram).
Proof.
  unfold transf_module, bind in *; intros.
  repeat destruct_match; try discriminate. inv H; cbn. tauto.
Qed.

Lemma expr_runp_clock_expr :
  forall f e e' asr asa btasr rhsval t,
    (forall (r : positive) (e : expr),
         t ! r = Some e -> exists v : value, expr_runp f btasr asa e v /\ asr ! r = Some v) ->
    (forall r : positive, t ! r = None -> btasr ! r = asr ! r) ->
    clock_expr t e = OK e' ->
    expr_runp f asr asa e rhsval ->
    expr_runp f btasr asa e' rhsval.
Proof.
  induction e; intros; cbn in *; unfold bind in *; repeat (destruct_match; try discriminate; []).
  - inv H1. inv H2. constructor.
  - inv H2. destruct (t ! r) eqn:?; inv H1.
    + eapply H in Heqo. simplify. unfold find_assocmap, AssocMapExt.get_default. rewrite H3. auto.
    + eapply H0 in Heqo. econstructor. unfold find_assocmap, AssocMapExt.get_default. rewrite Heqo. auto.
  - inv H1. inv H2. econstructor; eauto.
  - inv H1.
  - inv H1. inv H2.
  - inv H1. inv H2. econstructor; eauto.
  - inv H1. inv H2. econstructor; eauto.
  - inv H1. inv H2. econstructor; eauto.
    eapply erun_Vternary_false; eauto.
Qed.

Lemma match_assocmaps_empty_right :
  forall a b,
    match_assocmaps a b ->
    match_assocmaps a (merge_regs empty_assocmap b).
Proof.
  inversion 1; intros; subst. econstructor; intros.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  now rewrite PTree.gempty.
Qed.

Lemma match_assocmaps_empty_right2 :
  forall a b,
    match_assocmaps a b ->
    match_assocmaps a (merge_regs b empty_assocmap).
Proof.
  inversion 1; intros; subst. econstructor; intros.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  rewrite PTree.gempty. 
  rewrite H0. destruct (b ! r); eauto.
Qed.

Lemma match_assocmaps_empty_left :
  forall a b,
    match_assocmaps a b ->
    match_assocmaps (merge_regs empty_assocmap a) b.
Proof.
  inversion 1; intros; subst. econstructor; intros.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  rewrite PTree.gempty. 
  rewrite H0. destruct (b ! r); eauto.
Qed.

Lemma match_assocmaps_empty_left2 :
  forall a b,
    match_assocmaps a b ->
    match_assocmaps (merge_regs a empty_assocmap) b.
Proof.
  inversion 1; intros; subst. econstructor; intros.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  rewrite PTree.gempty. 
  rewrite H0. destruct (b ! r); eauto.
Qed.

Lemma match_assocmaps_empty_right' :
  forall a b,
    match_assocmaps a (merge_regs empty_assocmap b) ->
    match_assocmaps a b.
Proof.
  inversion 1; intros; subst. econstructor. intros. rewrite H0.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge. 
  rewrite PTree.gcombine by auto.
  now rewrite PTree.gempty.
Qed.

Lemma match_assocmaps_empty_right2' :
  forall a b,
    match_assocmaps a (merge_regs b empty_assocmap) ->
    match_assocmaps a b.
Proof.
  inversion 1; intros; subst. econstructor; intros. rewrite H0.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  rewrite PTree.gempty. 
  destruct (b ! r); eauto.
Qed.

Lemma match_assocmaps_empty_left' :
  forall a b,
    match_assocmaps (merge_regs empty_assocmap a) b ->
    match_assocmaps a b.
Proof.
  inversion 1; intros; subst. econstructor; intros. rewrite <- H0. 
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  rewrite PTree.gempty. 
  destruct (b ! r); eauto.
Qed.

Lemma match_assocmaps_empty_left2' :
  forall a b,
    match_assocmaps (merge_regs a empty_assocmap) b ->
    match_assocmaps a b.
Proof.
  inversion 1; intros; subst. econstructor; intros. rewrite <- H0.
  unfold merge_regs, empty_assocmap, AssocMapExt.merge.
  rewrite PTree.gcombine by auto.
  rewrite PTree.gempty.
  destruct (a ! r); eauto.
Qed.

Lemma stmnt_runp_clock_stmnt_empty :
  forall data t t' data',
    clock_stmnt t data = OK (t', data') ->
    forall f asr asa asr' asa',
      stmnt_runp f (mkassociations asr empty_assocmap) 
                   asa data asr' asa' ->
      exists asr'', asr' = (mkassociations asr'' empty_assocmap) /\ asa = asa'.
Proof.
  induction data; cbn in *; intros.
  - inv H0. eauto.
  - cbn in *. inv H0. 
    unfold bind2 in *; repeat (destruct_match; try discriminate; []). inv H.
    exploit IHdata1; eauto; simplify.
    exploit IHdata2; eauto; simplify.
  - discriminate.
  - discriminate.
  - unfold bind in *. repeat (destruct_match; try discriminate; []). inv H.
    inv H0; inv H5. cbn in *. eexists. unfold block_reg. auto.
  - repeat (destruct_match; try discriminate).
Qed.

Lemma stmnt_runp_clock_stmnt_out :
  forall data t t' data',
    clock_stmnt t data = OK (t', data') ->
    forall f basr nasr asa asr' asa',
      stmnt_runp f (mkassociations basr nasr) asa data' asr' asa' ->
      exists nasr', asr' = (mkassociations basr nasr') /\ asa = asa'.
Proof.
  induction data; cbn in *; intros.
  - inv H. inv H0. eauto.
  - cbn in *.
    unfold bind2 in *; repeat (destruct_match; try discriminate; []). inv H.
    inv H0.
    exploit IHdata1; eauto; simplify.
    exploit IHdata2; eauto; simplify.
  - discriminate.
  - discriminate.
  - unfold bind in *. repeat (destruct_match; try discriminate; []). inv H.
    inv H0; inv H5. cbn in *. eexists. unfold nonblock_reg. auto.
  - repeat (destruct_match; try discriminate).
Qed.

Lemma clock_stmnt_const :
  forall data t t0 s, 
    clock_stmnt t data = OK (t0, s) ->
    forall x, t0 ! x = None -> t ! x = None.
Proof.
  induction data.
  - inversion 1; subst; eauto.
  - intros; cbn in *. unfold bind2 in *. repeat (destruct_match; try discriminate).
    inv H. exploit IHdata1; eauto; simplify.
  - cbn in *; discriminate.
  - cbn in *; discriminate.
  - intros. cbn in *. unfold bind in *. repeat (destruct_match; try discriminate). subst. 
    inv H; eauto. destruct (peq r x); subst.
    + now rewrite PTree.gss in H0.
    + now rewrite PTree.gso in H0 by auto.
  - cbn; intros. repeat (destruct_match; try discriminate).
Qed.

(* Lemma stmnt_runp_clock_stmnt_t_in : *)
(*   forall data t t' data', *)
(*     clock_stmnt t data = OK (t', data') -> *)
(*     forall f asr asa asr' asa' a b, *)
(*       stmnt_runp f (mkassociations asr empty_assocmap)  *)
(*                    (mkassociations asa (empty_stack a b)) data (mkassociations asr' empty_assocmap) asa' -> *)
(*       forall btasr ntasr, *)
(*         match_assocmaps asr (merge_regs ntasr btasr) -> *)
(*         (forall r e, t ! r = Some e -> exists v, expr_runp f btasr asa e v /\ AssocMap.get r asr = Some v) -> *)
(*         (forall r, t ! r = None -> btasr ! r = asr ! r) -> *)
(*         (forall r e, t' ! r = Some e -> exists v, expr_runp f btasr asa e v /\ AssocMap.get r asr' = Some v). *)
(* Proof. *)
(*   induction data; cbn in *; intros. *)
(*   - inv H. inv H0. eauto. *)
(*   - unfold bind2 in *. repeat (destruct_match; try discriminate; []). inv H. *)
(*     inv H0. cbn in *. *)
(*     exploit stmnt_runp_clock_stmnt_empty. eapply Heqr0. eauto. simplify. *)
(*     exploit stmnt_runp_clock_stmnt_empty. eapply Heqr1. eauto. simplify. *)
(*     inv H. *)
(*     destruct (t0 ! r) eqn:?. *)
(*     + exploit IHdata1; eauto; simplify. *)
(*       exploit IHdata2; eauto. *)

Lemma stmnt_runp_clock_stmnt :
  forall data t t' data',
    clock_stmnt t data = OK (t', data') ->
    forall f asr asa asr' asa' a b,
      stmnt_runp f (mkassociations asr empty_assocmap) 
                   (mkassociations asa (empty_stack a b)) data asr' asa' ->
      forall btasr ntasr,
        match_assocmaps asr (merge_regs ntasr btasr) ->
        (forall r e, t ! r = Some e -> exists v, expr_runp f btasr asa e v /\ AssocMap.get r asr = Some v) ->
        (forall r, t ! r = None -> btasr ! r = asr ! r) ->
        exists tasr',
          stmnt_runp f (mkassociations btasr ntasr) (mkassociations asa (empty_stack a b)) data' tasr' asa'
          /\ match_assocmaps (merge_regs (assoc_nonblocking asr') (assoc_blocking asr'))
                             (merge_regs (assoc_nonblocking tasr') (assoc_blocking tasr'))
          /\ (forall r e, t' ! r = Some e -> exists v, expr_runp f btasr asa e v /\ AssocMap.get r (assoc_blocking asr') = Some v)
          /\ (forall r, t' ! r = None -> btasr ! r = (assoc_blocking asr') ! r).
Proof.
  induction data; cbn in *; intros.
  - inv H. inv H0. eexists. split; [|split]. econstructor. cbn.
    eapply match_assocmaps_empty_left. eauto. eauto.
  - unfold bind2 in *. repeat (destruct_match; try discriminate; []). inv H.
    inv H0. exploit stmnt_runp_clock_stmnt_empty. 2: { eassumption. }
    eauto. simplify. exploit IHdata1; eauto. Opaque merge_regs. simplify.
    destruct x0. cbn in *. exploit IHdata2. eauto. eauto.
    eapply match_assocmaps_empty_left'; eauto.
    exploit stmnt_runp_clock_stmnt_out. 2: { eauto. } eauto. simplify. inv H5.
    eauto. exploit stmnt_runp_clock_stmnt_out. 2: { eauto. } eauto. simplify. inv H5. eauto.
    simplify.
    econstructor; split; [|split; [|split]].
    + econstructor; eauto.
    + eauto.
    + exploit stmnt_runp_clock_stmnt_out. 2: { eapply H. } eauto.
      simplify. inv H10. eauto.
    + exploit stmnt_runp_clock_stmnt_out. 2: { eapply H. } eauto.
      simplify. inv H10. eauto.
    Transparent merge_regs. 
  - inv H.
  - inv H.
  - unfold bind in *. repeat (destruct_match; try discriminate; []). inv H.
    inv H0; inv H8. cbn in *.
    econstructor. split; [|split].
    econstructor. econstructor. cbn. eapply expr_runp_clock_expr; eauto.
    cbn. econstructor. intros. unfold merge_regs, AssocMapExt.merge, empty_assocmap in *.
    rewrite !PTree.gcombine by auto. rewrite PTree.gempty. cbn.
    inv H1. destruct (peq r r0); subst.
    + rewrite !PTree.gss. cbn. auto.
    + rewrite !PTree.gso by auto. rewrite H. rewrite PTree.gcombine by auto. auto.
    + split. intros. destruct (peq r0 r); subst.
      * rewrite PTree.gss in H. inv H.
        eexists; split. eapply expr_runp_clock_expr; eauto.
        rewrite PTree.gss. auto.
      * rewrite PTree.gso in H by auto. rewrite PTree.gso by auto. eauto.
      * intros. destruct (peq r r0); subst.
        -- rewrite PTree.gss in H. discriminate.
        -- rewrite PTree.gso in H by auto. rewrite PTree.gso by auto. eauto.
  - repeat (destruct_match; try discriminate).
Qed.

Require Import ProofIrrelevance.

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
        Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  #[local] Hint Resolve function_ptr_translated : mgen.

  Lemma functions_translated:
    forall (v: Values.val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  #[local] Hint Resolve functions_translated : mgen.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof. exact (Genv.senv_transf_partial TRANSL). Qed.
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
      unfold transf_module, bind in *; repeat (destruct_match; try discriminate; []). inv TRANSF.
      exploit transf_clock_stmnt_spec; eauto.
      eapply PTree.xelements_keys_norepet.
      eapply PTree.elements_correct. eauto. simplify.
      exploit stmnt_runp_clock_stmnt. eauto. eauto.
      eapply match_assocmaps_empty_right; eauto.
      intros. rewrite PTree.gempty in H5. discriminate.
      intros. inv ASSOC. eauto.
      simplify. destruct x1; cbn in *.
      exploit exec_ram_same; eauto.
      econstructor; eauto. apply match_assocmaps_refl.
      simplify. destruct x1. cbn in *.
      econstructor.
      econstructor.
      + econstructor. cbn. erewrite match_assocmaps_inv; eauto.
        erewrite match_assocmaps_inv; eauto.
        erewrite match_assocmaps_inv; eauto.
        cbn. eauto.
        cbn. eauto.
        cbn. eauto.
        eauto.
        eauto. cbn.
        eapply match_assocmaps_merge in H16.
        erewrite match_assocmaps_inv; eauto. eauto.
      + econstructor. eapply match_assocmaps_merge in H16. cbn in *. eauto.
        unfold transf_module, bind. rewrite Heqm0. destruct_match; auto. 
        simplify. cbn in Heqs0.
        pose proof (proof_irrelevance _ l l0). subst. auto.
        cbn in *. rewrite Heqs in Heqs0. discriminate.
        auto.
    - inversion 1; subst. exploit transf_module_eq; eauto. simplify. econstructor; split.
      apply step_finish; cbn. erewrite match_assocmaps_inv by eauto; congruence.
      erewrite match_assocmaps_inv by eauto. rewrite H8. eauto.
      econstructor; auto.
    - inversion 1; subst; intros. exploit transf_module_eq; eauto. simplify. 
      econstructor; split.
      apply step_call. rewrite H1. rewrite H5. rewrite H8. rewrite H2. rewrite H4.  rewrite H3. 
      rewrite H0. 
      econstructor; auto. inv H.
      repeat apply match_assocmaps_set. cbn.
      apply match_assocmaps_refl.
    - inversion 1; subst. inv STACKS. inv H0. destruct y.
      eexists; split. eapply step_return. eauto. inv H2.
      exploit transf_module_eq; eauto; simplify.
      constructor; auto. rewrite H1. repeat apply match_assocmaps_set. auto.
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
    destruct x; cbn in *; unfold Errors.bind in *;
    repeat (destruct_match; try discriminate; []); try (destruct_match; discriminate).
    inv H4.
    econstructor. econstructor. econstructor.
    eapply (Genv.init_mem_match TRANSL); eauto.
    setoid_rewrite (Linking.match_program_main TRANSL).
    rewrite symbols_preserved. eauto.
    eauto.
    econstructor. eauto.
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
