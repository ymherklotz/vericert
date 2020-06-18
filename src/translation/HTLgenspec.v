(*
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
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

From compcert Require RTL Op Maps Errors.
From compcert Require Import Maps.
From coqup Require Import Coquplib Verilog Value HTL HTLgen AssocMap.

Hint Resolve Maps.PTree.elements_keys_norepet : htlspec.
Hint Resolve Maps.PTree.elements_correct : htlspec.

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: st) (i: st_incr s1 s3),
    bind f g s1 = OK y s3 i ->
    exists x, exists s2, exists i1, exists i2,
            f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s'; exists s.
  destruct (g a s'); inv H.
  exists s0; auto.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: st) (i: st_incr s1 s3),
    bind2 f g s1 = OK z s3 i ->
    exists x, exists y, exists s2, exists i1, exists i2,
              f s1 = OK (x, y) s2 i1 /\ g x y s2 = OK z s3 i2.
Proof.
  unfold bind2; intros.
  exploit bind_inversion; eauto.
  intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
  exists x; exists y; exists s2; exists i1; exists i2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ _ = OK _ _ _) =>
    inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
    discriminate
  | (ret _ _ = OK _ _ _) =>
    inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
    discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
    let x := fresh "x" in (
      let s := fresh "s" in (
        let i1 := fresh "INCR" in (
          let i2 := fresh "INCR" in (
            let EQ1 := fresh "EQ" in (
              let EQ2 := fresh "EQ" in (
                destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
                clear H;
                try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let s := fresh "s" in (
          let i1 := fresh "INCR" in (
            let i2 := fresh "INCR" in (
              let EQ1 := fresh "EQ" in (
                let EQ2 := fresh "EQ" in (
                  destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
                  clear H;
                  try (monadInv1 EQ2))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

(** * Relational specification of the translation *)

(** We now define inductive predicates that characterise the fact that the
statemachine that is created by the translation contains the correct
translations for each of the elements *)

Inductive tr_op : Op.operation -> list reg -> expr -> Prop :=
| tr_op_Omove : forall r, tr_op Op.Omove (r::nil) (Vvar r)
| tr_op_Ointconst : forall n l, tr_op (Op.Ointconst n) l (Vlit (intToValue n))
| tr_op_Oneg : forall r, tr_op Op.Oneg (r::nil) (Vunop Vneg (Vvar r))
| tr_op_Osub : forall r1 r2, tr_op Op.Osub (r1::r2::nil) (bop Vsub r1 r2)
| tr_op_Omul : forall r1 r2, tr_op Op.Omul (r1::r2::nil) (bop Vmul r1 r2)
| tr_op_Omulimm : forall r n, tr_op (Op.Omulimm n) (r::nil) (boplit Vmul r n)
| tr_op_Odiv : forall r1 r2, tr_op Op.Odiv (r1::r2::nil) (bop Vdiv r1 r2)
| tr_op_Odivu : forall r1 r2, tr_op Op.Odivu (r1::r2::nil) (bop Vdivu r1 r2)
| tr_op_Omod : forall r1 r2, tr_op Op.Omod (r1::r2::nil) (bop Vmod r1 r2)
| tr_op_Omodu : forall r1 r2, tr_op Op.Omodu (r1::r2::nil) (bop Vmodu r1 r2)
| tr_op_Oand : forall r1 r2, tr_op Op.Oand (r1::r2::nil) (bop Vand r1 r2)
| tr_op_Oandimm : forall n r, tr_op (Op.Oandimm n) (r::nil) (boplit Vand r n)
| tr_op_Oor : forall r1 r2, tr_op Op.Oor (r1::r2::nil) (bop Vor r1 r2)
| tr_op_Oorimm : forall n r, tr_op (Op.Oorimm n) (r::nil) (boplit Vor r n)
| tr_op_Oxor : forall r1 r2, tr_op Op.Oxor (r1::r2::nil) (bop Vxor r1 r2)
| tr_op_Oxorimm : forall n r, tr_op (Op.Oxorimm n) (r::nil) (boplit Vxor r n)
| tr_op_Onot : forall r, tr_op Op.Onot (r::nil) (Vunop Vnot (Vvar r))
| tr_op_Oshl : forall r1 r2, tr_op Op.Oshl (r1::r2::nil) (bop Vshl r1 r2)
| tr_op_Oshlimm : forall n r, tr_op (Op.Oshlimm n) (r::nil) (boplit Vshl r n)
| tr_op_Oshr : forall r1 r2, tr_op Op.Oshr (r1::r2::nil) (bop Vshr r1 r2)
| tr_op_Oshrimm : forall n r, tr_op (Op.Oshrimm n) (r::nil) (boplit Vshr r n)
| tr_op_Ocmp : forall c l e s s' i, translate_condition c l s = OK e s' i -> tr_op (Op.Ocmp c) l e
| tr_op_Olea : forall a l e s s' i, translate_eff_addressing a l s = OK e s' i -> tr_op (Op.Olea a) l e
| tr_op_Oleal : forall a l e s s' i, translate_eff_addressing a l s = OK e s' i -> tr_op (Op.Oleal a) l e
| tr_op_Ocast32signed : forall r, tr_op (Op.Ocast32signed) (r::nil) (Vvar r).
Hint Constructors tr_op : htlspec.

Inductive tr_instr (fin rtrn st stk : reg) : RTL.instruction -> stmnt -> stmnt -> Prop :=
| tr_instr_Inop :
    forall n,
      tr_instr fin rtrn st stk (RTL.Inop n) Vskip (state_goto st n)
| tr_instr_Iop :
    forall n op args e dst,
      tr_op op args e ->
      tr_instr fin rtrn st stk (RTL.Iop op args dst n) (Vnonblock (Vvar dst) e) (state_goto st n)
| tr_instr_Icond :
    forall n1 n2 cond args s s' i c,
      translate_condition cond args s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Icond cond args n1 n2) Vskip (state_cond st c n1 n2)
| tr_instr_Ireturn_None :
    tr_instr fin rtrn st stk (RTL.Ireturn None) (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z)))
                                                  (block rtrn (Vlit (ZToValue 1%nat 0%Z)))) Vskip
| tr_instr_Ireturn_Some :
    forall r,
      tr_instr fin rtrn st stk (RTL.Ireturn (Some r))
               (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z))) (block rtrn (Vvar r))) Vskip
| tr_instr_Iload :
    forall mem addr args s s' i c dst n,
      translate_arr_access mem addr args stk s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Iload mem addr args dst n) (nonblock dst c) (state_goto st n)
| tr_instr_Istore :
    forall mem addr args s s' i c src n,
      translate_arr_access mem addr args stk s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Istore mem addr args src n) (Vnonblock c (Vvar src))
               (state_goto st n).
Hint Constructors tr_instr : htlspec.

Inductive tr_code (c : RTL.code) (pc : RTL.node) (i : RTL.instruction) (stmnts trans : PTree.t stmnt)
          (fin rtrn st stk : reg) : Prop :=
  tr_code_intro :
    forall s t,
      c!pc = Some i ->
      stmnts!pc = Some s ->
      trans!pc = Some t ->
      tr_instr fin rtrn st stk i s t ->
      tr_code c pc i stmnts trans fin rtrn st stk.
Hint Constructors tr_code : htlspec.

Inductive tr_module (f : RTL.function) : module -> Prop :=
  tr_module_intro :
    forall data control fin rtrn st stk stk_len m start rst clk scldecls arrdecls,
      (forall pc i, Maps.PTree.get pc f.(RTL.fn_code) = Some i ->
               tr_code f.(RTL.fn_code) pc i data control fin rtrn st stk) ->
      stk_len = Z.to_nat (f.(RTL.fn_stacksize) / 4) ->
      Z.modulo (f.(RTL.fn_stacksize)) 4 = 0 ->
      m = (mkmodule f.(RTL.fn_params)
                        data
                        control
                        f.(RTL.fn_entrypoint)
                        st stk stk_len fin rtrn start rst clk scldecls arrdecls) ->
      tr_module f m.
Hint Constructors tr_module : htlspec.

Lemma create_reg_datapath_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_datapath_trans : htlspec.

Lemma create_reg_controllogic_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_controllogic_trans : htlspec.

Lemma declare_reg_datapath_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_datapath_trans : htlspec.

Lemma declare_reg_controllogic_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_controllogic_trans : htlspec.

Lemma create_arr_datapath_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_arr_datapath_trans : htlspec.

Lemma create_arr_controllogic_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_arr_controllogic_trans : htlspec.

Lemma get_refl_x :
  forall s s' x i,
    get s = OK x s' i ->
    s = x.
Proof. inversion 1. trivial. Qed.
Hint Resolve get_refl_x : htlspec.

Lemma get_refl_s :
  forall s s' x i,
    get s = OK x s' i ->
    s = s'.
Proof. inversion 1. trivial. Qed.
Hint Resolve get_refl_s : htlspec.

Ltac inv_incr :=
  repeat match goal with
  | [ H: create_reg _ _ ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    assert (H1 := H); eapply create_reg_datapath_trans in H;
    eapply create_reg_controllogic_trans in H1
  | [ H: create_arr _ _ _ ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    assert (H1 := H); eapply create_arr_datapath_trans in H;
    eapply create_arr_controllogic_trans in H1
  | [ H: get ?s = OK _ _ _ |- _ ] =>
    let H1 := fresh "H" in
    assert (H1 := H); apply get_refl_x in H; apply get_refl_s in H1;
    subst
  | [ H: st_prop _ _ |- _ ] => unfold st_prop in H; destruct H
  | [ H: st_incr _ _ |- _ ] => destruct st_incr
  end.

Lemma collect_controllogic_trans :
  forall A f l cs cs' ci,
  (forall s s' x i y, f y s = OK x s' i -> s.(st_controllogic) = s'.(st_controllogic)) ->
  @HTLMonadExtra.collectlist A f l cs = OK tt cs' ci -> cs.(st_controllogic) = cs'.(st_controllogic).
Proof.
  induction l; intros; monadInv H0.
  - trivial.
  - apply H in EQ. rewrite EQ. eauto.
Qed.

Lemma collect_datapath_trans :
  forall A f l cs cs' ci,
  (forall s s' x i y, f y s = OK x s' i -> s.(st_datapath) = s'.(st_datapath)) ->
  @HTLMonadExtra.collectlist A f l cs = OK tt cs' ci -> cs.(st_datapath) = cs'.(st_datapath).
Proof.
  induction l; intros; monadInv H0.
  - trivial.
  - apply H in EQ. rewrite EQ. eauto.
Qed.

Lemma collect_declare_controllogic_trans :
  forall io n l s s' i,
  HTLMonadExtra.collectlist (fun r : reg => declare_reg io r n) l s = OK tt s' i ->
  s.(st_controllogic) = s'.(st_controllogic).
Proof.
  intros. eapply collect_controllogic_trans; try eassumption.
  intros. eapply declare_reg_controllogic_trans. simpl in H0. eassumption.
Qed.

Lemma collect_declare_datapath_trans :
  forall io n l s s' i,
  HTLMonadExtra.collectlist (fun r : reg => declare_reg io r n) l s = OK tt s' i ->
  s.(st_datapath) = s'.(st_datapath).
Proof.
  intros. eapply collect_datapath_trans; try eassumption.
  intros. eapply declare_reg_datapath_trans. simpl in H0. eassumption.
Qed.

Ltac rewrite_states :=
  match goal with
  | [ H: ?x ?s = ?x ?s' |- _ ] =>
    let c1 := fresh "c" in
    let c2 := fresh "c" in
    remember (?x ?s) as c1; remember (?x ?s') as c2; try subst
  end.

Lemma translate_instr_tr_op :
  forall op args s s' e i,
    translate_instr op args s = OK e s' i ->
    tr_op op args e.
Proof.
  intros.
  destruct op eqn:?; eauto with htlspec; try discriminate; simpl in *;
    try (match goal with
           [ H: match ?args with _ => _ end _ = _ _ _ |- _ ] =>
           repeat (destruct args; try discriminate)
         end);
    monadInv H; constructor.
Qed.
Hint Resolve translate_instr_tr_op : htlspec.

Ltac unfold_match H :=
  match type of H with
  | context[match ?g with _ => _ end] => destruct g eqn:?; try discriminate
  end.

Ltac inv_add_instr' H :=
  match type of H with
  | ?f _ _ _ = OK _ _ _ => unfold f in H
  | ?f _ _ _ _ = OK _ _ _ => unfold f in H
  | ?f _ _ _ _ _ = OK _ _ _ => unfold f in H
  end; repeat unfold_match H; inversion H.

Ltac inv_add_instr :=
  match goal with
  | H: context[add_instr_skip _ _ _] |- _ =>
    inv_add_instr' H
  | H: context[add_instr_skip _ _] |- _ =>
    monadInv H; inv_incr; inv_add_instr
  | H: context[add_instr _ _ _ _] |- _ =>
    inv_add_instr' H
  | H: context[add_instr _ _ _] |- _ =>
    monadInv H; inv_incr; inv_add_instr
  | H: context[add_branch_instr _ _ _ _ _] |- _ =>
    inv_add_instr' H
  | H: context[add_branch_instr _ _ _ _] |- _ =>
    monadInv H; inv_incr; inv_add_instr
  end.

Ltac destruct_optional :=
  match goal with H: option ?r |- _ => destruct H end.

Lemma iter_expand_instr_spec :
  forall l fin rtrn stack s s' i x c,
    HTLMonadExtra.collectlist (transf_instr fin rtrn stack) l s = OK x s' i ->
    list_norepet (List.map fst l) ->
    (forall pc instr, In (pc, instr) l -> c!pc = Some instr) ->
    (forall pc instr, In (pc, instr) l ->
                      c!pc = Some instr ->
                      tr_code c pc instr s'.(st_datapath) s'.(st_controllogic) fin rtrn s'.(st_st) stack).
Proof.
  induction l; simpl; intros; try contradiction.
  destruct a as [pc1 instr1]; simpl in *. inv H0. monadInv H. inv_incr.
  destruct (peq pc pc1).
  - subst.
    destruct instr1 eqn:?; try discriminate;
      try destruct_optional; inv_add_instr; econstructor; try assumption.
    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + inversion H2. inversion H9. rewrite H. apply tr_instr_Inop.
      eapply in_map with (f := fst) in H9. contradiction.

    + destruct o with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + destruct o0 with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + inversion H2. inversion H14. unfold nonblock. assert (HST: st_st s4 = st_st s2) by congruence. rewrite HST.
      constructor. eapply translate_instr_tr_op. apply EQ1.
      eapply in_map with (f := fst) in H14. contradiction.

    + destruct o with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + destruct o0 with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + inversion H2. inversion H14. rewrite <- e2. assert (HST: st_st s2 = st_st s0) by congruence.
      rewrite HST. econstructor. apply EQ1.
      eapply in_map with (f := fst) in H14. contradiction.

    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct H2.
      * inversion H2.
        replace (st_st s2) with (st_st s0) by congruence.
        eauto with htlspec.
      * apply in_map with (f := fst) in H2. contradiction.

    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct H2.
      * inversion H2.
        replace (st_st s2) with (st_st s0) by congruence.
        eauto with htlspec.
      * apply in_map with (f := fst) in H2. contradiction.

    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + inversion H2.
      * inversion H9.
        replace (st_st s2) with (st_st s0) by congruence.
        eauto with htlspec.
      * apply in_map with (f := fst) in H9. contradiction.

    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + inversion H2.
      * inversion H9.
        replace (st_st s2) with (st_st s0) by congruence.
        eauto with htlspec.
      * apply in_map with (f := fst) in H9. contradiction.

  - eapply IHl. apply EQ0. assumption.
    destruct H2. inversion H2. subst. contradiction.
    intros. specialize H1 with pc0 instr0. destruct H1. tauto. trivial.
    destruct H2. inv H2. contradiction. assumption. assumption.
Qed.
Hint Resolve iter_expand_instr_spec : htlspec.

Lemma create_arr_inv : forall w x y z a b c d,
    create_arr w x y z = OK (a, b) c d -> y = b.
Proof.
  inversion 1. reflexivity.
Qed.

Theorem transl_module_correct :
  forall f m,
    transl_module f = Errors.OK m -> tr_module f m.
Proof.
  intros until m.
  unfold transl_module.
  unfold run_mon.
  destruct (transf_module f (max_state f)) eqn:?; try discriminate.
  intros. inv H.
  inversion s; subst.

  unfold transf_module in *.
  destruct (Z.eq_dec (RTL.fn_stacksize f mod 4) 0); monadInv Heqr.

  (* TODO: We should be able to fold this into the automation. *)
  pose proof (create_arr_inv _ _ _ _ _ _ _ _ EQ0) as STK_LEN.
  rewrite <- STK_LEN.

  econstructor; simpl; trivial.
  intros.
  inv_incr.
  assert (EQ3D := EQ3).
  destruct x4.
  apply collect_declare_datapath_trans in EQ3.
  apply collect_declare_controllogic_trans in EQ3D.
  assert (STC: st_controllogic s10 = st_controllogic s3) by congruence.
  assert (STD: st_datapath s10 = st_datapath s3) by congruence.
  assert (STST: st_st s10 = st_st s3) by congruence.
  rewrite STC. rewrite STD. rewrite STST.
  eapply iter_expand_instr_spec; eauto with htlspec.
  apply PTree.elements_complete.
Qed.
