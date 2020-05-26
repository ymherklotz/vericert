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

From Coq Require Import FSets.FMapPositive.
From compcert Require RTL Op Maps Errors.
From coqup Require Import Coquplib Verilog Value HTL HTLgen AssocMap.

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
| tr_op_Olea : forall a l e s s' i, translate_eff_addressing a l s = OK e s' i -> tr_op (Op.Olea a) l e.

Inductive tr_instr (fin rtrn st : reg) : RTL.instruction -> stmnt -> stmnt -> Prop :=
| tr_instr_Inop :
    forall n,
      tr_instr fin rtrn st (RTL.Inop n) Vskip (state_goto st n)
| tr_instr_Iop :
    forall n op args e dst,
      tr_op op args e ->
      tr_instr fin rtrn st (RTL.Iop op args dst n) (Vnonblock (Vvar dst) e) (state_goto st n)
| tr_instr_Icond :
    forall n1 n2 cond args s s' i c,
      translate_condition cond args s = OK c s' i ->
      tr_instr fin rtrn st (RTL.Icond cond args n1 n2) Vskip (state_cond st c n1 n2)
| tr_instr_Ireturn_None :
    tr_instr fin rtrn st (RTL.Ireturn None) (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z)))
                                                  (block rtrn (Vlit (ZToValue 1%nat 0%Z)))) Vskip
| tr_instr_Ireturn_Some :
    forall r,
      tr_instr fin rtrn st (RTL.Ireturn (Some r))
               (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z))) (block rtrn (Vvar r))) Vskip.

Inductive tr_code (pc : RTL.node) (i : RTL.instruction) (stmnts trans : PositiveMap.t stmnt)
          (fin rtrn st : reg) : Prop :=
  tr_code_intro :
    forall s t,
      stmnts!pc = Some s ->
      trans!pc = Some t ->
      tr_instr fin rtrn st i s t ->
      tr_code pc i stmnts trans fin rtrn st.

Inductive tr_module (f : RTL.function) : module -> Prop :=
  tr_module_intro :
    forall data control fin rtrn st m,
      (forall pc i, Maps.PTree.get pc f.(RTL.fn_code) = Some i ->
                    tr_code pc i data control fin rtrn st) ->
      m = (mkmodule f.(RTL.fn_params)
                        data
                        control
                        f.(RTL.fn_entrypoint)
                            st fin rtrn) ->
      tr_module f m.

Lemma create_reg_datapath_trans :
  forall s s' x i,
    create_reg s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.

Lemma create_reg_controllogic_trans :
  forall s s' x i,
    create_reg s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.

Lemma get_refl_x :
  forall s s' x i,
    get s = OK x s' i ->
    s = x.
Proof. inversion 1. trivial. Qed.

Lemma get_refl_s :
  forall s s' x i,
    get s = OK x s' i ->
    s = s'.
Proof. inversion 1. trivial. Qed.

Ltac inv_incr :=
  match goal with
  | [ H: create_reg ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    assert (H1 := H); eapply create_reg_datapath_trans in H;
    eapply create_reg_controllogic_trans in H1; inv_incr
  | [ H: get ?s = OK _ _ _ |- _ ] =>
    let H1 := fresh "H" in
    assert (H1 := H); apply get_refl_x in H; apply get_refl_s in H1;
    subst; inv_incr
  | [ H: st_prop _ _ |- _ ] => unfold st_prop in H; destruct H; inv_incr
  | [ H: st_incr _ _ |- _ ] => destruct st_incr; inv_incr
  | _ => idtac
  end.

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
  destruct op eqn:?; try (econstructor; apply H); try discriminate; simpl in *;
    try (match goal with
           [ H: match ?args with _ => _ end _ = _ _ _ |- _ ] =>
           repeat (destruct args; try discriminate)
         end);
    monadInv H; constructor.
Qed.

Lemma iter_expand_instr_spec :
  forall l fin rtrn s s' i x,
    HTLMonadExtra.collectlist (transf_instr fin rtrn) l s = OK x s' i ->
    list_norepet (List.map fst l) ->
    (forall pc instr, In (pc, instr) l ->
                      tr_code pc instr s'.(st_datapath) s'.(st_controllogic) fin rtrn s'.(st_st)).
Proof.
  induction l; simpl; intros.
  - contradiction.
  - destruct a as [pc1 instr1]; simpl in *. inv H0. monadInv H. inv_incr.
    destruct (peq pc pc1).

    + subst.
      destruct instr1 eqn:?; try discriminate.

      * unfold add_instr in EQ.
        destruct (check_empty_node_datapath s1 pc1); try discriminate.
        destruct (check_empty_node_controllogic s1 pc1); try discriminate.
        inversion EQ.
        econstructor.
        destruct o with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        destruct o0 with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        inversion H1. inversion H7. rewrite H. apply tr_instr_Inop.
        eapply in_map with (f := fst) in H7. simpl in H7. contradiction.

      * monadInv EQ.
        inv_incr.
        unfold add_instr in EQ2.
        destruct (check_empty_node_datapath s0 pc1); try discriminate.
        destruct (check_empty_node_controllogic s0 pc1); try discriminate.
        inversion EQ2.
        econstructor.
        destruct o with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        destruct o0 with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        inversion H1. inversion H7. unfold nonblock. rewrite <- e2. rewrite H. constructor.
        eapply translate_instr_tr_op. apply EQ1.

        eapply in_map with (f := fst) in H7. simpl in H7. contradiction.

      * monadInv EQ.
        inv_incr.
        unfold add_branch_instr in EQ2.
        destruct (check_empty_node_datapath s0 pc1); try discriminate.
        destruct (check_empty_node_controllogic s0 pc1); try discriminate.
        inversion EQ2.

        econstructor.
        destruct o with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].
        destruct o0 with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        inversion H1. inversion H7. rewrite <- e2. rewrite H. econstructor.
        apply EQ1.

        eapply in_map with (f := fst) in H7. simpl in H7. contradiction.

      * destruct o3 eqn:?.
        unfold add_instr_skip in EQ.
        destruct (check_empty_node_datapath s1 pc1); try discriminate.
        destruct (check_empty_node_controllogic s1 pc1); try discriminate.
        inversion EQ.

        econstructor.
        destruct o with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].
        destruct o0 with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        inversion H1. inversion H7. constructor.

        eapply in_map with (f := fst) in H7. simpl in H7. contradiction.

        unfold add_instr_skip in EQ.
        destruct (check_empty_node_datapath s1 pc1); try discriminate.
        destruct (check_empty_node_controllogic s1 pc1); try discriminate.
        inversion EQ.

        econstructor.
        destruct o with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].
        destruct o0 with pc1; destruct H9; simpl in *; rewrite AssocMap.gss in H7;
          [ discriminate | apply H7 ].

        inversion H1. inversion H7. apply constructor.

        eapply in_map with (f := fst) in H7. simpl in H7. contradiction.

    + eapply IHl. apply EQ0. assumption.
      destruct H1. inversion H1. subst. contradiction.
      assumption.

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
  monadInv Heqr.
  econstructor; simpl; trivial.
  intros.
  inv_incr.
  assert (st_controllogic s8 = st_controllogic s2).
  { rewrite <- H5. rewrite <- H6. rewrite <- H7. trivial. }
  rewrite <- H10.
  assert (st_datapath s8 = st_datapath s2).
  { rewrite <- EQ4. rewrite <- EQ3. rewrite <- EQ2. trivial. }
  assert (st_st s5 = st_st s2).
  { rewrite H10. rewrite <- H50. trivial. }
  rewrite H80. rewrite H81. rewrite H82.
  eapply iter_expand_instr_spec.
  apply EQ0.
  apply Maps.PTree.elements_keys_norepet.
  apply Maps.PTree.elements_correct.
  assumption.
Qed.
