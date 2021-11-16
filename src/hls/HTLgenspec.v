(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *               2020 James Pollard <j@mes.dev>
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

Require compcert.backend.RTL.
Require compcert.common.Errors.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.HTL.
Require Import vericert.hls.HTLgen.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.FunctionalUnits.

#[local] Hint Resolve Maps.PTree.elements_keys_norepet : htlspec.
#[local] Hint Resolve Maps.PTree.elements_correct : htlspec.

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

Inductive tr_instr (fin rtrn st stk : reg) : RTL.instruction -> stmnt -> stmnt -> Prop :=
| tr_instr_Inop :
    forall n,
      Z.pos n <= Int.max_unsigned ->
      tr_instr fin rtrn st stk (RTL.Inop n) Vskip (state_goto st n)
| tr_instr_Iop :
    forall n op args dst s s' e i,
      Z.pos n <= Int.max_unsigned ->
      translate_instr op args s = OK e s' i ->
      tr_instr fin rtrn st stk (RTL.Iop op args dst n) (Vnonblock (Vvar dst) e) (state_goto st n)
| tr_instr_Icond :
    forall n1 n2 cond args s s' i c,
      Z.pos n1 <= Int.max_unsigned ->
      Z.pos n2 <= Int.max_unsigned ->
      translate_condition cond args s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Icond cond args n1 n2) Vskip (state_cond st c n1 n2)
| tr_instr_Ireturn_None :
    tr_instr fin rtrn st stk (RTL.Ireturn None) (Vseq (block fin (Vlit (ZToValue 1%Z)))
                                                  (block rtrn (Vlit (ZToValue 0%Z)))) Vskip
| tr_instr_Ireturn_Some :
    forall r,
      tr_instr fin rtrn st stk (RTL.Ireturn (Some r))
               (Vseq (block fin (Vlit (ZToValue 1%Z))) (block rtrn (Vvar r))) Vskip
| tr_instr_Iload :
    forall mem addr args s s' i c dst n,
      Z.pos n <= Int.max_unsigned ->
      translate_arr_access mem addr args stk s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Iload mem addr args dst n) (nonblock dst c) (state_goto st n)
| tr_instr_Istore :
    forall mem addr args s s' i c src n,
      Z.pos n <= Int.max_unsigned ->
      translate_arr_access mem addr args stk s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Istore mem addr args src n) (Vnonblock c (Vvar src))
               (state_goto st n).
(*| tr_instr_Ijumptable :
    forall cexpr tbl r,
    cexpr = tbl_to_case_expr st tbl ->
    tr_instr fin rtrn st stk (RTL.Ijumptable r tbl) (Vskip) (Vcase (Vvar r) cexpr (Some Vskip)).*)
#[local] Hint Constructors tr_instr : htlspec.

Inductive tr_code (c : RTL.code) (pc : RTL.node) (i : RTL.instruction) (stmnts trans : PTree.t stmnt)
          (fin rtrn st stk : reg) : Prop :=
  tr_code_intro :
    forall s t,
      c!pc = Some i ->
      stmnts!pc = Some s ->
      trans!pc = Some t ->
      tr_instr fin rtrn st stk i s t ->
      tr_code c pc i stmnts trans fin rtrn st stk.
#[local] Hint Constructors tr_code : htlspec.

Inductive tr_module (f : RTL.function) : module -> Prop :=
  tr_module_intro :
    forall data control fin rtrn st stk stk_len m start rst clk scldecls arrdecls wf1 wf2 wf3 wf4,
      m = (mkmodule f.(RTL.fn_params)
                        data
                        control
                        f.(RTL.fn_entrypoint)
                        st stk stk_len fin rtrn start rst clk scldecls arrdecls None wf1 wf2 wf3 wf4) ->
      (forall pc i, Maps.PTree.get pc f.(RTL.fn_code) = Some i ->
               tr_code f.(RTL.fn_code) pc i data control fin rtrn st stk) ->
      stk_len = Z.to_nat (f.(RTL.fn_stacksize) / 4) ->
      Z.modulo (f.(RTL.fn_stacksize)) 4 = 0 ->
      0 <= f.(RTL.fn_stacksize) < Integers.Ptrofs.modulus ->
      st = ((RTL.max_reg_function f) + 1)%positive ->
      fin = ((RTL.max_reg_function f) + 2)%positive ->
      rtrn = ((RTL.max_reg_function f) + 3)%positive ->
      stk = ((RTL.max_reg_function f) + 4)%positive ->
      start = ((RTL.max_reg_function f) + 5)%positive ->
      rst = ((RTL.max_reg_function f) + 6)%positive ->
      clk = ((RTL.max_reg_function f) + 7)%positive ->
      tr_module f m.
#[local] Hint Constructors tr_module : htlspec.

Lemma create_reg_datapath_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
#[local] Hint Resolve create_reg_datapath_trans : htlspec.

Lemma create_reg_controllogic_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
#[local] Hint Resolve create_reg_controllogic_trans : htlspec.

Lemma declare_reg_datapath_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
#[local] Hint Resolve create_reg_datapath_trans : htlspec.

Lemma declare_reg_controllogic_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
#[local] Hint Resolve create_reg_controllogic_trans : htlspec.

Lemma declare_reg_freshreg_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_freshreg) = s'.(st_freshreg).
Proof. inversion 1; auto. Qed.
#[local] Hint Resolve declare_reg_freshreg_trans : htlspec.

Lemma create_arr_datapath_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
#[local] Hint Resolve create_arr_datapath_trans : htlspec.

Lemma create_arr_controllogic_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
#[local] Hint Resolve create_arr_controllogic_trans : htlspec.

Lemma get_refl_x :
  forall s s' x i,
    get s = OK x s' i ->
    s = x.
Proof. inversion 1. trivial. Qed.
#[local] Hint Resolve get_refl_x : htlspec.

Lemma get_refl_s :
  forall s s' x i,
    get s = OK x s' i ->
    s = s'.
Proof. inversion 1. trivial. Qed.
#[local] Hint Resolve get_refl_s : htlspec.

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

Lemma collect_freshreg_trans :
  forall A f l cs cs' ci,
  (forall s s' x i y, f y s = OK x s' i -> s.(st_freshreg) = s'.(st_freshreg)) ->
  @HTLMonadExtra.collectlist A f l cs = OK tt cs' ci -> cs.(st_freshreg) = cs'.(st_freshreg).
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

Lemma collect_declare_freshreg_trans :
  forall io n l s s' i,
  HTLMonadExtra.collectlist (fun r : reg => declare_reg io r n) l s = OK tt s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  intros. eapply collect_freshreg_trans; try eassumption.
  inversion 1. auto.
Qed.

Ltac unfold_match H :=
  match type of H with
  | context[match ?g with _ => _ end] => destruct g eqn:?; try discriminate
  end.

Lemma translate_eff_addressing_freshreg_trans :
  forall op args s r s' i,
  translate_eff_addressing op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
#[local] Hint Resolve translate_eff_addressing_freshreg_trans : htlspec.

Lemma translate_comparison_freshreg_trans :
  forall op args s r s' i,
  translate_comparison op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
#[local] Hint Resolve translate_comparison_freshreg_trans : htlspec.

Lemma translate_comparisonu_freshreg_trans :
  forall op args s r s' i,
  translate_comparisonu op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
#[local] Hint Resolve translate_comparisonu_freshreg_trans : htlspec.

Lemma translate_comparison_imm_freshreg_trans :
  forall op args s r s' i n,
  translate_comparison_imm op args n s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
#[local] Hint Resolve translate_comparison_imm_freshreg_trans : htlspec.

Lemma translate_comparison_immu_freshreg_trans :
  forall op args s r s' i n,
  translate_comparison_immu op args n s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
#[local] Hint Resolve translate_comparison_immu_freshreg_trans : htlspec.

Lemma translate_condition_freshreg_trans :
  forall op args s r s' i,
  translate_condition op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; eauto with htlspec.
Qed.
#[local] Hint Resolve translate_condition_freshreg_trans : htlspec.

Lemma translate_instr_freshreg_trans :
  forall op args s r s' i,
  translate_instr op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; eauto with htlspec.
  monadInv H1. eauto with htlspec.
Qed.
#[local] Hint Resolve translate_instr_freshreg_trans : htlspec.

Lemma translate_arr_access_freshreg_trans :
  forall mem addr args st s r s' i,
  translate_arr_access mem addr args st s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  intros. unfold translate_arr_access in H. repeat (unfold_match H); inv H; eauto with htlspec.
Qed.
#[local] Hint Resolve translate_arr_access_freshreg_trans : htlspec.

Lemma add_instr_freshreg_trans :
  forall n n' st s r s' i,
  add_instr n n' st s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_instr in H. repeat (unfold_match H). inv H. auto. Qed.
#[local] Hint Resolve add_instr_freshreg_trans : htlspec.

Lemma add_branch_instr_freshreg_trans :
  forall n n0 n1 e s r s' i,
  add_branch_instr e n n0 n1 s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_branch_instr in H. repeat (unfold_match H). inv H. auto. Qed.
#[local] Hint Resolve add_branch_instr_freshreg_trans : htlspec.

Lemma add_node_skip_freshreg_trans :
  forall n1 n2 s r s' i,
  add_node_skip n1 n2 s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_node_skip in H. repeat (unfold_match H). inv H. auto. Qed.
#[local] Hint Resolve add_node_skip_freshreg_trans : htlspec.

Lemma add_instr_skip_freshreg_trans :
  forall n1 n2 s r s' i,
  add_instr_skip n1 n2 s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_instr_skip in H. repeat (unfold_match H). inv H. auto. Qed.
#[local] Hint Resolve add_instr_skip_freshreg_trans : htlspec.

Lemma transf_instr_freshreg_trans :
  forall fin ret st instr s v s' i,
    transf_instr fin ret st instr s = OK v s' i ->
    s.(st_freshreg) = s'.(st_freshreg).
Proof.
  intros. destruct instr eqn:?. subst. unfold transf_instr in H.
  destruct i0; try (monadInv H); try (unfold_match H); eauto with htlspec.
  - monadInv H. apply add_instr_freshreg_trans in EQ2. apply translate_instr_freshreg_trans in EQ.
    apply declare_reg_freshreg_trans in EQ1. congruence.
  - monadInv H. apply add_instr_freshreg_trans in EQ2. apply translate_arr_access_freshreg_trans in EQ.
    apply declare_reg_freshreg_trans in EQ1. congruence.
  - monadInv H. apply add_instr_freshreg_trans in EQ0. apply translate_arr_access_freshreg_trans in EQ. congruence.
  - monadInv H. apply translate_condition_freshreg_trans in EQ. apply add_branch_instr_freshreg_trans in EQ0.
    congruence.
  (*- inv EQ. apply add_node_skip_freshreg_trans in EQ0. congruence.*)
Qed.
#[local] Hint Resolve transf_instr_freshreg_trans : htlspec.

Lemma collect_trans_instr_freshreg_trans :
  forall fin ret st l s s' i,
  HTLMonadExtra.collectlist (transf_instr fin ret st) l s = OK tt s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  intros. eapply collect_freshreg_trans; try eassumption.
  eauto with htlspec.
Qed.

Ltac rewrite_states :=
  match goal with
  | [ H: ?x ?s = ?x ?s' |- _ ] =>
    let c1 := fresh "c" in
    let c2 := fresh "c" in
    remember (?x ?s) as c1; remember (?x ?s') as c2; try subst
  end.

Ltac inv_add_instr' H :=
  match type of H with
  | ?f _ _ = OK _ _ _ => unfold f in H
  | ?f _ _ _ = OK _ _ _ => unfold f in H
  | ?f _ _ _ _ = OK _ _ _ => unfold f in H
  | ?f _ _ _ _ _ = OK _ _ _ => unfold f in H
  | ?f _ _ _ _ _ _ = OK _ _ _ => unfold f in H
  end; repeat unfold_match H; inversion H.

Ltac inv_add_instr :=
  match goal with
  | H: (if ?c then _ else _) _ = OK _ _ _ |- _ => destruct c eqn:EQN; try discriminate; inv_add_instr
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
  | H: context[add_node_skip _ _ _] |- _ =>
    inv_add_instr' H
  | H: context[add_node_skip _ _] |- _ =>
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
      apply Z.leb_le. assumption.
      eapply in_map with (f := fst) in H9. contradiction.

    + destruct o with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + destruct o0 with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + inversion H2. inversion H14. unfold nonblock. replace (st_st s4) with (st_st s2) by congruence.
      econstructor. apply Z.leb_le; assumption.
      apply EQ1. eapply in_map with (f := fst) in H14. contradiction.

    + destruct o with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + destruct o0 with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + inversion H2. inversion H14. rewrite <- e2. replace (st_st s2) with (st_st s0) by congruence.
      econstructor. apply Z.leb_le; assumption.
      apply EQ1. eapply in_map with (f := fst) in H14. contradiction.

    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct H2.
      * inversion H2.
        replace (st_st s2) with (st_st s0) by congruence.
        econstructor. apply Z.leb_le; assumption.
        eauto with htlspec.
      * apply in_map with (f := fst) in H2. contradiction.

    + destruct o with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct o0 with pc1; destruct H11; simpl in *; rewrite AssocMap.gss in H9; eauto; congruence.
    + destruct H2.
      * inversion H2.
        replace (st_st s2) with (st_st s0) by congruence.
        econstructor; try (apply Z.leb_le; apply andb_prop in EQN; apply EQN).
        eauto with htlspec.
      * apply in_map with (f := fst) in H2. contradiction.

    (*+ destruct o with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + destruct o0 with pc1; destruct H16; simpl in *; rewrite AssocMap.gss in H14; eauto; congruence.
    + inversion H2.
      * inversion H14. constructor. congruence.
      * apply in_map with (f := fst) in H14. contradiction.
      *)
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
#[local] Hint Resolve iter_expand_instr_spec : htlspec.

Lemma create_arr_inv : forall w x y z a b c d,
    create_arr w x y z = OK (a, b) c d ->
    y = b /\ a = z.(st_freshreg) /\ c.(st_freshreg) = Pos.succ (z.(st_freshreg)).
Proof.
  inversion 1; split; auto.
Qed.

Lemma create_reg_inv : forall a b s r s' i,
    create_reg a b s = OK r s' i ->
    r = s.(st_freshreg) /\ s'.(st_freshreg) = Pos.succ (s.(st_freshreg)).
Proof.
  inversion 1; auto.
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
  unfold stack_correct in *.
  destruct (0 <=? RTL.fn_stacksize f) eqn:STACK_BOUND_LOW;
    destruct (RTL.fn_stacksize f <? Integers.Ptrofs.modulus) eqn:STACK_BOUND_HIGH;
    destruct (RTL.fn_stacksize f mod 4 =? 0) eqn:STACK_ALIGN;
    crush;
    monadInv Heqr.

  repeat unfold_match EQ9. monadInv EQ9.

  (* TODO: We should be able to fold this into the automation. *)
  pose proof (create_arr_inv _ _ _ _ _ _ _ _ EQ0) as STK_LEN. inv STK_LEN. inv H5.
  pose proof (create_reg_inv _ _ _ _ _ _ EQ) as FIN_VAL. inv FIN_VAL.
  pose proof (create_reg_inv _ _ _ _ _ _ EQ1) as RET_VAL. inv RET_VAL.
  destruct x3. destruct x4.
  pose proof (collect_trans_instr_freshreg_trans _ _ _ _ _ _ _ EQ2) as TR_INSTR.
  pose proof (collect_declare_freshreg_trans _ _ _ _ _ _ EQ3) as TR_DEC.
  pose proof (create_reg_inv _ _ _ _ _ _ EQ4) as START_VAL. inv START_VAL.
  pose proof (create_reg_inv _ _ _ _ _ _ EQ5) as RESET_VAL. inv RESET_VAL.
  pose proof (create_reg_inv _ _ _ _ _ _ EQ6) as CLK_VAL. inv CLK_VAL.
  rewrite H9 in *. rewrite H8 in *. replace (st_freshreg s4) with (st_freshreg s2) in * by congruence.
  rewrite H6 in *. rewrite H7 in *. rewrite H5 in *. simpl in *.
  inv_incr.
  econstructor; simpl; auto; try lia.
  intros.
  assert (EQ3D := EQ3).
  apply collect_declare_datapath_trans in EQ3.
  apply collect_declare_controllogic_trans in EQ3D.
  replace (st_controllogic s10) with (st_controllogic s3) by congruence.
  replace (st_datapath s10) with (st_datapath s3) by congruence.
  replace (st_st s10) with (st_st s3) by congruence.
  eapply iter_expand_instr_spec; eauto with htlspec.
  rewrite H5. rewrite H7. apply EQ2.
  apply PTree.elements_complete.
  eauto with htlspec.
  erewrite <- collect_declare_freshreg_trans; try eassumption.
  lia.
Qed.
