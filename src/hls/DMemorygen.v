(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021-2023 Yann Herklotz <yann@yannherklotz.com>
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

Local Open Scope positive.
Local Open Scope assocmap.

#[local] Hint Resolve max_reg_stmnt_le_stmnt_tree : mgen.
#[local] Hint Resolve max_reg_stmnt_lt_stmnt_tree : mgen.
#[local] Hint Resolve max_stmnt_lt_module : mgen.

Lemma int_eq_not_false : forall x, Int.eq x (Int.not x) = false.
Proof.
  intros. unfold Int.eq.
  rewrite Int.unsigned_not.
  replace Int.max_unsigned with 4294967295%Z by crush.
  assert (X: forall x, (x <> 4294967295 - x)%Z) by lia.
  specialize (X (Int.unsigned x)). apply zeq_false; auto.
Qed.

Definition opt_eqb {A} (eqb: A -> A -> bool) (a b: option A): bool :=
  match a, b with
  | Some a', Some b' => eqb a' b'
  | None, None => true
  | _, _ => false
  end.

Definition unop_eqb (e1 e2: unop): bool :=
  match e1, e2 with
  | Vneg, Vneg => true
  | Vnot, Vnot => true
  | _, _ => false
  end.

Definition binop_eqb (e1 e2: binop): bool :=
  match e1, e2 with
  | Vadd, Vadd => true
  | Vsub, Vsub => true
  | Vmul, Vmul => true
  | Vdiv, Vdiv => true
  | Vdivu, Vdivu => true
  | Vmod, Vmod => true
  | Vmodu, Vmodu => true
  | Vlt, Vlt => true
  | Vltu, Vltu => true
  | Vgt, Vgt => true
  | Vgtu, Vgtu => true
  | Vle, Vle => true
  | Vleu, Vleu => true
  | Vge, Vge => true
  | Vgeu, Vgeu => true
  | Veq, Veq => true
  | Vne, Vne => true
  | Vand, Vand => true
  | Vor, Vor => true
  | Vxor, Vxor => true
  | Vshl, Vshl => true
  | Vshr, Vshr => true
  | Vshru, Vshru => true
  | _, _ => false
  end.

Fixpoint expr_eqb (e1 e2: expr): bool :=
  match e1, e2 with
  | Vlit v, Vlit v' => Int.eq v v'
  | Vvar r, Vvar r' => Pos.eqb r r'
  | Vvari r e, Vvari r' e' => Pos.eqb r r' && expr_eqb e e'
  | Vrange r e1 e2, Vrange r' e1' e2' =>
    Pos.eqb r r' && expr_eqb e1 e1' && expr_eqb e2 e2'
  | Vinputvar r, Vinputvar r' => Pos.eqb r r'
  | Vbinop b e1 e2, Vbinop b' e1' e2' =>
    binop_eqb b b' && expr_eqb e1 e1' && expr_eqb e2 e2'
  | Vunop b e1, Vunop b' e1' =>
    unop_eqb b b' && expr_eqb e1 e1'
  | Vternary e1 e2 e3, Vternary e1' e2' e3' =>
    expr_eqb e1 e1' && expr_eqb e2 e2' && expr_eqb e3 e3'
  | _, _ => false
  end.

Fixpoint stmnt_eqb (s1 s2: stmnt): bool :=
  match s1, s2 with
  | Vskip, Vskip => true
  | Vseq s1 s2, Vseq s1' s2' => stmnt_eqb s1 s1' && stmnt_eqb s2 s2'
  | Vcond e st sf, Vcond e' st' sf' =>
    expr_eqb e e'
    && stmnt_eqb st st'
    && stmnt_eqb sf sf'
  | Vcase e sl os, Vcase e' sl' os' =>
    expr_eqb e e'
    && stmnt_expr_list_eqb sl sl'
    && opt_eqb stmnt_eqb os os'
  | Vblock e1 e2, Vblock e1' e2' =>
    expr_eqb e1 e1' && expr_eqb e2 e2'
  | Vnonblock e1 e2, Vnonblock e1' e2' =>
    expr_eqb e1 e1' && expr_eqb e2 e2'
  | _, _ => false
  end
with stmnt_expr_list_eqb (s1 s2: stmnt_expr_list): bool :=
  match s1, s2 with
  | Stmntnil, Stmntnil => true
  | Stmntcons e s sl, Stmntcons e' s' sl' =>
    expr_eqb e e'
    && stmnt_eqb s s'
    && stmnt_expr_list_eqb sl sl'
  | _, _ => false
  end.

Fixpoint replace_stmnt (base r b: stmnt): stmnt :=
  match base with
  | Vskip as st | Vblock _ _ as st | Vnonblock _ _ as st =>
    if stmnt_eqb st r then b else st
  | Vseq s1 s2 =>
    Vseq (replace_stmnt s1 r b) (replace_stmnt s2 r b)
  | Vcond c s1 s2 =>
    Vcond c (replace_stmnt s1 r b) (replace_stmnt s2 r b)
  | Vcase e sl (Some os) =>
    Vcase e (replace_stmnt_expr_list sl r b) (Some (replace_stmnt os r b))
  | Vcase e sl None =>
    Vcase e (replace_stmnt_expr_list sl r b) None
  end
with replace_stmnt_expr_list (base: stmnt_expr_list) (r b: stmnt) :=
  match base with
  | Stmntnil => Stmntnil
  | Stmntcons e s sl =>
    Stmntcons e (replace_stmnt s r b) (replace_stmnt_expr_list sl r b)
  end.

Definition transf_maps state ram in_ (d: PTree.t stmnt) :=
  match in_ with
  | (i, n) =>
    match PTree.get i d with
    (* Conditional store *)
    | Some (Vseq (Vseq Vskip (Vcond ec (Vblock (Vvari r e1) e2) Vskip)) (Vblock (Vvar state') (Vlit y))) =>
      if (r =? (ram_mem ram)) && (state' =? state) then
        let nd := Vseq (Vblock (Vvar (ram_u_en ram)) (Vbinop Vxor (Vunop Vneg (Vbinop Vne ec (Vlit (ZToValue 0)))) (Vvar (ram_u_en ram))))
                       (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                             (Vseq (Vblock (Vvar (ram_d_in ram)) (Vternary ec e2 (Vvar (ram_d_in ram))))
                                   (Vblock (Vvar (ram_addr ram)) (Vternary ec e1 (Vvar (ram_addr ram))))))
        in
        PTree.set i (Vseq nd (Vblock (Vvar state') (Vlit y))) d
      else d
    | Some (Vseq ((Vblock (Vvar _) _) as rest) (Vnonblock (Vvari r e1) e2)) =>
      if r =? (ram_mem ram) then
        let nd := Vseq (Vblock (Vvar (ram_u_en ram)) (Vunop Vnot (Vvar (ram_u_en ram))))
                       (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                             (Vseq (Vblock (Vvar (ram_d_in ram)) e2)
                                   (Vblock (Vvar (ram_addr ram)) e1)))
        in
        PTree.set i (Vseq rest nd) d
      else d
    | Some (Vseq (Vseq Vskip (Vblock (Vvar e1) (Vternary ec (Vvari r e2) (Vvar e4)))) (Vblock (Vvar st') (Vlit e3))) =>
      if (r =? (ram_mem ram)) && (st' =? state) && (Z.pos n <=? Int.max_unsigned)%Z
         && (e1 <? state) && (max_reg_expr e2 <? state) && (max_reg_expr (Vlit e3) <? state)
         && (max_reg_expr ec <? state) && (e1 =? e4)
      then
        let nd :=
            Vseq (Vblock (Vvar (ram_u_en ram)) (Vbinop Vxor (Vunop Vneg (Vbinop Vne ec (Vlit (ZToValue 0)))) (Vvar (ram_u_en ram))))
                 (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                       (Vblock (Vvar (ram_addr ram)) (Vternary ec e2 (Vvar (ram_addr ram)))))
        in
        let aout := Vblock (Vvar e1) (Vternary ec (Vvar (ram_d_out ram)) (Vvar e4)) in
        let redirect := Vblock (Vvar state) (Vlit (posToValue n)) in
        (PTree.set i (Vseq redirect nd) (PTree.set n (Vseq (Vblock (Vvar st') (Vlit e3)) aout) d))
      else d
    | Some (Vseq (Vblock (Vvar st') e3) (Vnonblock (Vvar e1) (Vvari r e2))) =>
      if (r =? (ram_mem ram)) && (st' =? state) && (Z.pos n <=? Int.max_unsigned)%Z
         && (e1 <? state) && (max_reg_expr e2 <? state) && (max_reg_expr e3 <? state)
      then
        let nd :=
            Vseq (Vblock (Vvar (ram_u_en ram)) (Vunop Vnot (Vvar (ram_u_en ram))))
                 (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                       (Vblock (Vvar (ram_addr ram)) e2))
        in
        let aout := Vblock (Vvar e1) (Vvar (ram_d_out ram)) in
        let redirect := Vblock (Vvar state) (Vlit (posToValue n)) in
        (PTree.set i (Vseq redirect nd) (PTree.set n (Vseq (Vblock (Vvar st') e3) aout) d))
      else d
    | _ => d
    end
  end.

Lemma transf_maps_wf :
  forall state ram d d' i,
    map_well_formed d ->
    transf_maps state ram i d = d' ->
    map_well_formed d'.
Proof.
  unfold transf_maps; intros; repeat destruct_match; try destruct i;
  try match goal with
  | H: (_, _) = (_, _) |- _ => inv H
  end; auto.
  - unfold map_well_formed.
    simplify; intros.
    destruct (Pos.eq_dec p p1); subst; auto.
    unfold map_well_formed in *.
    apply AssocMap.elements_correct in Heqo.
    eapply in_map with (f := fst) in Heqo. simplify.
    apply AssocMapExt.elements_iff in H0. inv H0.
    rewrite AssocMap.gss in H3. inv H3; auto.
    apply AssocMapExt.elements_iff in H0. inv H0.
    repeat rewrite AssocMap.gso in H3 by lia. unfold map_well_formed in H.
    eapply H. eapply AssocMapExt.elements_iff; eauto.
  - unfold map_well_formed in *; intros.
    apply AssocMapExt.elements_iff in H0. inv H0.
    destruct (peq p p1); subst.
    + rewrite PTree.gss in H1.
      eapply H. eapply AssocMapExt.elements_iff; eauto.
    + rewrite PTree.gso in H1 by auto. destruct (peq p1 p0); subst.
      -- simplify. eauto.
      -- rewrite PTree.gso in H1 by auto. eapply H. eapply AssocMapExt.elements_iff; eauto.
  - unfold map_well_formed in *; intros.
    apply AssocMapExt.elements_iff in H0. inv H0.
    destruct (peq p p1); subst.
    + rewrite PTree.gss in H1.
      eapply H. eapply AssocMapExt.elements_iff; eauto.
    + rewrite PTree.gso in H1 by auto. destruct (peq p1 p0); subst.
      -- simplify. eauto.
      -- rewrite PTree.gso in H1 by auto. eapply H. eapply AssocMapExt.elements_iff; eauto.
  - unfold map_well_formed.
    simplify; intros.
    destruct (Pos.eq_dec p p1); subst; auto.
    unfold map_well_formed in *.
    apply AssocMap.elements_correct in Heqo.
    eapply in_map with (f := fst) in Heqo. simplify.
    apply AssocMapExt.elements_iff in H0. inv H0.
    rewrite AssocMap.gss in H1. inv H1; auto.
    apply AssocMapExt.elements_iff in H0. inv H0.
    repeat rewrite AssocMap.gso in H3 by lia. unfold map_well_formed in H.
    eapply H. eapply AssocMapExt.elements_iff; eauto.
    rewrite PTree.gso in H1; eauto.
Qed.

Definition max_pc {A: Type} (m: PTree.t A) :=
  fold_right Pos.max 1%positive (map fst (PTree.elements m)).

Fixpoint zip_range {A: Type} n (l: list A) {struct l} :=
  match l with
  | nil => nil
  | a :: b => (a, n) :: zip_range (n+1) b
  end.

Lemma zip_range_fst_idem : forall A (l: list A) a, map fst (zip_range a l) = l.
Proof. induction l; crush. Qed.

Lemma zip_range_not_in_snd :
  forall A (l: list A) a n, a < n -> ~ In a (map snd (zip_range n l)).
Proof.
  unfold not; induction l; crush.
  inv H0; try lia. eapply IHl.
  assert (X: a0 < n + 1) by lia. apply X; auto. auto.
Qed.

Lemma zip_range_snd_no_repet :
  forall A (l: list A) a, list_norepet (map snd (zip_range a l)).
Proof.
  induction l; crush; constructor; auto; [].
  apply zip_range_not_in_snd; lia.
Qed.

Lemma zip_range_in :
  forall A (l: list A) a n i, In (a, i) (zip_range n l) -> In a l.
Proof.
  induction l; crush. inv H. inv H0. auto. right. eapply IHl; eauto.
Qed.

Lemma zip_range_not_in :
  forall A (l: list A) a i n, ~ In a l -> ~ In (a, i) (zip_range n l).
Proof.
  unfold not; induction l; crush. inv H0. inv H1. apply H. left. auto.
  apply H. right. eapply zip_range_in; eauto.
Qed.

Lemma zip_range_no_repet :
  forall A (l: list A) a, list_norepet l -> list_norepet (zip_range a l).
Proof.
  induction l; simplify; constructor;
  match goal with H: list_norepet _ |- _ => inv H end;
  [apply zip_range_not_in|]; auto.
Qed.

Definition transf_code state ram d :=
  fold_right (transf_maps state ram) d
             (zip_range (max_pc d + 1)
                        (map fst (PTree.elements d))).

Lemma transf_code_wf' :
  forall l d state ram d',
    map_well_formed d ->
    fold_right (transf_maps state ram) d l = d' ->
    map_well_formed d'.
Proof.
  induction l; intros; simpl in *. inv H0; auto.
  remember (fold_right (transf_maps state ram) d l).
  apply transf_maps_wf in H0. auto. eapply IHl; eauto.
Qed.

Lemma transf_code_wf :
  forall d state ram d',
    map_well_formed d ->
    transf_code state ram d = d' ->
    map_well_formed d'.
Proof. eauto using transf_code_wf'. Qed.

Lemma ram_wf :
  forall x,
    x + 1 < x + 2 /\ x + 2 < x + 3 /\ x + 3 < x + 4 /\ x + 4 < x + 5 /\ x + 5 < x + 6.
Proof. lia. Qed.

Lemma module_ram_wf' :
  forall m addr,
    addr = max_reg_module m + 1 ->
    mod_clk m < addr.
Proof. unfold max_reg_module; lia. Qed.

Definition transf_module (m: module): module.
  refine (
  let max_reg := max_reg_module m in
  let addr := max_reg+1 in
  let en := max_reg+2 in
  let d_in := max_reg+3 in
  let d_out := max_reg+4 in
  let wr_en := max_reg+5 in
  let u_en := max_reg+6 in
  let new_size := (mod_stk_len m) in
  let ram := mk_ram new_size (mod_stk m) en u_en addr wr_en d_in d_out ltac:(eauto using ram_wf) in
  let tc := transf_code (mod_st m) ram (mod_datapath m) in
  match mod_ram m with
  | None =>
    mkmodule m.(mod_params)
                 tc
                 (mod_entrypoint m)
                 (mod_st m)
                 (mod_stk m)
                 (mod_stk_len m)
                 (mod_finish m)
                 (mod_return m)
                 (mod_start m)
                 (mod_reset m)
                 (mod_clk m)
                 (AssocMap.set u_en (None, VScalar 1)
                  (AssocMap.set en (None, VScalar 1)
                   (AssocMap.set wr_en (None, VScalar 1)
                    (AssocMap.set d_out (None, VScalar 32)
                     (AssocMap.set d_in (None, VScalar 32)
                      (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))))
                       (AssocMap.set m.(mod_stk)
                                 (None, VArray 32 (2 ^ Nat.log2_up new_size))%nat m.(mod_arrdecls))
                 (Some ram)
                 _ (mod_ordering_wf m) _ (mod_params_wf m)
  | _ => m
  end).
  eapply transf_code_wf. apply (mod_wf m). destruct tc eqn:?; simpl.
  rewrite <- Heqt. intuition. intuition.
  inversion 1; subst. auto using module_ram_wf'.
Defined.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : program) :=
  transform_program transf_fundef p.

Inductive match_assocmaps : positive -> assocmap -> assocmap -> Prop :=
  match_assocmap: forall p rs rs',
    (forall r, r < p -> rs!r = rs'!r) ->
    match_assocmaps p rs rs'.

Inductive match_arrs : assocmap_arr -> assocmap_arr -> Prop :=
| match_assocmap_arr_intro: forall ar ar',
    (forall s arr,
        ar ! s = Some arr ->
        exists arr',
          ar' ! s = Some arr'
          /\ (forall addr,
                 array_get_error addr arr = array_get_error addr arr')
          /\ arr_length arr = arr_length arr')%nat ->
    (forall s, ar ! s = None -> ar' ! s = None) ->
    match_arrs ar ar'.

Inductive match_arrs_size : assocmap_arr -> assocmap_arr -> Prop :=
  match_arrs_size_intro :
    forall nasa basa,
      (forall s arr,
          nasa ! s = Some arr ->
          exists arr',
            basa ! s = Some arr' /\ arr_length arr = arr_length arr') ->
      (forall s arr,
          basa ! s = Some arr ->
          exists arr',
            nasa ! s = Some arr' /\ arr_length arr = arr_length arr') ->
      (forall s, basa ! s = None <-> nasa ! s = None) ->
      match_arrs_size nasa basa.

Definition match_empty_size (m : module) (ar : assocmap_arr) : Prop :=
  match_arrs_size (empty_stack m.(mod_stk) m.(mod_stk_len)) ar.
#[local] Hint Unfold match_empty_size : mgen.

Definition disable_ram (ram: option ram) (asr : assocmap_reg) : Prop :=
  match ram with
  | Some r => Int.eq (asr # ((ram_en r), 32)) (asr # ((ram_u_en r), 32)) = true
  | None => True
  end.

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr' asa'
      (DISABLE_RAM: disable_ram (mod_ram (transf_module m)) asr')
      (MATCH_ASSOC: match_assocmaps (max_reg_module m + 1) asr asr')
      (MATCH_ARRS: match_arrs asa asa')
      (MATCH_EMPT1: match_empty_size m asa)
      (MATCH_EMPT2: match_empty_size m asa')
      (MATCH_RES: r < mod_st m),
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r (transf_module m) pc asr' asa').

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa'
           (ASSOC: match_assocmaps (max_reg_module m + 1) asr asr')
           (ARRS: match_arrs asa asa')
           (STACKS: list_forall2 match_stackframes res res')
           (ARRS_SIZE: match_empty_size m asa)
           (ARRS_SIZE2: match_empty_size m asa')
           (DISABLE_RAM: disable_ram (mod_ram (transf_module m)) asr'),
      match_states (State res m st asr asa)
                   (State res' (transf_module m) st asr' asa')
| match_returnstate :
    forall res res' i
           (STACKS: list_forall2 match_stackframes res res'),
      match_states (Returnstate res i) (Returnstate res' i)
| match_initial_call :
    forall m,
      match_states (Callstate nil m nil)
                   (Callstate nil (transf_module m) nil).
#[local] Hint Constructors match_states : htlproof.

Definition empty_stack_ram r :=
  AssocMap.set (ram_mem r) (Array.arr_repeat None (ram_size r)) (AssocMap.empty arr).

Definition empty_stack' len st :=
  AssocMap.set st (Array.arr_repeat None len) (AssocMap.empty arr).

Definition match_empty_size' l s (ar : assocmap_arr) : Prop :=
  match_arrs_size (empty_stack' l s) ar.
#[local] Hint Unfold match_empty_size : mgen.

Definition merge_reg_assocs r :=
  Verilog.mkassociations (Verilog.merge_regs (assoc_nonblocking r) (assoc_blocking r)) empty_assocmap.

Definition merge_arr_assocs st len r :=
  Verilog.mkassociations (Verilog.merge_arrs (assoc_nonblocking r) (assoc_blocking r)) (empty_stack' len st).

Inductive match_reg_assocs : positive -> reg_associations -> reg_associations -> Prop :=
  match_reg_association:
    forall p rab rab' ran ran',
      match_assocmaps p rab rab' ->
      match_assocmaps p ran ran' ->
      match_reg_assocs p (mkassociations rab ran) (mkassociations rab' ran').

Inductive match_arr_assocs : arr_associations -> arr_associations -> Prop :=
  match_arr_association:
    forall rab rab' ran ran',
      match_arrs rab rab' ->
      match_arrs ran ran' ->
      match_arr_assocs (mkassociations rab ran) (mkassociations rab' ran').

Ltac mgen_crush := crush; eauto with mgen.

Lemma match_assocmaps_equiv : forall p a, match_assocmaps p a a.
Proof. constructor; auto. Qed.
#[local] Hint Resolve match_assocmaps_equiv : mgen.

Lemma match_arrs_equiv : forall a, match_arrs a a.
Proof. econstructor; mgen_crush. Qed.
#[local] Hint Resolve match_arrs_equiv : mgen.

Lemma match_reg_assocs_equiv : forall p a, match_reg_assocs p a a.
Proof. destruct a; constructor; mgen_crush. Qed.
#[local] Hint Resolve match_reg_assocs_equiv : mgen.

Lemma match_arr_assocs_equiv : forall a, match_arr_assocs a a.
Proof. destruct a; constructor; mgen_crush. Qed.
#[local] Hint Resolve match_arr_assocs_equiv : mgen.

Lemma match_arrs_size_equiv : forall a, match_arrs_size a a.
Proof. intros; repeat econstructor; eauto. Qed.
#[local] Hint Resolve match_arrs_size_equiv : mgen.

Lemma match_stacks_equiv :
  forall m s l,
    mod_stk m = s ->
    mod_stk_len m = l ->
    empty_stack' l s = empty_stack m.(mod_stk) m.(mod_stk_len).
Proof. unfold empty_stack', empty_stack; mgen_crush. Qed.
#[local] Hint Rewrite match_stacks_equiv : mgen.

Lemma match_assocmaps_max1 :
  forall p p' a b,
    match_assocmaps (Pos.max p' p) a b ->
    match_assocmaps p a b.
Proof.
  intros. inv H. constructor. intros.
  apply H0. lia.
Qed.
#[local] Hint Resolve match_assocmaps_max1 : mgen.

Lemma match_assocmaps_max2 :
  forall p p' a b,
    match_assocmaps (Pos.max p p') a b ->
    match_assocmaps p a b.
Proof.
  intros. inv H. constructor. intros.
  apply H0. lia.
Qed.
#[local] Hint Resolve match_assocmaps_max2 : mgen.

Lemma match_assocmaps_ge :
  forall p p' a b,
    match_assocmaps p' a b ->
    p <= p' ->
    match_assocmaps p a b.
Proof.
  intros. inv H. constructor. intros.
  apply H1. lia.
Qed.
#[local] Hint Resolve match_assocmaps_ge : mgen.

Lemma match_reg_assocs_max1 :
  forall p p' a b,
    match_reg_assocs (Pos.max p' p) a b ->
    match_reg_assocs p a b.
Proof. intros; inv H; econstructor; mgen_crush. Qed.
#[local] Hint Resolve match_reg_assocs_max1 : mgen.

Lemma match_reg_assocs_max2 :
  forall p p' a b,
    match_reg_assocs (Pos.max p p') a b ->
    match_reg_assocs p a b.
Proof. intros; inv H; econstructor; mgen_crush. Qed.
#[local] Hint Resolve match_reg_assocs_max2 : mgen.

Lemma match_reg_assocs_ge :
  forall p p' a b,
    match_reg_assocs p' a b ->
    p <= p' ->
    match_reg_assocs p a b.
Proof. intros; inv H; econstructor; mgen_crush. Qed.
#[local] Hint Resolve match_reg_assocs_ge : mgen.

Definition forall_ram (P: reg -> Prop) ram :=
  P (ram_en ram)
  /\ P (ram_u_en ram)
  /\ P (ram_addr ram)
  /\ P (ram_wr_en ram)
  /\ P (ram_d_in ram)
  /\ P (ram_d_out ram).

Lemma forall_ram_lt :
  forall m r,
    (mod_ram m) = Some r ->
    forall_ram (fun x => x < max_reg_module m + 1) r.
Proof.
  assert (X: forall a b c, a < b + 1 -> a < Pos.max c b + 1) by lia.
  unfold forall_ram; simplify; unfold DHTL.max_reg_module; repeat apply X;
  unfold DHTL.max_reg_ram; rewrite H; try lia.
Qed.
#[local] Hint Resolve forall_ram_lt : mgen.

Definition exec_all d_s c_s rs1 ar1 rs3 ar3 :=
  exists f rs2 ar2,
    stmnt_runp f rs1 ar1 c_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 d_s rs3 ar3.

Definition exec_all_ram r d_s c_s rs1 ar1 rs4 ar4 :=
  exists f rs2 ar2 rs3 ar3,
    stmnt_runp f rs1 ar1 c_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 d_s rs3 ar3
    /\ exec_ram (merge_reg_assocs rs3) (merge_arr_assocs (ram_mem r) (ram_size r) ar3) (Some r) rs4 ar4.

(* This is not actually correct. *)
(* Lemma merge_reg_idempotent : *)
(*   forall rs p,  *)
(*     match_reg_assocs p (merge_reg_assocs (merge_reg_assocs rs)) (merge_reg_assocs rs). *)
(* Proof. intros. unfold merge_reg_assocs. cbn. unfold merge_regs.  *)
(* #[global] Hint Rewrite merge_reg_idempotent : mgen. *)

Ltac simplify_local := intros; unfold_constants; cbn in *;
                         repeat (nicify_hypotheses; nicify_goals; kill_bools; substpp);
                         cbn in *.

Ltac simplify_val := repeat (simplify_local; unfold uvalueToZ, valueToPtr, Ptrofs.of_int, valueToInt, intToValue,
                               ptrToValue in *).

Ltac crush_val := simplify_val; try discriminate; try congruence; try lia; liapp; try assumption.

Ltac crush_local := simplify_local; try discriminate; try congruence; try lia; liapp;
              try assumption; auto.

Ltac mgen_crush_local := crush_local; eauto with mgen.

Lemma merge_arr_idempotent :
  forall ar st len v v',
    (assoc_nonblocking ar)!st = Some v ->
    (assoc_blocking ar)!st = Some v' ->
    arr_length v' = len ->
    arr_length v = len ->
    (assoc_blocking (merge_arr_assocs st len (merge_arr_assocs st len ar)))!st
    = (assoc_blocking (merge_arr_assocs st len ar))!st
    /\ (assoc_nonblocking (merge_arr_assocs st len (merge_arr_assocs st len ar)))!st
       = (assoc_nonblocking (merge_arr_assocs st len ar))!st.
Proof.
  split; simplify_local; eauto.
  unfold merge_arrs.
  rewrite AssocMap.gcombine by reflexivity.
  unfold empty_stack'.
  rewrite AssocMap.gss.
  setoid_rewrite merge_arr_empty2; auto.
  rewrite AssocMap.gcombine by reflexivity.
  unfold merge_arr, arr.
  rewrite H. rewrite H0. auto.
  unfold combine.
  simplify_local.
  rewrite list_combine_length.
  rewrite (arr_wf v). rewrite (arr_wf v').
  lia.
Qed.

Lemma empty_arr :
  forall m s,
    (exists l, (empty_stack m.(mod_stk) m.(mod_stk_len)) ! s = Some (arr_repeat None l))
    \/ (empty_stack m.(mod_stk) m.(mod_stk_len)) ! s = None.
Proof.
  unfold empty_stack. simplify.
  destruct (Pos.eq_dec s (mod_stk m)); subst.
  left. eexists. apply AssocMap.gss.
  right. rewrite AssocMap.gso; auto.
Qed.

Lemma merge_arr_empty':
  forall m ar s v,
    match_empty_size m ar ->
    (merge_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) ar) ! s = v ->
    ar ! s = v.
Proof.
  inversion 1; subst.
  pose proof (empty_arr m s).
  simplify_local.
  destruct (merge_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) ar) ! s eqn:?; subst.
  - inv H3. inv H4.
    learn H3 as H5. apply H0 in H5. inv H5. simplify_local.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H3 in Heqo. erewrite merge_arr_empty2 in Heqo. auto. eauto.
    rewrite list_repeat_len in H6. auto.
    learn H4 as H6. apply H2 in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H4 in Heqo. unfold Verilog.arr in *. rewrite H6 in Heqo.
    discriminate.
  - inv H3. inv H4. learn H3 as H4. apply H0 in H4. inv H4. simplify_local.
    rewrite list_repeat_len in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto. rewrite H3 in Heqo.
    unfold Verilog.arr in *. rewrite H4 in Heqo.
    discriminate.
    apply H2 in H4; auto.
Qed.

Lemma merge_arr_empty :
  forall m ar ar',
    match_empty_size m ar ->
    match_arrs ar ar' ->
    match_arrs (merge_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) ar) ar'.
Proof.
  inversion 1; subst; inversion 1; subst;
  econstructor; intros; apply merge_arr_empty' in H6; auto.
Qed.
#[local] Hint Resolve merge_arr_empty : mgen.

Lemma merge_arr_empty'':
  forall m ar s v,
    match_empty_size m ar ->
    ar ! s = v ->
    (merge_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) ar) ! s = v.
Proof.
  inversion 1; subst.
  pose proof (empty_arr m s).
  simplify_local.
  destruct (merge_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) ar) ! s eqn:?; subst.
  - inv H3. inv H4.
    learn H3 as H5. apply H0 in H5. inv H5. simplify_local.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H3 in Heqo. erewrite merge_arr_empty2 in Heqo. auto. eauto.
    rewrite list_repeat_len in H6. auto.
    learn H4 as H6. apply H2 in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H4 in Heqo. unfold Verilog.arr in *. rewrite H6 in Heqo.
    discriminate.
  - inv H3. inv H4. learn H3 as H4. apply H0 in H4. inv H4. simplify_local.
    rewrite list_repeat_len in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto. rewrite H3 in Heqo.
    unfold Verilog.arr in *. rewrite H4 in Heqo.
    discriminate.
    apply H2 in H4; auto.
Qed.

Lemma merge_arr_empty_match :
  forall m ar,
    match_empty_size m ar ->
    match_empty_size m (merge_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) ar).
Proof.
  inversion 1; subst.
  constructor; simplify_local.
  learn H3 as H4. apply H0 in H4. inv H4. simplify_local.
  eexists; split; eauto. apply merge_arr_empty''; eauto.
  apply merge_arr_empty' in H3; auto.
  split; simplify_local.
  unfold merge_arrs in H3. rewrite AssocMap.gcombine in H3; auto.
  unfold merge_arr in *.
  destruct (empty_stack m.(mod_stk) m.(mod_stk_len)) ! s eqn:?;
           destruct ar ! s; try discriminate; eauto.
  apply merge_arr_empty''; auto. apply H2 in H3; auto.
Qed.
#[local] Hint Resolve merge_arr_empty_match : mgen.

Definition ram_present {A: Type} ar r v v' :=
  (assoc_nonblocking ar)!(ram_mem r) = Some v
  /\ @arr_length A v = ram_size r
  /\ (assoc_blocking ar)!(ram_mem r) = Some v'
  /\ arr_length v' = ram_size r.

Lemma find_assoc_get :
  forall rs r trs,
    rs ! r = trs ! r ->
    rs # r = trs # r.
Proof.
  intros; unfold find_assocmap, AssocMapExt.get_default; rewrite H; auto.
Qed.
#[local] Hint Resolve find_assoc_get : mgen.

Lemma find_assoc_get2 :
  forall rs p r v trs,
    (forall r, r < p -> rs ! r = trs ! r) ->
    r < p ->
    rs # r = v ->
    trs # r = v.
Proof.
  intros; unfold find_assocmap, AssocMapExt.get_default; rewrite <- H; auto.
Qed.
#[local] Hint Resolve find_assoc_get2 : mgen.

Lemma get_assoc_gt :
  forall A (rs : AssocMap.t A) p r v trs,
    (forall r, r < p -> rs ! r = trs ! r) ->
    r < p ->
    rs ! r = v ->
    trs ! r = v.
Proof. intros. rewrite <- H; auto. Qed.
#[local] Hint Resolve get_assoc_gt : mgen.

Lemma expr_runp_matches :
  forall f rs ar e v,
    expr_runp f rs ar e v ->
    forall trs tar,
      match_assocmaps (max_reg_expr e + 1) rs trs ->
      match_arrs ar tar ->
      expr_runp f trs tar e v.
Proof.
  induction 1.
  - intros. econstructor.
  - intros. econstructor. inv H0. symmetry.
    apply find_assoc_get.
    apply H2. crush.
  - intros. econstructor. apply IHexpr_runp; eauto.
    inv H1. constructor. simplify.
    assert (forall a b c, a < b + 1 -> a < Pos.max c b + 1) by lia.
    eapply H4 in H1. eapply H3 in H1. auto.
    inv H2.
    unfold arr_assocmap_lookup in *.
    destruct (stack ! r) eqn:?; [|discriminate].
    inv H1.
    inv H0.
    eapply H3 in Heqo. inv Heqo. inv H0.
    unfold arr in *. rewrite H1. inv H5.
    rewrite H0. auto.
  - intros. econstructor; eauto. eapply IHexpr_runp1; eauto.
    econstructor. inv H2. intros.
    assert (forall a b c, a < b + 1 -> a < Pos.max b c + 1) by lia.
    simplify.
    eapply H5 in H2. apply H4 in H2. auto.
    apply IHexpr_runp2; eauto.
    econstructor. inv H2. intros.
    assert (forall a b c, a < b + 1 -> a < Pos.max c b + 1) by lia.
    simplify. eapply H5 in H2. apply H4 in H2. auto.
  - intros. econstructor; eauto.
  - intros. econstructor; eauto. apply IHexpr_runp1; eauto.
    constructor. inv H2. intros. simplify.
    assert (forall a b c, a < b + 1 -> a < Pos.max b c + 1) by lia.
    eapply H5 in H2. apply H4 in H2. auto.
    apply IHexpr_runp2; eauto. simplify.
    assert (forall a b c d, a < b + 1 -> a < Pos.max c (Pos.max b d) + 1) by lia.
    constructor. intros. eapply H4 in H5. inv H2. apply H6 in H5. auto.
  - intros. eapply erun_Vternary_false. apply IHexpr_runp1; eauto. constructor. inv H2.
    intros. simplify. assert (forall a b c, a < b + 1 -> a < Pos.max b c + 1) by lia.
    eapply H5 in H2. apply H4 in H2. auto.
    apply IHexpr_runp2; eauto. econstructor. inv H2. simplify.
    assert (forall a b c d, a < b + 1 -> a < Pos.max c (Pos.max d b) + 1) by lia.
    eapply H5 in H2. apply H4 in H2. auto. auto.
  - intros. econstructor. apply IHexpr_runp; eauto. constructor. inv H3.
    intros. simplify. assert (forall a b c, a < b + 1 -> a < Pos.max b c + 1) by lia.
    eapply H1 in H0. eapply H5. instantiate (1:=1) in H0. lia. eauto. eauto.
    inv H3.
    intros. simplify. assert (forall a b c, a < b + 1 -> a < Pos.max b c + 1) by lia.
    unfold "#". unfold AssocMapExt.get_default. rewrite H5. auto. lia.
Qed.
#[local] Hint Resolve expr_runp_matches : mgen.

Lemma expr_runp_matches2 :
  forall f rs ar e v p,
    expr_runp f rs ar e v ->
    max_reg_expr e < p ->
    forall trs tar,
      match_assocmaps p rs trs ->
      match_arrs ar tar ->
      expr_runp f trs tar e v.
Proof.
  intros. eapply expr_runp_matches; eauto.
  assert (max_reg_expr e + 1 <= p) by lia.
  mgen_crush.
Qed.
#[local] Hint Resolve expr_runp_matches2 : mgen.

Lemma match_assocmaps_gss :
  forall p rab rab' r rhsval,
    match_assocmaps p rab rab' ->
    match_assocmaps p rab # r <- rhsval rab' # r <- rhsval.
Proof.
  intros. inv H. econstructor.
  intros.
  unfold find_assocmap. unfold AssocMapExt.get_default.
  destruct (Pos.eq_dec r r0); subst.
  repeat rewrite PTree.gss; auto.
  repeat rewrite PTree.gso; auto.
Qed.
#[local] Hint Resolve match_assocmaps_gss : mgen.

Lemma match_assocmaps_gt :
  forall p s ra ra' v,
    p <= s ->
    match_assocmaps p ra ra' ->
    match_assocmaps p ra (ra' # s <- v).
Proof.
  intros. inv H0. constructor.
  intros. rewrite AssocMap.gso; try lia. apply H1; auto.
Qed.
#[local] Hint Resolve match_assocmaps_gt : mgen.

Lemma match_reg_assocs_block :
  forall p rab rab' r rhsval,
    match_reg_assocs p rab rab' ->
    match_reg_assocs p (block_reg r rab rhsval) (block_reg r rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
#[local] Hint Resolve match_reg_assocs_block : mgen.

Lemma match_reg_assocs_nonblock :
  forall p rab rab' r rhsval,
    match_reg_assocs p rab rab' ->
    match_reg_assocs p (nonblock_reg r rab rhsval) (nonblock_reg r rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
#[local] Hint Resolve match_reg_assocs_nonblock : mgen.

Lemma some_inj :
  forall A (x: A) y,
    Some x = Some y ->
    x = y.
Proof. inversion 1; auto. Qed.

Lemma arrs_present :
  forall r i v ar arr,
    (arr_assocmap_set r i v ar) ! r = Some arr ->
    exists b, ar ! r = Some b.
Proof.
  intros. unfold arr_assocmap_set in *.
  destruct ar!r eqn:?.
  rewrite AssocMap.gss in H.
  inv H. eexists. auto. rewrite Heqo in H. discriminate.
Qed.

Ltac inv_exists :=
  match goal with
  | H: exists _, _ |- _ => inv H
  end.

Lemma array_get_error_bound_gt :
  forall A i (a : Array A),
    (i >= arr_length a)%nat ->
    array_get_error i a = None.
Proof.
  intros. unfold array_get_error.
  apply nth_error_None. destruct a. simplify.
  lia.
Qed.
#[local] Hint Resolve array_get_error_bound_gt : mgen.

Lemma array_get_error_each :
  forall A addr i (v : A) a x,
    arr_length a = arr_length x ->
    array_get_error addr a = array_get_error addr x ->
    array_get_error addr (array_set i v a) = array_get_error addr (array_set i v x).
Proof.
  intros.
  destruct (Nat.eq_dec addr i); subst.
  destruct (lt_dec i (arr_length a)).
  repeat rewrite array_get_error_set_bound; auto.
  rewrite <- H. auto.
  apply Nat.nlt_ge in n.
  repeat rewrite array_get_error_bound_gt; auto.
  rewrite <- array_set_len. rewrite <- H. lia.
  repeat rewrite array_gso; auto.
Qed.
#[local] Hint Resolve array_get_error_each : mgen.

Lemma match_arrs_gss :
  forall ar ar' r v i,
    match_arrs ar ar' ->
    match_arrs (arr_assocmap_set r i v ar) (arr_assocmap_set r i v ar').
Proof.
  Ltac mag_tac :=
    match goal with
    | H: ?ar ! _ = Some _, H2: forall s arr, ?ar ! s = Some arr -> _ |- _ =>
      let H3 := fresh "H" in
      learn H as H3; apply H2 in H3; inv_exists; simplify
    | H: ?ar ! _ = None, H2: forall s, ?ar ! s = None -> _ |- _ =>
      let H3 := fresh "H" in
      learn H as H3; apply H2 in H3; inv_exists; simplify
    | H: ?ar ! _ = _ |- context[match ?ar ! _ with _ => _ end] =>
      unfold Verilog.arr in *; rewrite H
    | H: ?ar ! _ = _, H2: context[match ?ar ! _ with _ => _ end] |- _ =>
      unfold Verilog.arr in *; rewrite H in H2
    | H: context[(_ # ?s <- _) ! ?s] |- _ => rewrite AssocMap.gss in H
    | H: context[(_ # ?r <- _) ! ?s], H2: ?r <> ?s |- _ => rewrite AssocMap.gso in H; auto
    | |- context[(_ # ?s <- _) ! ?s] => rewrite AssocMap.gss
    | H: ?r <> ?s |- context[(_ # ?r <- _) ! ?s] => rewrite AssocMap.gso; auto
    end.
  intros.
  inv H. econstructor; simplify.
  destruct (Pos.eq_dec r s); subst.
  - unfold arr_assocmap_set, Verilog.arr in *.
    destruct ar!s eqn:?.
    mag_tac.
    econstructor; simplify.
    repeat mag_tac; auto.
    intros. repeat mag_tac. simplify.
    apply array_get_error_each; auto.
    repeat mag_tac; crush.
    repeat mag_tac; crush.
  - unfold arr_assocmap_set in *.
    destruct ar ! r eqn:?. rewrite AssocMap.gso in H; auto.
    apply H0 in Heqo. apply H0 in H. repeat inv_exists. simplify.
    econstructor. unfold Verilog.arr in *. rewrite H3. simplify.
    rewrite AssocMap.gso; auto. eauto. intros. auto. auto.
    apply H1 in Heqo. apply H0 in H. repeat inv_exists; simplify.
    econstructor. unfold Verilog.arr in *. rewrite Heqo. simplify; eauto.
  - destruct (Pos.eq_dec r s); unfold arr_assocmap_set, Verilog.arr in *; simplify; subst.
    destruct ar!s eqn:?; repeat mag_tac; crush.
    apply H1 in H. mag_tac; crush.
    destruct ar!r eqn:?; repeat mag_tac; crush.
    apply H1 in Heqo. repeat mag_tac; auto.
Qed.
#[local] Hint Resolve match_arrs_gss : mgen.

Lemma match_arr_assocs_block :
  forall rab rab' r i rhsval,
    match_arr_assocs rab rab' ->
    match_arr_assocs (block_arr r i rab rhsval) (block_arr r i rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
#[local] Hint Resolve match_arr_assocs_block : mgen.

Lemma match_arr_assocs_nonblock :
  forall rab rab' r i rhsval,
    match_arr_assocs rab rab' ->
    match_arr_assocs (nonblock_arr r i rab rhsval) (nonblock_arr r i rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
#[local] Hint Resolve match_arr_assocs_nonblock : mgen.

Lemma match_states_same :
  forall f rs1 ar1 c rs2 ar2 p,
    stmnt_runp f rs1 ar1 c rs2 ar2 ->
    max_reg_stmnt c < p ->
    forall trs1 tar1,
      match_reg_assocs p rs1 trs1 ->
      match_arr_assocs ar1 tar1 ->
      exists trs2 tar2,
        stmnt_runp f trs1 tar1 c trs2 tar2
        /\ match_reg_assocs p rs2 trs2
        /\ match_arr_assocs ar2 tar2.
Proof.
  Ltac match_states_same_facts :=
    match goal with
    | H: match_reg_assocs _ _ _ |- _ =>
      let H2 := fresh "H" in
      learn H as H2; inv H2
    | H: match_arr_assocs _ _ |- _ =>
      let H2 := fresh "H" in
      learn H as H2; inv H2
    | H1: context[exists _, _], H2: context[exists _, _] |- _ =>
      learn H1; learn H2;
      exploit H1; mgen_crush; exploit H2; mgen_crush
    | H1: context[exists _, _] |- _ =>
      learn H1; exploit H1; mgen_crush
    end.
  Ltac match_states_same_tac :=
    match goal with
    | |- exists _, _ => econstructor
    | |- _ < _ => lia
    | H: context[_ <> _] |- stmnt_runp _ _ _ (Vcase _ (Stmntcons _ _ _) _) _ _ =>
      eapply stmnt_runp_Vcase_nomatch
    | |- stmnt_runp _ _ _ (Vcase _ (Stmntcons _ _ _) _) _ _ =>
      eapply stmnt_runp_Vcase_match
    | H: valueToBool _ = false |- stmnt_runp _ _ _ _ _ _ =>
      eapply stmnt_runp_Vcond_false
    | |- stmnt_runp _ _ _ _ _ _ => econstructor
    | |- expr_runp _ _ _ _ _ => eapply expr_runp_matches2
    end; mgen_crush; try lia.
  induction 1; simplify; repeat match_states_same_facts;
    try destruct_match; try solve [repeat match_states_same_tac].
  - inv H. exists (block_reg r {| assoc_blocking := rab'; assoc_nonblocking := ran' |} rhsval);
      repeat match_states_same_tac; econstructor.
  - exists (nonblock_reg r {| assoc_blocking := rab'; assoc_nonblocking := ran' |} rhsval);
      repeat match_states_same_tac; inv H; econstructor.
  - econstructor. exists (block_arr r i {| assoc_blocking := rab'0; assoc_nonblocking := ran'0 |} rhsval).
    simplify; repeat match_states_same_tac. inv H. econstructor.
    repeat match_states_same_tac. eauto. mgen_crush.
  - econstructor. exists (nonblock_arr r i {| assoc_blocking := rab'0; assoc_nonblocking := ran'0 |} rhsval).
    simplify; repeat match_states_same_tac. inv H. econstructor.
    repeat match_states_same_tac. eauto. mgen_crush.
Qed.

Lemma match_reg_assocs_merge :
  forall p rs rs',
    match_reg_assocs p rs rs' ->
    match_reg_assocs p (merge_reg_assocs rs) (merge_reg_assocs rs').
Proof.
  inversion 1.
  econstructor; econstructor; crush. inv H3.  inv H.
  inv H7. inv H9.
  unfold merge_regs.
  destruct (ran!r) eqn:?; destruct (rab!r) eqn:?.
  erewrite AssocMapExt.merge_correct_1; eauto.
  erewrite AssocMapExt.merge_correct_1; eauto.
  rewrite <- H2; eauto.
  erewrite AssocMapExt.merge_correct_1; eauto.
  erewrite AssocMapExt.merge_correct_1; eauto.
  rewrite <- H2; eauto.
  erewrite AssocMapExt.merge_correct_2; eauto.
  erewrite AssocMapExt.merge_correct_2; eauto.
  rewrite <- H2; eauto.
  rewrite <- H; eauto.
  erewrite AssocMapExt.merge_correct_3; eauto.
  erewrite AssocMapExt.merge_correct_3; eauto.
  rewrite <- H2; eauto.
  rewrite <- H; eauto.
Qed.
#[local] Hint Resolve match_reg_assocs_merge : mgen.

Lemma transf_not_changed :
  forall state ram n d i d_s,
    (forall e1 e2 e3 e4 r, d_s <> (Vseq (Vblock (Vvar e1) e2) (Vnonblock (Vvari r e3) e4))) ->
    (forall e1 e2 e3 e4 r, d_s <> (Vseq (Vblock (Vvar e1) e2) (Vnonblock e3 (Vvari r e4)))) ->
    (forall e1 e2 e3 r state' ec, d_s <> (Vseq (Vseq Vskip (Vcond ec (Vblock (Vvari r e1) e2) Vskip)) (Vblock (Vvar state') e3))) ->
    (forall e1 ec r e2 e4 st' e3, d_s <> (Vseq (Vseq Vskip (Vblock (Vvar e1) (Vternary ec (Vvari r e2) (Vvar e4)))) (Vblock (Vvar st') e3))) ->
    d!i = Some d_s ->
    transf_maps state ram (i, n) d = d.
Proof. intros; unfold transf_maps; repeat destruct_match; mgen_crush. Qed.

Lemma transf_not_changed_neq :
  forall state ram n d d' i a d_s,
    transf_maps state ram (a, n) d = d' ->
    d!i = Some d_s ->
    a <> i -> n <> i ->
    d'!i = Some d_s.
Proof.
  unfold transf_maps; intros; repeat destruct_match; subst; mgen_crush;
  repeat (rewrite AssocMap.gso; auto).
Qed.

Lemma forall_gt :
  forall l, Forall (Pos.ge (fold_right Pos.max 1 l)) l.
Proof.
  induction l; auto.
  constructor. inv IHl; simplify; lia.
  simplify. destruct (Pos.max_dec a (fold_right Pos.max 1 l)).
  rewrite e. apply Pos.max_l_iff in e. apply Pos.le_ge in e.
  apply Forall_forall. rewrite Forall_forall in IHl.
  intros.
  assert (X: forall a b c, a >= c -> c >= b -> a >= b) by lia.
  apply X with (b := x) in e; auto.
  rewrite e; auto.
Qed.

Lemma max_index_list :
  forall A (l : list (positive * A)) i d_s,
    In (i, d_s) l ->
    list_norepet (map fst l) ->
    i <= fold_right Pos.max 1 (map fst l).
Proof.
  induction l; crush.
  inv H. inv H0. simplify. lia.
  inv H0.
  let H := fresh "H" in
  assert (H: forall a b c, c <= b -> c <= Pos.max a b) by lia;
  apply H; eapply IHl; eauto.
Qed.

Lemma max_index :
  forall A d i (d_s: A), d ! i = Some d_s -> i <= max_pc d.
Proof.
  unfold max_pc;
  eauto using max_index_list,
  PTree.elements_correct, PTree.elements_keys_norepet.
Qed.

Lemma max_index_2' :
  forall l i, i > fold_right Pos.max 1 l -> Forall (Pos.gt i) l.
Proof. induction l; crush; constructor; [|apply IHl]; lia. Qed.

Lemma max_index_2'' :
  forall l i, Forall (Pos.gt i) l -> ~ In i l.
Proof.
  induction l; crush. unfold not in *.
  intros. inv H0. inv H. lia. eapply IHl.
  inv H. apply H4. auto.
Qed.

Lemma elements_correct_none :
  forall A am k,
    ~ List.In k (List.map (@fst _ A) (AssocMap.elements am)) ->
    AssocMap.get k am = None.
Proof.
  intros. apply AssocMapExt.elements_correct' in H. unfold not in *.
  destruct am ! k eqn:?; auto. exfalso. apply H. eexists. auto.
Qed.
#[local] Hint Resolve elements_correct_none : assocmap.

Lemma max_index_2 :
  forall A (d: AssocMap.t A) i, i > max_pc d -> d ! i = None.
Proof.
  intros. unfold max_pc in *. apply max_index_2' in H.
  apply max_index_2'' in H. apply elements_correct_none. auto.
Qed.

Definition match_prog (p: program) (tp: program) :=
  Linking.match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. unfold transf_program, match_prog.
  apply Linking.match_transform_program.
Qed.

Lemma exec_all_Vskip :
  forall rs ar,
    exec_all Vskip Vskip rs ar rs ar.
Proof.
  unfold exec_all.
  intros. repeat econstructor.
  Unshelve. unfold fext. exact tt.
Qed.

Lemma match_assocmaps_trans:
  forall p rs1 rs2 rs3,
    match_assocmaps p rs1 rs2 ->
    match_assocmaps p rs2 rs3 ->
    match_assocmaps p rs1 rs3.
Proof.
  intros. inv H. inv H0. econstructor; eauto.
  intros. rewrite H1 by auto. auto.
Qed.

Lemma match_reg_assocs_trans:
  forall p rs1 rs2 rs3,
    match_reg_assocs p rs1 rs2 ->
    match_reg_assocs p rs2 rs3 ->
    match_reg_assocs p rs1 rs3.
Proof.
  intros. inv H. inv H0.
  econstructor; eapply match_assocmaps_trans; eauto.
Qed.

Lemma empty_arrs_match :
  forall m,
    match_arrs (empty_stack m.(mod_stk) m.(mod_stk_len)) (empty_stack (transf_module m).(mod_stk) (transf_module m).(mod_stk_len)).
Proof.
  intros;
  unfold empty_stack, transf_module; repeat destruct_match; mgen_crush.
Qed.
#[local] Hint Resolve empty_arrs_match : mgen.

Lemma max_module_stmnts :
  forall m,
    max_stmnt_tree (mod_datapath m) < max_reg_module m + 1.
Proof. intros. unfold max_reg_module. lia. Qed.
#[local] Hint Resolve max_module_stmnts : mgen.

Lemma transf_module_code :
  forall m,
    mod_ram m = None ->
    transf_code (mod_st m)
                {| ram_size := mod_stk_len m;
                   ram_mem := mod_stk m;
                   ram_en := max_reg_module m + 2;
                   ram_addr := max_reg_module m + 1;
                   ram_wr_en := max_reg_module m + 5;
                   ram_d_in := max_reg_module m + 3;
                   ram_d_out := max_reg_module m + 4;
                   ram_u_en := max_reg_module m + 6;
                   ram_ordering := ram_wf (max_reg_module m) |}
                (mod_datapath m)
    = ((mod_datapath (transf_module m))).
Proof. unfold transf_module; intros; repeat destruct_match; crush. Qed.
#[local] Hint Resolve transf_module_code : mgen.

Lemma transf_module_code_ram :
  forall m r, mod_ram m = Some r -> transf_module m = m.
Proof. unfold transf_module; intros; repeat destruct_match; crush. Qed.
#[local] Hint Resolve transf_module_code_ram : mgen.

Lemma mod_reset_lt : forall m, mod_reset m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
#[local] Hint Resolve mod_reset_lt : mgen.

Lemma mod_finish_lt : forall m, mod_finish m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
#[local] Hint Resolve mod_finish_lt : mgen.

Lemma mod_return_lt : forall m, mod_return m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
#[local] Hint Resolve mod_return_lt : mgen.

Lemma mod_start_lt : forall m, mod_start m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
#[local] Hint Resolve mod_start_lt : mgen.

Lemma mod_stk_lt : forall m, mod_stk m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
#[local] Hint Resolve mod_stk_lt : mgen.

Lemma mod_st_lt : forall m, mod_st m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
#[local] Hint Resolve mod_st_lt : mgen.

Lemma mod_reset_modify :
  forall m ar ar' v,
    match_assocmaps (max_reg_module m + 1) ar ar' ->
    ar ! (mod_reset m) = Some v ->
    ar' ! (mod_reset (transf_module m)) = Some v.
Proof.
  inversion 1. intros.
  unfold transf_module; repeat destruct_match; simplify;
  rewrite <- H0; eauto with mgen.
Qed.
#[local] Hint Resolve mod_reset_modify : mgen.

Lemma mod_finish_modify :
  forall m ar ar' v,
    match_assocmaps (max_reg_module m + 1) ar ar' ->
    ar ! (mod_finish m) = Some v ->
    ar' ! (mod_finish (transf_module m)) = Some v.
Proof.
  inversion 1. intros.
  unfold transf_module; repeat destruct_match; simplify;
  rewrite <- H0; eauto with mgen.
Qed.
#[local] Hint Resolve mod_finish_modify : mgen.

Lemma mod_return_modify :
  forall m ar ar' v,
    match_assocmaps (max_reg_module m + 1) ar ar' ->
    ar ! (mod_return m) = Some v ->
    ar' ! (mod_return (transf_module m)) = Some v.
Proof.
  inversion 1. intros.
  unfold transf_module; repeat destruct_match; simplify;
  rewrite <- H0; eauto with mgen.
Qed.
#[local] Hint Resolve mod_return_modify : mgen.

Lemma mod_start_modify :
  forall m ar ar' v,
    match_assocmaps (max_reg_module m + 1) ar ar' ->
    ar ! (mod_start m) = Some v ->
    ar' ! (mod_start (transf_module m)) = Some v.
Proof.
  inversion 1. intros.
  unfold transf_module; repeat destruct_match; simplify;
  rewrite <- H0; eauto with mgen.
Qed.
#[local] Hint Resolve mod_start_modify : mgen.

Lemma mod_st_modify :
  forall m ar ar' v,
    match_assocmaps (max_reg_module m + 1) ar ar' ->
    ar ! (mod_st m) = Some v ->
    ar' ! (mod_st (transf_module m)) = Some v.
Proof.
  inversion 1. intros.
  unfold transf_module; repeat destruct_match; simplify;
  rewrite <- H0; eauto with mgen.
Qed.
#[local] Hint Resolve mod_st_modify : mgen.

Lemma match_arrs_read :
  forall ra ra' addr v mem,
    arr_assocmap_lookup ra mem addr = Some v ->
    match_arrs ra ra' ->
    arr_assocmap_lookup ra' mem addr = Some v.
Proof.
  unfold arr_assocmap_lookup. intros. destruct_match; destruct_match; try discriminate.
  inv H0. eapply H1 in Heqo0. inv Heqo0. simplify. unfold arr in *.
  rewrite H in Heqo. inv Heqo.
  rewrite H0. auto.
  inv H0. eapply H1 in Heqo0. inv Heqo0. inv H0. unfold arr in *.
  rewrite H3 in Heqo. discriminate.
Qed.
#[local] Hint Resolve match_arrs_read : mgen.

Lemma match_reg_implies_equal :
  forall ra ra' p a b c,
    Int.eq (ra # a) (ra # b) = c ->
    a < p -> b < p ->
    match_assocmaps p ra ra' ->
    Int.eq (ra' # a) (ra' # b) = c.
Proof.
  unfold find_assocmap, AssocMapExt.get_default; intros.
  inv H2. destruct (ra ! a) eqn:?; destruct (ra ! b) eqn:?;
  repeat rewrite <- H3 by lia; rewrite Heqo; rewrite Heqo0; auto.
Qed.
#[local] Hint Resolve match_reg_implies_equal : mgen.

Lemma exec_ram_same :
  forall rs1 ar1 ram rs2 ar2 p,
    exec_ram rs1 ar1 (Some ram) rs2 ar2 ->
    forall_ram (fun x => x < p) ram ->
    forall trs1 tar1,
      match_reg_assocs p rs1 trs1 ->
      match_arr_assocs ar1 tar1 ->
      exists trs2 tar2,
        exec_ram trs1 tar1 (Some ram) trs2 tar2
        /\ match_reg_assocs p rs2 trs2
        /\ match_arr_assocs ar2 tar2.
Proof.
  Ltac exec_ram_same_facts :=
    match goal with
    | H: match_reg_assocs _ _ _ |- _ => let H2 := fresh "H" in learn H as H2; inv H2
    | H: match_assocmaps _ _ _ |- _ => let H2 := fresh "H" in learn H as H2; inv H2
    | H: match_arr_assocs _ _ |- _ => let H2 := fresh "H" in learn H as H2; inv H2
    | H: match_arrs _ _ |- _ => let H2 := fresh "H" in learn H as H2; inv H2
    end.
  inversion 1; subst; destruct ram; unfold forall_ram; simplify; repeat exec_ram_same_facts.
  - repeat (econstructor; mgen_crush).
  - do 2 econstructor; simplify;
      [eapply exec_ram_Some_write; [ apply H1 | apply H2 | | | | | ] | | ];
      mgen_crush.
  - do 2 econstructor; simplify; [eapply exec_ram_Some_read | | ];
      repeat (try econstructor; mgen_crush).
Qed.

Lemma match_assocmaps_merge :
  forall p nasr basr nasr' basr',
    match_assocmaps p nasr nasr' ->
    match_assocmaps p basr basr' ->
    match_assocmaps p (merge_regs nasr basr) (merge_regs nasr' basr').
Proof.
  unfold merge_regs.
  intros. inv H. inv H0. econstructor.
  intros.
  destruct nasr ! r eqn:?; destruct basr ! r eqn:?.
  erewrite AssocMapExt.merge_correct_1; mgen_crush.
  erewrite AssocMapExt.merge_correct_1; mgen_crush.
  erewrite AssocMapExt.merge_correct_1; mgen_crush.
  erewrite AssocMapExt.merge_correct_1; mgen_crush.
  erewrite AssocMapExt.merge_correct_2; mgen_crush.
  erewrite AssocMapExt.merge_correct_2; mgen_crush.
  erewrite AssocMapExt.merge_correct_3; mgen_crush.
  erewrite AssocMapExt.merge_correct_3; mgen_crush.
Qed.
#[local] Hint Resolve match_assocmaps_merge : mgen.

Lemma list_combine_nth_error1 :
  forall l l' addr v,
    length l = length l' ->
    nth_error l addr = Some (Some v) ->
    nth_error (list_combine merge_cell l l') addr = Some (Some v).
Proof. induction l; destruct l'; destruct addr; crush. Qed.

Lemma list_combine_nth_error2 :
  forall l' l addr v,
    length l = length l' ->
    nth_error l addr = Some None ->
    nth_error l' addr = Some (Some v) ->
    nth_error (list_combine merge_cell l l') addr = Some (Some v).
Proof. induction l'; try rewrite nth_error_nil in *; destruct l; destruct addr; crush. Qed.

Lemma list_combine_nth_error3 :
  forall l l' addr,
    length l = length l' ->
    nth_error l addr = Some None ->
    nth_error l' addr = Some None ->
    nth_error (list_combine merge_cell l l') addr = Some None.
Proof. induction l; destruct l'; destruct addr; crush. Qed.

Lemma list_combine_nth_error4 :
  forall l l' addr,
    length l = length l' ->
    nth_error l addr = None ->
    nth_error (list_combine merge_cell l l') addr = None.
Proof. induction l; destruct l'; destruct addr; crush. Qed.

Lemma list_combine_nth_error5 :
  forall l l' addr,
    length l = length l' ->
    nth_error l' addr = None ->
    nth_error (list_combine merge_cell l l') addr = None.
Proof. induction l; destruct l'; destruct addr; crush. Qed.

Lemma array_get_error_merge1 :
  forall a a0 addr v,
    arr_length a = arr_length a0 ->
    array_get_error addr a = Some (Some v) ->
    array_get_error addr (combine merge_cell a a0) = Some (Some v).
Proof.
  unfold array_get_error, combine in *; intros;
  apply list_combine_nth_error1; destruct a; destruct a0; crush.
Qed.

Lemma array_get_error_merge2 :
  forall a a0 addr v,
    arr_length a = arr_length a0 ->
    array_get_error addr a0 = Some (Some v) ->
    array_get_error addr a = Some None ->
    array_get_error addr (combine merge_cell a a0) = Some (Some v).
Proof.
  unfold array_get_error, combine in *; intros;
  apply list_combine_nth_error2; destruct a; destruct a0; crush.
Qed.

Lemma array_get_error_merge3 :
  forall a a0 addr,
    arr_length a = arr_length a0 ->
    array_get_error addr a0 = Some None ->
    array_get_error addr a = Some None ->
    array_get_error addr (combine merge_cell a a0) = Some None.
Proof.
  unfold array_get_error, combine in *; intros;
  apply list_combine_nth_error3; destruct a; destruct a0; crush.
Qed.

Lemma array_get_error_merge4 :
  forall a a0 addr,
    arr_length a = arr_length a0 ->
    array_get_error addr a = None ->
    array_get_error addr (combine merge_cell a a0) = None.
Proof.
  unfold array_get_error, combine in *; intros;
  apply list_combine_nth_error4; destruct a; destruct a0; crush.
Qed.

Lemma array_get_error_merge5 :
  forall a a0 addr,
    arr_length a = arr_length a0 ->
    array_get_error addr a0 = None ->
    array_get_error addr (combine merge_cell a a0) = None.
Proof.
  unfold array_get_error, combine in *; intros;
  apply list_combine_nth_error5; destruct a; destruct a0; crush.
Qed.

Lemma match_arrs_merge' :
  forall addr nasa basa arr s x x0 a a0 nasa' basa',
    (AssocMap.combine merge_arr nasa basa) ! s = Some arr ->
    nasa ! s = Some a ->
    basa ! s = Some a0 ->
    nasa' ! s = Some x0 ->
    basa' ! s = Some x ->
    arr_length x = arr_length x0 ->
    array_get_error addr a0 = array_get_error addr x ->
    arr_length a0 = arr_length x ->
    array_get_error addr a = array_get_error addr x0 ->
    arr_length a = arr_length x0 ->
    array_get_error addr arr = array_get_error addr (combine merge_cell x0 x).
Proof.
  intros. rewrite AssocMap.gcombine in H by auto.
  unfold merge_arr in H.
  rewrite H0 in H. rewrite H1 in H. inv H.
  destruct (array_get_error addr a0) eqn:?; destruct (array_get_error addr a) eqn:?.
  destruct o; destruct o0.
  erewrite array_get_error_merge1; eauto. erewrite array_get_error_merge1; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
  erewrite array_get_error_merge2; eauto. erewrite array_get_error_merge2; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
  erewrite array_get_error_merge1; eauto. erewrite array_get_error_merge1; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
  erewrite array_get_error_merge3; eauto. erewrite array_get_error_merge3; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
  erewrite array_get_error_merge4; eauto. erewrite array_get_error_merge4; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
  erewrite array_get_error_merge5; eauto. erewrite array_get_error_merge5; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
  erewrite array_get_error_merge5; eauto. erewrite array_get_error_merge5; eauto.
  rewrite <- H6 in H4. rewrite <- H8 in H4. auto.
Qed.

Lemma match_arrs_merge :
  forall nasa nasa' basa basa',
    match_arrs_size nasa basa ->
    match_arrs nasa nasa' ->
    match_arrs basa basa' ->
    match_arrs (merge_arrs nasa basa) (merge_arrs nasa' basa').
Proof.
  unfold merge_arrs.
  intros. inv H. inv H0. inv H1. econstructor.
  - intros. destruct nasa ! s eqn:?; destruct basa ! s eqn:?; unfold Verilog.arr in *.
    + pose proof Heqo. apply H in Heqo. pose proof Heqo0. apply H0 in Heqo0.
      repeat inv_exists. simplify.
      eexists. simplify. rewrite AssocMap.gcombine; eauto.
      unfold merge_arr. unfold Verilog.arr in *. rewrite H11. rewrite H12. auto.
      intros. eapply match_arrs_merge'; eauto. eapply H2 in H7; eauto.
      inv_exists. simplify. congruence.
      rewrite AssocMap.gcombine in H1; auto. unfold merge_arr in H1.
      rewrite H7 in H1. rewrite H8 in H1. inv H1.
      repeat rewrite combine_length; auto.
      eapply H2 in H7; eauto. inv_exists; simplify; congruence.
      eapply H2 in H7; eauto. inv_exists; simplify; congruence.
    + apply H2 in Heqo; inv_exists; crush.
    + apply H3 in Heqo0; inv_exists; crush.
    + rewrite AssocMap.gcombine in H1 by auto. unfold merge_arr in *.
      rewrite Heqo in H1. rewrite Heqo0 in H1. discriminate.
  - intros. rewrite AssocMap.gcombine in H1 by auto. unfold merge_arr in H1.
    repeat destruct_match; crush.
    rewrite AssocMap.gcombine by auto; unfold merge_arr.
    apply H5 in Heqo. apply H6 in Heqo0.
    unfold Verilog.arr in *.
    rewrite Heqo. rewrite Heqo0. auto.
Qed.
#[local] Hint Resolve match_arrs_merge : mgen.

Lemma match_empty_size_merge :
  forall nasa2 basa2 m,
  match_empty_size m nasa2 ->
  match_empty_size m basa2 ->
  match_empty_size m (merge_arrs nasa2 basa2).
Proof.
  intros. inv H. inv H0. constructor.
  simplify. unfold merge_arrs. rewrite AssocMap.gcombine by auto.
  pose proof H0 as H6. apply H1 in H6. inv_exists; simplify.
  pose proof H0 as H9. apply H in H9. inv_exists; simplify.
  eexists. simplify. unfold merge_arr. unfold Verilog.arr in *. rewrite H6.
  rewrite H9. auto. rewrite H8. symmetry. apply combine_length. congruence.
  intros.
  destruct (nasa2 ! s) eqn:?; destruct (basa2 ! s) eqn:?.
  unfold merge_arrs in H0. rewrite AssocMap.gcombine in H0 by auto.
  unfold merge_arr in *. setoid_rewrite Heqo in H0. setoid_rewrite Heqo0 in H0. inv H0.
  apply H2 in Heqo. apply H4 in Heqo0. repeat inv_exists; simplify.
  eexists. simplify. eauto. rewrite list_combine_length.
  rewrite (arr_wf a). rewrite (arr_wf a0). lia.
  unfold merge_arrs in H0. rewrite AssocMap.gcombine in H0 by auto.
  unfold merge_arr in *.  setoid_rewrite Heqo in H0. setoid_rewrite Heqo0 in H0.
  apply H2 in Heqo. inv_exists; simplify.
  econstructor; eauto.
  unfold merge_arrs in H0. rewrite AssocMap.gcombine in H0 by auto.
  unfold merge_arr in *.  setoid_rewrite Heqo in H0. setoid_rewrite Heqo0 in H0.
  inv H0. apply H4 in Heqo0. inv_exists; simplify. econstructor; eauto.
  unfold merge_arrs in H0. rewrite AssocMap.gcombine in H0 by auto.
  unfold merge_arr in *.  setoid_rewrite Heqo in H0. setoid_rewrite Heqo0 in H0.
  discriminate.
  split; intros.
  unfold merge_arrs in H0. rewrite AssocMap.gcombine in H0 by auto.
  unfold merge_arr in *. repeat destruct_match; crush. apply H5 in Heqo0; auto.
  pose proof H0.
  apply H5 in H0.
  apply H3 in H6. unfold merge_arrs. rewrite AssocMap.gcombine by auto.
  setoid_rewrite H0. setoid_rewrite H6. auto.
Qed.
#[local] Hint Resolve match_empty_size_merge : mgen.

Lemma match_empty_size_match :
  forall m nasa2 basa2,
    match_empty_size m nasa2 ->
    match_empty_size m basa2 ->
    match_arrs_size nasa2 basa2.
Proof.
  Ltac match_empty_size_match_solve :=
    match goal with
    | H: context[forall s arr, ?ar ! s = Some arr -> _], H2: ?ar ! _ = Some _ |- _ =>
      let H3 := fresh "H" in
      learn H; pose proof H2 as H3; apply H in H3; repeat inv_exists
    | H: context[forall s, ?ar ! s = None <-> _], H2: ?ar ! _ = None |- _ =>
      let H3 := fresh "H" in
      learn H; pose proof H2 as H3; apply H in H3
    | H: context[forall s, _ <-> ?ar ! s = None], H2: ?ar ! _ = None |- _ =>
      let H3 := fresh "H" in
      learn H; pose proof H2 as H3; apply H in H3
    | |- exists _, _ => econstructor
    | |- _ ! _ = Some _ => eassumption
    | |- _ = _ => congruence
    | |- _ <-> _ => split
    end; simplify.
  inversion 1; inversion 1; constructor; simplify; repeat match_empty_size_match_solve.
Qed.
#[local] Hint Resolve match_empty_size_match : mgen.

Lemma match_get_merge :
  forall p ran ran' rab rab' s v,
    s < p ->
    match_assocmaps p ran ran' ->
    match_assocmaps p rab rab' ->
    (merge_regs ran rab) ! s = Some v ->
    (merge_regs ran' rab') ! s = Some v.
Proof.
  intros.
  assert (X: match_assocmaps p (merge_regs ran rab) (merge_regs ran' rab')) by auto with mgen.
  inv X. rewrite <- H3; auto.
Qed.
#[local] Hint Resolve match_get_merge : mgen.

Ltac masrp_tac :=
  match goal with
  | H: context[forall s arr, ?ar ! s = Some arr -> _], H2: ?ar ! _ = Some _ |- _ =>
    let H3 := fresh "H" in
    learn H; pose proof H2 as H3; apply H in H3; repeat inv_exists
  | H: context[forall s, ?ar ! s = None <-> _], H2: ?ar ! _ = None |- _ =>
    let H3 := fresh "H" in
    learn H; pose proof H2 as H3; apply H in H3
  | H: context[forall s, _ <-> ?ar ! s = None], H2: ?ar ! _ = None |- _ =>
    let H3 := fresh "H" in
    learn H; pose proof H2 as H3; apply H in H3
  | ra: arr_associations |- _ =>
    let ra1 := fresh "ran" in let ra2 := fresh "rab" in destruct ra as [ra1 ra2]
  | |- _ ! _ = _ => solve [mgen_crush]
  | |- _ = _ => congruence
  | |- _ <> _ => lia
  | H: ?ar ! ?s = _ |- context[match ?ar ! ?r with _ => _ end] => learn H; destruct (Pos.eq_dec s r); subst
  | H: ?ar ! ?s = _ |- context[match ?ar ! ?s with _ => _ end] => setoid_rewrite H
  | |- context[match ?ar ! ?s with _ => _ end] => destruct (ar ! s) eqn:?
  | H: ?s <> ?r |- context[(_ # ?r <- _) ! ?s] => rewrite AssocMap.gso
  | H: ?r <> ?s |- context[(_ # ?r <- _) ! ?s] => rewrite AssocMap.gso
  | |- context[(_ # ?s <- _) ! ?s] => rewrite AssocMap.gss
  | H: context[match ?ar ! ?r with _ => _ end ! ?s] |- _ =>
    destruct (ar ! r) eqn:?; destruct (Pos.eq_dec r s); subst
  | H: ?ar ! ?s = _, H2: context[match ?ar ! ?s with _ => _ end] |- _ =>
    setoid_rewrite H in H2
  | H: context[match ?ar ! ?s with _ => _ end] |- _ => destruct (ar ! s) eqn:?
  | H: ?s <> ?r, H2: context[(_ # ?r <- _) ! ?s] |- _ => rewrite AssocMap.gso in H2
  | H: ?r <> ?s, H2: context[(_ # ?r <- _) ! ?s] |- _ => rewrite AssocMap.gso in H2
  | H: context[(_ # ?s <- _) ! ?s] |- _ => rewrite AssocMap.gss in H
  | |- context[match_empty_size] => constructor
  | |- context[arr_assocmap_set] => unfold arr_assocmap_set
  | H: context[arr_assocmap_set] |- _ => unfold arr_assocmap_set in H
  | |- exists _, _ => econstructor
  | |- _ <-> _ => split
  end; simplify.

Lemma match_empty_assocmap_set :
  forall m r i rhsval asa,
    match_empty_size m asa ->
    match_empty_size m (arr_assocmap_set r i rhsval asa).
Proof.
  inversion 1; subst; simplify.
  constructor. intros.
  repeat masrp_tac.
  intros. do 5 masrp_tac; try solve [repeat masrp_tac].
  apply H1 in H3. inv_exists. simplify.
  econstructor. simplify. apply H3. congruence.
  repeat masrp_tac. destruct (Pos.eq_dec r s); subst.
  rewrite AssocMap.gss in H8. discriminate.
  rewrite AssocMap.gso in H8; auto. apply H2 in H8. auto.
  destruct (Pos.eq_dec r s); subst. apply H1 in H5. inv_exists. simplify.
  rewrite H5 in H8. discriminate.
  rewrite AssocMap.gso; auto.
  apply H2 in H5. auto. apply H2 in H5. auto.
  Unshelve. auto.
Qed.
#[local] Hint Resolve match_empty_assocmap_set : mgen.

Lemma match_arrs_size_stmnt_preserved :
  forall m f rs1 ar1 ar2 c rs2,
    stmnt_runp f rs1 ar1 c rs2 ar2 ->
    match_empty_size m (assoc_nonblocking ar1) ->
    match_empty_size m (assoc_blocking ar1) ->
    match_empty_size m (assoc_nonblocking ar2) /\ match_empty_size m (assoc_blocking ar2).
Proof.
  induction 1; inversion 1; inversion 1; eauto; simplify; try solve [repeat masrp_tac].
  subst. apply IHstmnt_runp2; apply IHstmnt_runp1; auto.
  apply IHstmnt_runp2; apply IHstmnt_runp1; auto.
  apply match_empty_assocmap_set. auto.
  apply match_empty_assocmap_set. auto.
Qed.

Lemma match_arrs_size_stmnt_preserved2 :
  forall m f rs1 na ba na' ba' c rs2,
    stmnt_runp f rs1 {| assoc_nonblocking := na; assoc_blocking := ba |} c rs2
               {| assoc_nonblocking := na'; assoc_blocking := ba' |} ->
    match_empty_size m na ->
    match_empty_size m ba ->
    match_empty_size m na' /\ match_empty_size m ba'.
Proof.
  intros.
  remember ({| assoc_blocking := ba; assoc_nonblocking := na |}) as ar1.
  remember ({| assoc_blocking := ba'; assoc_nonblocking := na' |}) as ar2.
  assert (X1: na' = (assoc_nonblocking ar2)) by (rewrite Heqar2; auto). rewrite X1.
  assert (X2: ba' = (assoc_blocking ar2)) by (rewrite Heqar2; auto). rewrite X2.
  assert (X3: na = (assoc_nonblocking ar1)) by (rewrite Heqar1; auto). rewrite X3 in *.
  assert (X4: ba = (assoc_blocking ar1)) by (rewrite Heqar1; auto). rewrite X4 in *.
  eapply match_arrs_size_stmnt_preserved; mgen_crush.
Qed.
#[local] Hint Resolve match_arrs_size_stmnt_preserved2 : mgen.

Lemma match_arrs_size_ram_preserved :
  forall m rs1 ar1 ar2 ram rs2,
    exec_ram rs1 ar1 ram rs2 ar2 ->
    match_empty_size m (assoc_nonblocking ar1) ->
    match_empty_size m (assoc_blocking ar1) ->
    match_empty_size m (assoc_nonblocking ar2)
    /\ match_empty_size m (assoc_blocking ar2).
Proof.
  induction 1; inversion 1; inversion 1; subst; simplify; try solve [repeat masrp_tac].
  masrp_tac. masrp_tac. solve [repeat masrp_tac].
  masrp_tac. masrp_tac. masrp_tac. masrp_tac. masrp_tac. masrp_tac. masrp_tac.
  masrp_tac. masrp_tac. masrp_tac. masrp_tac. masrp_tac. masrp_tac. masrp_tac.
  masrp_tac. apply H8 in H1; inv_exists; simplify. repeat masrp_tac. auto.
  repeat masrp_tac.
  repeat masrp_tac.
  repeat masrp_tac.
  destruct (Pos.eq_dec (ram_mem r) s); subst; repeat masrp_tac.
  destruct (Pos.eq_dec (ram_mem r) s); subst; repeat masrp_tac.
  apply H9 in H17; auto. apply H9 in H17; auto.
  Unshelve. eauto.
Qed.
#[local] Hint Resolve match_arrs_size_ram_preserved : mgen.

Lemma match_arrs_size_ram_preserved2 :
  forall m rs1 na na' ba ba' ram rs2,
    exec_ram rs1 {| assoc_nonblocking := na; assoc_blocking := ba |} ram rs2
    {| assoc_nonblocking := na'; assoc_blocking := ba' |} ->
    match_empty_size m na -> match_empty_size m ba ->
    match_empty_size m na' /\ match_empty_size m ba'.
Proof.
  intros.
  remember ({| assoc_blocking := ba; assoc_nonblocking := na |}) as ar1.
  remember ({| assoc_blocking := ba'; assoc_nonblocking := na' |}) as ar2.
  assert (X1: na' = (assoc_nonblocking ar2)) by (rewrite Heqar2; auto). rewrite X1.
  assert (X2: ba' = (assoc_blocking ar2)) by (rewrite Heqar2; auto). rewrite X2.
  assert (X3: na = (assoc_nonblocking ar1)) by (rewrite Heqar1; auto). rewrite X3 in *.
  assert (X4: ba = (assoc_blocking ar1)) by (rewrite Heqar1; auto). rewrite X4 in *.
  eapply match_arrs_size_ram_preserved; mgen_crush.
Qed.
#[local] Hint Resolve match_arrs_size_ram_preserved2 : mgen.

Lemma empty_stack_m :
  forall m, empty_stack (mod_stk m) (mod_stk_len m) = empty_stack' (mod_stk_len m) (mod_stk m).
Proof. unfold empty_stack, empty_stack'; mgen_crush. Qed.
#[local] Hint Rewrite empty_stack_m : mgen.

Ltac clear_forall :=
  repeat match goal with
  | H: context[forall _, _] |- _ => clear H
  end.

Lemma list_combine_none :
  forall n l,
    length l = n ->
    list_combine Verilog.merge_cell (list_repeat None n) l = l.
Proof.
  induction n; intros; crush.
  - symmetry. apply length_zero_iff_nil. auto.
  - destruct l; crush.
    rewrite list_repeat_cons.
    crush. f_equal.
    eauto.
Qed.

Lemma combine_none :
  forall n a,
    a.(arr_length) = n ->
    arr_contents (combine Verilog.merge_cell (arr_repeat None n) a) = arr_contents a.
Proof.
  intros.
  unfold combine.
  crush.

  rewrite <- (arr_wf a) in H.
  apply list_combine_none.
  assumption.
Qed.

Lemma combine_none2 :
  forall n a addr,
    arr_length a = n ->
    array_get_error addr (combine Verilog.merge_cell (arr_repeat None n) a)
    = array_get_error addr a.
Proof. intros; auto using array_get_error_equal, combine_none. Qed.

Lemma list_combine_lookup_first :
  forall l1 l2 n,
    length l1 = length l2 ->
    nth_error l1 n = Some None ->
    nth_error (list_combine Verilog.merge_cell l1 l2) n = nth_error l2 n.
Proof.
  induction l1; intros; crush.

  rewrite nth_error_nil in H0.
  discriminate.

  destruct l2 eqn:EQl2. crush.
  simpl in H. inv H.
  destruct n; simpl in *.
  inv H0. simpl. reflexivity.
  eauto.
Qed.

Lemma combine_lookup_first :
  forall a1 a2 n,
    a1.(arr_length) = a2.(arr_length) ->
    array_get_error n a1 = Some None ->
    array_get_error n (combine Verilog.merge_cell a1 a2) = array_get_error n a2.
Proof.
  intros.

  unfold array_get_error in *.
  apply list_combine_lookup_first; eauto.
  rewrite a1.(arr_wf). rewrite a2.(arr_wf).
  assumption.
Qed.

Lemma list_combine_lookup_second :
  forall l1 l2 n x,
    length l1 = length l2 ->
    nth_error l1 n = Some (Some x) ->
    nth_error (list_combine Verilog.merge_cell l1 l2) n = Some (Some x).
Proof.
  induction l1; intros; crush; auto.

  destruct l2 eqn:EQl2. crush.
  simpl in H. inv H.
  destruct n; simpl in *.
  inv H0. simpl. reflexivity.
  eauto.
Qed.

Lemma combine_lookup_second :
  forall a1 a2 n x,
    a1.(arr_length) = a2.(arr_length) ->
    array_get_error n a1 = Some (Some x) ->
    array_get_error n (combine Verilog.merge_cell a1 a2) = Some (Some x).
Proof.
  intros.

  unfold array_get_error in *.
  apply list_combine_lookup_second; eauto.
  rewrite a1.(arr_wf). rewrite a2.(arr_wf).
  assumption.
Qed.

Lemma match_get_arrs2 :
  forall a i v l,
    length a = l ->
    list_combine merge_cell (list_set i (Some v) (list_repeat None l)) a =
    list_combine merge_cell (list_repeat None l) (list_set i (Some v) a).
Proof.
  induction a; crush; subst.
  - destruct i. unfold list_repeat. unfold list_repeat'. auto.
    unfold list_repeat. unfold list_repeat'. auto.
  - destruct i.
    rewrite list_repeat_cons. simplify. auto.
    rewrite list_repeat_cons. simplify. f_equal. apply IHa. auto.
Qed.

Lemma match_get_arrs :
  forall addr i v x4 x x3,
    x4 = arr_length x ->
    x4 = arr_length x3 ->
    array_get_error addr (combine merge_cell (array_set i (Some v) (arr_repeat None x4))
                                  (combine merge_cell x x3))
    = array_get_error addr (combine merge_cell (arr_repeat None x4)
                                    (array_set i (Some v) (combine merge_cell x x3))).
Proof.
  intros. apply array_get_error_equal. unfold combine. simplify.
  destruct x; destruct x3; simplify.
  apply match_get_arrs2. rewrite list_combine_length. subst.
  rewrite H0. lia.
Qed.

Lemma combine_array_set' :
  forall a b i v,
    length a = length b ->
    list_combine merge_cell (list_set i (Some v) a) b =
    list_set i (Some v) (list_combine merge_cell a b).
Proof.
  induction a; simplify; crush.
  - destruct i; crush.
  - destruct i; destruct b; crush.
    f_equal. apply IHa. auto.
Qed.

Lemma combine_array_set :
  forall a b i v addr,
    arr_length a = arr_length b ->
    array_get_error addr (combine merge_cell (array_set i (Some v) a) b)
    = array_get_error addr (array_set i (Some v) (combine merge_cell a b)).
Proof.
  intros. destruct a; destruct b. unfold array_set. simplify.
  unfold array_get_error. simplify. f_equal.
  apply combine_array_set'. crush.
Qed.

Lemma array_get_combine' :
  forall a b a' b' addr,
    length a = length b ->
    length a = length b' ->
    length a = length a' ->
    nth_error a addr = nth_error a' addr ->
    nth_error b addr = nth_error b' addr ->
    nth_error (list_combine merge_cell a b) addr =
    nth_error (list_combine merge_cell a' b') addr.
Proof.
  induction a; crush.
  - destruct b; crush; destruct b'; crush; destruct a'; crush.
  - destruct b; crush; destruct b'; crush; destruct a'; crush;
    destruct addr; crush; apply IHa.
Qed.

Lemma array_get_combine :
  forall a b a' b' addr,
    arr_length a = arr_length b ->
    arr_length a = arr_length b' ->
    arr_length a = arr_length a' ->
    array_get_error addr a = array_get_error addr a' ->
    array_get_error addr b = array_get_error addr b' ->
    array_get_error addr (combine merge_cell a b)
    = array_get_error addr (combine merge_cell a' b').
Proof.
  intros; unfold array_get_error, combine in *; destruct a; destruct b;
  destruct a'; destruct b'; simplify; apply array_get_combine'; crush.
Qed.

Lemma match_empty_size_exists_Some :
  forall m rab s v,
    match_empty_size m rab ->
    rab ! s = Some v ->
    exists v', (empty_stack (mod_stk m) (mod_stk_len m)) ! s = Some v' /\ arr_length v = arr_length v'.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_empty_size_exists_None :
  forall m rab s,
    match_empty_size m rab ->
    rab ! s = None ->
    (empty_stack (mod_stk m) (mod_stk_len m)) ! s = None.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_empty_size_exists_None' :
  forall m rab s,
    match_empty_size m rab ->
    (empty_stack (mod_stk m) (mod_stk_len m)) ! s = None ->
    rab ! s = None.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_empty_size_exists_Some' :
  forall m rab s v,
    match_empty_size m rab ->
    (empty_stack (mod_stk m) (mod_stk_len m)) ! s = Some v ->
    exists v', rab ! s = Some v' /\ arr_length v = arr_length v'.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_arrs_Some :
  forall ra ra' s v,
    match_arrs ra ra' ->
    ra ! s = Some v ->
    exists v', ra' ! s = Some v'
               /\ (forall addr, array_get_error addr v = array_get_error addr v')
               /\ arr_length v = arr_length v'.
Proof. inversion 1; intros; repeat masrp_tac. intros. rewrite H5. auto. Qed.

Lemma match_arrs_None :
  forall ra ra' s,
    match_arrs ra ra' ->
    ra ! s = None ->
    ra' ! s = None.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Ltac learn_next :=
  match goal with
  | H: match_empty_size _ ?rab, H2: ?rab ! _ = Some _ |- _ =>
    let H3 := fresh "H" in
    learn H2 as H3; eapply match_empty_size_exists_Some in H3;
    eauto; inv_exists; simplify
  | H: match_empty_size _ ?rab, H2: ?rab ! _ = None |- _ =>
    let H3 := fresh "H" in
    learn H2 as H3; eapply match_empty_size_exists_None in H3; eauto
  end.

Ltac learn_empty :=
  match goal with
  | H: match_empty_size _ _, H2: (empty_stack _ _) ! _ = Some _ |- _ =>
    let H3 := fresh "H" in
    learn H as H3; eapply match_empty_size_exists_Some' in H3;
    [| eassumption]; inv_exists; simplify
  | H: match_arrs ?ar _, H2: ?ar ! _ = Some _ |- _ =>
    let H3 := fresh "H" in
    learn H as H3; eapply match_arrs_Some in H3;
    [| eassumption]; inv_exists; simplify
  | H: match_empty_size _ _, H2: (empty_stack _ _) ! _ = None |- _ =>
    let H3 := fresh "H" in
    learn H as H3; eapply match_empty_size_exists_None' in H3;
    [| eassumption]; simplify
  end.

Lemma empty_set_none :
  forall m ran rab s i v s0,
    match_empty_size m ran ->
    match_empty_size m rab ->
    (arr_assocmap_set s i v ran) ! s0 = None ->
    (arr_assocmap_set s i v rab) ! s0 = None.
Proof.
  unfold arr_assocmap_set; inversion 1; subst; simplify.
  destruct (Pos.eq_dec s s0); subst.
  destruct ran ! s0 eqn:?.
  rewrite AssocMap.gss in H4. inv H4.
  learn_next. learn_empty. rewrite H6; auto.
  destruct ran ! s eqn:?. rewrite AssocMap.gso in H4.
  learn_next. learn_empty. rewrite H6. rewrite AssocMap.gso.
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end. clear Heqo. clear H5. clear H6.
  learn_next. repeat learn_empty. auto. auto. auto.
  pose proof Heqo. learn_next; repeat learn_empty.
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end.
  pose proof H4. learn_next; repeat learn_empty.
  rewrite H7. auto.
Qed.

Ltac clear_learnt :=
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end.

Lemma match_arrs_size_assoc :
  forall a b,
    match_arrs_size a b ->
    match_arrs_size b a.
Proof. inversion 1; constructor; crush; split; apply H2. Qed.
#[local] Hint Resolve match_arrs_size_assoc : mgen.

Lemma match_arrs_merge_set2 :
  forall rab rab' ran ran' s m i v,
    match_empty_size m rab ->
    match_empty_size m ran ->
    match_empty_size m rab' ->
    match_empty_size m ran' ->
    match_arrs rab rab' ->
    match_arrs ran ran' ->
    match_arrs (merge_arrs (arr_assocmap_set s i v ran) rab)
               (merge_arrs (arr_assocmap_set s i v (empty_stack (mod_stk m) (mod_stk_len m)))
                           (merge_arrs ran' rab')).
Proof.
  simplify.
  constructor; intros.
  unfold arr_assocmap_set in *. destruct (Pos.eq_dec s s0); subst.
  destruct ran ! s0 eqn:?. unfold merge_arrs in *. rewrite AssocMap.gcombine in *; auto.
  learn_next. repeat learn_empty.
  econstructor. simplify. rewrite H6. rewrite AssocMap.gcombine by auto.
  rewrite AssocMap.gss. simplify. setoid_rewrite H9. setoid_rewrite H7. simplify.
  intros. rewrite AssocMap.gss in H5. setoid_rewrite H13 in H5.
  simplify. pose proof (empty_arr m s0). inv H5. inv_exists. setoid_rewrite H5 in H6. inv H6.
  unfold arr_repeat in H8. simplify. rewrite list_repeat_len in H8. rewrite list_repeat_len in H10.
  rewrite match_get_arrs. crush. rewrite combine_none2. rewrite combine_array_set; try congruence.
  apply array_get_error_each. rewrite combine_length; try congruence.
  rewrite combine_length; try congruence.
  apply array_get_combine; crush.
  rewrite <- array_set_len. rewrite combine_length; crush. crush. crush.
  setoid_rewrite H21 in H6; discriminate. rewrite combine_length.
  rewrite <- array_set_len; crush.
  unfold merge_arr in *. rewrite AssocMap.gss in H5. setoid_rewrite H13 in H5.
  inv H5. rewrite combine_length. rewrite <- array_set_len; crush.
  rewrite <- array_set_len; crush.
  rewrite combine_length; crush.
  destruct rab ! s0 eqn:?. learn_next. repeat learn_empty.
  rewrite H11 in Heqo. discriminate.
  unfold merge_arrs in H5. rewrite AssocMap.gcombine in H5; auto. rewrite Heqo in H5.
  rewrite Heqo0 in H5. crush.

  destruct ran ! s eqn:?.
  learn_next. repeat learn_empty. rewrite H6.
  unfold merge_arrs in *. rewrite AssocMap.gcombine in H5; auto.
  rewrite AssocMap.gcombine; auto. rewrite AssocMap.gso in H5; auto.
  rewrite AssocMap.gso; auto.
  destruct ran ! s0 eqn:?.
  learn_next.
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end.
  repeat learn_empty.
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end.
  rewrite AssocMap.gcombine; auto. setoid_rewrite Heqo0 in H5. setoid_rewrite H29 in H5.
  simplify.
  pose proof (empty_arr m s0). inv H5. inv_exists. rewrite H5 in H21. inv H21.
  econstructor. simplify. setoid_rewrite H23. rewrite H25. setoid_rewrite H5.
  simplify. intros. rewrite combine_none2. apply array_get_combine; solve [crush].
  crush. rewrite list_combine_length. rewrite (arr_wf x5). rewrite (arr_wf x6).
  rewrite <- H26. rewrite <- H28. rewrite list_repeat_len. lia. rewrite list_combine_length.
  rewrite (arr_wf a). rewrite (arr_wf x7). rewrite combine_length. rewrite arr_repeat_length.
  rewrite H24. rewrite <- H32. rewrite list_repeat_len. lia.
  rewrite arr_repeat_length. rewrite combine_length. rewrite <- H26. symmetry. apply list_repeat_len.
  congruence.
  rewrite H37 in H21; discriminate.
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end. eapply match_empty_size_exists_None in H0; eauto.
  clear H6. repeat learn_empty. setoid_rewrite Heqo0 in H5.
  setoid_rewrite H29 in H5. discriminate.
  pose proof (match_arrs_merge ran ran' rab rab').
  eapply match_empty_size_match in H; [|apply H0].
  apply H6 in H; auto. inv H. apply H7 in H5. inv_exists. simplify.
  learn_next. rewrite H9. econstructor. simplify.
  apply merge_arr_empty''; mgen_crush.
  auto. auto.
  unfold merge_arrs in *. rewrite AssocMap.gcombine in H5; auto. rewrite AssocMap.gcombine; auto.
  destruct (arr_assocmap_set s i v ran) ! s0 eqn:?; destruct rab ! s0 eqn:?; crush.
  learn_next. repeat learn_empty.
  repeat match goal with
  | H: Learnt _ |- _ => clear H
  end.
  erewrite empty_set_none. rewrite AssocMap.gcombine; auto.
  simplify. rewrite H7. rewrite H8. auto. apply H0. mgen_crush. auto.
Qed.

Definition all_match_empty_size m ar :=
  match_empty_size m (assoc_nonblocking ar) /\ match_empty_size m (assoc_blocking ar).
#[local] Hint Unfold all_match_empty_size : mgen.

Definition match_module_to_ram m ram :=
  ram_size ram = mod_stk_len m /\ ram_mem ram = mod_stk m.
#[local] Hint Unfold match_module_to_ram : mgen.

Lemma zip_range_forall_le :
  forall A (l: list A) n, Forall (Pos.le n) (map snd (zip_range n l)).
Proof.
  induction l; crush; constructor; [lia|].
  assert (forall n x, n+1 <= x -> n <= x) by lia.
  apply Forall_forall. intros. apply H. generalize dependent x.
  apply Forall_forall. apply IHl.
Qed.

(* Lemma transf_code_fold_correct: *)
(*   forall l m state ram d' c' n, *)
(*     fold_right (transf_maps state ram) (mod_datapath m, mod_controllogic m) l = (d', c') -> *)
(*     Forall (fun x => x < n) (map fst l) -> *)
(*     Forall (Pos.le n) (map snd l) -> *)
(*     list_norepet (map fst l) -> *)
(*     list_norepet (map snd l) -> *)
(*     (forall p i c_s rs1 ar1 rs2 ar2 trs1 tar1 d_s, *)
(*         i < n -> *)
(*         all_match_empty_size m ar1 -> *)
(*         all_match_empty_size m tar1 -> *)
(*         match_module_to_ram m ram -> *)
(*         (mod_datapath m)!i = Some d_s -> *)
(*         (mod_controllogic m)!i = Some c_s -> *)
(*         match_reg_assocs p rs1 trs1 -> *)
(*         match_arr_assocs ar1 tar1 -> *)
(*         max_reg_module m < p -> *)
(*         exec_all d_s c_s rs1 ar1 rs2 ar2 -> *)
(*         exists d_s' c_s' trs2 tar2, *)
(*           d'!i = Some d_s' /\ c'!i = Some c_s' *)
(*           /\ exec_all_ram ram d_s' c_s' trs1 tar1 trs2 tar2 *)
(*           /\ match_reg_assocs p (merge_reg_assocs rs2) (merge_reg_assocs trs2) *)
(*           /\ match_arr_assocs (merge_arr_assocs (ram_mem ram) (ram_size ram) ar2) *)
(*                               (merge_arr_assocs (ram_mem ram) (ram_size ram) tar2)). *)
(* Proof. *)
(*   induction l as [| a l IHl]; simplify. *)
(*   - match goal with *)
(*     | H: (_, _) = (_, _) |- _ => inv H *)
(*     end; *)
(*     unfold exec_all in *; repeat inv_exists; simplify. *)
(*     exploit match_states_same; *)
(*     try match goal with *)
(*     | H: stmnt_runp _ _ _ ?c _ _, H2: (mod_controllogic _) ! _ = Some ?c |- _ => apply H *)
(*     end; eauto; mgen_crush; *)
(*     try match goal with *)
(*     | H: (mod_controllogic _) ! _ = Some ?c |- _ => *)
(*       apply max_reg_stmnt_le_stmnt_tree in H; unfold max_reg_module in *; lia *)
(*     end; intros; *)
(*     exploit match_states_same; *)
(*     try match goal with *)
(*     | H: stmnt_runp _ _ _ ?c _ _, H2: (mod_datapath _) ! _ = Some ?c |- _ => apply H *)
(*     end; eauto; mgen_crush; *)
(*     try match goal with *)
(*     | H: (mod_datapath _) ! _ = Some ?c |- _ => *)
(*       apply max_reg_stmnt_le_stmnt_tree in H; unfold max_reg_module in *; lia *)
(*     end; intros; *)
(*     repeat match goal with *)
(*     | |- exists _, _ => eexists *)
(*     end; simplify; eauto; *)
(*     unfold exec_all_ram; *)
(*     repeat match goal with *)
(*     | |- exists _, _ => eexists *)
(*     end; simplify; eauto. *)
(*     constructor. admit. *)
(*   Abort. *)

Lemma empty_stack_transf : forall m, empty_stack (mod_stk (transf_module m)) (mod_stk_len (transf_module m)) = empty_stack (mod_stk m) (mod_stk_len m).
Proof. unfold empty_stack, transf_module; intros; repeat destruct_match; crush. Qed.

Definition alt_unchanged (d d': AssocMap.t stmnt) i := d ! i = d' ! i.

Definition alt_store_cond ram (d d': AssocMap.t stmnt) i :=
  exists e1 e2 y ec state',
    d' ! i = Some (Vseq (Vseq (Vblock (Vvar (ram_u_en ram)) (Vbinop Vxor (Vunop Vneg (Vbinop Vne ec (Vlit (ZToValue 0)))) (Vvar (ram_u_en ram))))
                       (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                             (Vseq (Vblock (Vvar (ram_d_in ram)) (Vternary ec e2 (Vvar (ram_d_in ram))))
                                   (Vblock (Vvar (ram_addr ram)) (Vternary ec e1 (Vvar (ram_addr ram))))))) (Vblock (Vvar state') (Vlit y)))
    /\ d ! i = Some (Vseq (Vseq Vskip (Vcond ec (Vblock (Vvari (ram_mem ram) e1) e2) Vskip)) (Vblock (Vvar state') (Vlit y))).

Definition alt_store ram (d d': AssocMap.t stmnt) i :=
  exists e1 e2 rest,
    d' ! i = Some (Vseq rest (Vseq (Vblock (Vvar (ram_u_en ram)) (Vunop Vnot (Vvar (ram_u_en ram))))
                        (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                              (Vseq (Vblock (Vvar (ram_d_in ram)) e2)
                                    (Vblock (Vvar (ram_addr ram)) e1)))))
    /\ d ! i = Some (Vseq rest (Vnonblock (Vvari (ram_mem ram) e1) e2)).

Definition alt_load_cond state ram (d d': AssocMap.t stmnt) i n :=
  exists ns e1 e2 ec,
    d' ! i = Some (Vseq (Vblock (Vvar state) (Vlit (posToValue n))) (Vseq (Vblock (Vvar (ram_u_en ram)) (Vbinop Vxor (Vunop Vneg (Vbinop Vne ec (Vlit (ZToValue 0)))) (Vvar (ram_u_en ram))))
                 (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                       (Vblock (Vvar (ram_addr ram)) (Vternary ec e2 (Vvar (ram_addr ram)))))))
    /\ d' ! n = Some (Vseq (Vblock (Vvar state) (Vlit ns)) (Vblock (Vvar e1) (Vternary ec (Vvar (ram_d_out ram)) (Vvar e1))))
    /\ d ! i = Some (Vseq (Vseq Vskip (Vblock (Vvar e1) (Vternary ec (Vvari (ram_mem ram) e2) (Vvar e1)))) (Vblock (Vvar state) (Vlit ns)))
    /\ e1 < state
    /\ max_reg_expr e2 < state
    /\ max_reg_expr (Vlit ns) < state
    /\ max_reg_expr ec < state
    /\ (Z.pos n <= Int.max_unsigned)%Z.

Definition alt_load state ram (d d': AssocMap.t stmnt) i n :=
  exists ns e1 e2,
    d' ! i = Some (Vseq (Vblock (Vvar state) (Vlit (posToValue n))) (Vseq (Vblock (Vvar (ram_u_en ram)) (Vunop Vnot (Vvar (ram_u_en ram))))
                        (Vseq (Vblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                              (Vblock (Vvar (ram_addr ram)) e2))))
    /\ d' ! n = Some (Vseq (Vblock (Vvar state) ns) (Vblock (Vvar e1) (Vvar (ram_d_out ram))))
    /\ d ! i = Some (Vseq (Vblock (Vvar state) ns) (Vnonblock (Vvar e1) (Vvari (ram_mem ram) e2)))
    /\ e1 < state
    /\ max_reg_expr e2 < state
    /\ max_reg_expr ns < state
    /\ (Z.pos n <= Int.max_unsigned)%Z.

Definition alternatives state ram d d' i n :=
  alt_unchanged d d' i
  \/ alt_store ram d d' i
  \/ alt_load state ram d d' i n
  \/ alt_store_cond ram d d' i
  \/ alt_load_cond state ram d d' i n.

Lemma transf_alternatives :
  forall ram n d state i d',
    transf_maps state ram (i, n) d = d' ->
    i <> n ->
    alternatives state ram d d' i n.
Proof.
  intros. unfold transf_maps in *.
  repeat destruct_match; subst; try match goal with
                         | H: (_, _) = (_, _) |- _ => inv H
                         end; try solve [left; econstructor; crush]; simplify;
  repeat match goal with
  | H: (_ =? _) = true |- _ => apply Peqb_true_eq in H; subst
  end; unfold alternatives;
  intuition (repeat econstructor; simplify;
  repeat match goal with
         | |- ( _ # ?s <- _ ) ! ?s = Some _ => apply AssocMap.gss
         | |- ( _ # ?s <- _ ) ! ?r = Some _ => rewrite AssocMap.gso by lia
         | |- _ = None => apply max_index_2; lia
         | H: context[_ <? _] |- _ => apply Pos.ltb_lt in H
         end; auto).
Qed.

Lemma transf_alternatives_neq :
  forall state ram a n' n d'' d' i d,
    transf_maps state ram (a, n) d = d' ->
    a <> i -> n' <> n -> i <> n' -> a <> n' ->
    i <> n -> a <> n ->
    alternatives state ram d'' d i n' ->
    alternatives state ram d'' d' i n'.
Proof.
  unfold alternatives, alt_unchanged, alt_store, alt_load, alt_store_cond, alt_load_cond, transf_maps; intros;
  repeat match goal with H: _ \/ _ |- _ => inv H | H: _ /\ _ |- _ => destruct H end;
  intuition
  (repeat inv_exists; simplify;
  repeat destruct_match;
  repeat match goal with
         | H: (_, _) = (_, _) |- _ => inv H
         | |- exists _, _ => econstructor
         end; repeat split; repeat rewrite AssocMap.gso by lia; eauto; lia).
Qed.

Lemma transf_alternatives_neq2 :
  forall state ram a n' n d'' d' i d,
    transf_maps state ram (a, n) d' = d ->
    a <> i -> n' <> n -> i <> n' -> a <> n' -> i <> n ->
    alternatives state ram d d'' i n' ->
    alternatives state ram d' d'' i n'.
Proof.
  unfold alternatives, alt_unchanged, alt_store, alt_load, alt_store_cond, alt_load_cond, transf_maps; intros;
  repeat match goal with H: _ \/ _ |- _ => inv H | H: _ /\ _ |- _ => destruct H end;
  intuition 
  (repeat inv_exists; simplify;
  repeat destruct_match;
  repeat match goal with
         | H: (_, _) = (_, _) |- _ => inv H
         | |- exists _, _ => econstructor
         end; repeat split; repeat rewrite AssocMap.gso in * by lia; eauto; lia).
Qed.

Lemma transf_alt_unchanged_neq :
  forall i d'' d d',
    alt_unchanged d' d'' i ->
    d' ! i = d ! i ->
    alt_unchanged d d'' i.
Proof. unfold alt_unchanged; simplify; congruence. Qed.

Lemma transf_maps_neq :
  forall state ram d i n d' i' n' va vb,
    transf_maps state ram (i, n) d = d' ->
    d ! i' = va -> d ! n' = vb ->
    i <> i' -> i <> n' -> n <> i' -> n <> n' ->
    d' ! i' = va /\ d' ! n' = vb.
Proof.
  unfold transf_maps; intros; repeat destruct_match; simplify;
  repeat match goal with
         | H: (_, _) = (_, _) |- _ => inv H
         | H: (_ =? _) = true |- _ => apply Peqb_true_eq in H; subst
         | |- context[( _ # ?s <- _ ) ! ?r] => rewrite AssocMap.gso by lia
         end; crush.
Qed.

Lemma alternatives_different_map :
  forall l state ram d d'' d' n i p,
    i <= p -> n > p ->
    Forall (Pos.lt p) (map snd l) ->
    Forall (Pos.ge p) (map fst l) ->
    ~ In n (map snd l) ->
    ~ In i (map fst l) ->
    fold_right (transf_maps state ram) d l = d' ->
    alternatives state ram d' d'' i n ->
    alternatives state ram d d'' i n.
Proof.
  Opaque transf_maps.
  induction l; intros.
  - crush.
  - simplify; repeat match goal with
                     | H: context[_ :: _] |- _ => inv H
                     | H: transf_maps _ _ _ (fold_right (transf_maps ?s ?r) (?d, ?c) ?l) = (_, _) |- _ =>
                       let X := fresh "X" in
                       remember (fold_right (transf_maps s r) (d, c) l) as X
                     | X: _ * _ |- _ => destruct X
                     | H: (_, _) = _ |- _ => symmetry in H
                     end; simplify.
    remember p0 as i'. symmetry in Heqi'. subst.
    remember p1 as n'. symmetry in Heqn'. subst.
    assert (i <> n') by lia.
    assert (n <> i') by lia.
    assert (n <> n') by lia.
    assert (i <> i') by lia.
    eapply IHl; eauto.
    eapply transf_alternatives_neq2; eauto; try lia.
Qed.

Lemma transf_fold_alternatives :
  forall l state ram d d' i n d_s,
    fold_right (transf_maps state ram) d l = d' ->
    max_pc d < n ->
    Forall (Pos.lt (max_pc d)) (map snd l) ->
    Forall (Pos.ge (max_pc d)) (map fst l) ->
    list_norepet (map fst l) ->
    list_norepet (map snd l) ->
    In (i, n) l ->
    d ! i = Some d_s ->
    alternatives state ram d d' i n.
Proof.
  Opaque transf_maps.
  induction l; crush; [].
  repeat match goal with
         | H: context[_ :: _] |- _ => inv H
         | H: transf_maps _ _ _ (fold_right (transf_maps ?s ?r) ?d ?l) = (_, _) |- _ =>
           let X := fresh "X" in
           remember (fold_right (transf_maps s r) d l) as X
         | X: _ * _ |- _ => destruct X
         | H: (_, _) = _ |- _ => symmetry in H
         end; subst.
  match goal with H: _ \/ _ |- _ => inv H end.
  match goal with H: (_, _) = (_, _) |- _ => inv H end. simplify.
  eapply alternatives_different_map; eauto.
  simplify; lia. simplify; lia. apply transf_alternatives; auto. lia.
  simplify.
  assert (X: In i (map fst l)). { replace i with (fst (i, n)) by auto. apply in_map; auto. }
  assert (X2: In n (map snd l)). { replace n with (snd (i, n)) by auto. apply in_map; auto. }
  assert (X3: n <> p0). { destruct (Pos.eq_dec n p0); subst; crush. }
  assert (X4: i <> p). { destruct (Pos.eq_dec i p); subst; crush. }
  eapply transf_alternatives_neq; eauto; apply max_index in H6; lia.
  Transparent transf_maps.
Qed.

Lemma zip_range_inv :
  forall A (l: list A) i n,
    In i l ->
    exists n', In (i, n') (zip_range n l) /\ n' >= n.
Proof.
  induction l; crush.
  inv H. econstructor.
  split. left. eauto. lia.
  eapply IHl in H0. inv H0. inv H.
  econstructor. split. right. apply H0. lia.
Qed.

Lemma zip_range_not_in_fst :
  forall A (l: list A) a n, ~ In a l -> ~ In a (map fst (zip_range n l)).
Proof. unfold not; induction l; crush; inv H0; firstorder. Qed.

Lemma zip_range_no_repet_fst :
  forall A (l: list A) a, list_norepet l -> list_norepet (map fst (zip_range a l)).
Proof.
  induction l; simplify; constructor; inv H; firstorder;
  eapply zip_range_not_in_fst; auto.
Qed.

Lemma transf_code_alternatives :
  forall state ram d d' i d_s,
    transf_code state ram d = d' ->
    d ! i = Some d_s ->
    exists n, alternatives state ram d d' i n.
Proof.
  unfold transf_code;
  intros.
  pose proof H0 as X.
  apply PTree.elements_correct in X. assert (In i (map fst (PTree.elements d))).
  { replace i with (fst (i, d_s)) by auto. apply in_map. auto. }
  exploit zip_range_inv. apply H1. intros. inv H2. simplify.
  instantiate (1 := (max_pc d + 1)) in H2.
  exists x.
  eapply transf_fold_alternatives;
  eauto using forall_gt, PTree.elements_keys_norepet, max_index. lia.
  assert (Forall (Pos.le ((max_pc d) + 1))
    (map snd (zip_range ((max_pc d) + 1)
                        (map fst (PTree.elements d))))) by apply zip_range_forall_le.
  apply Forall_forall; intros. eapply Forall_forall in H3; eauto. lia.
  rewrite zip_range_fst_idem. apply Forall_forall; intros.
  apply AssocMapExt.elements_iff in H3. inv H3. apply max_index in H4. lia.
  eapply zip_range_no_repet_fst. apply PTree.elements_keys_norepet.
  eapply zip_range_snd_no_repet.
Qed.

Lemma max_reg_stmnt_not_modified :
  forall s f rs ar rs' ar',
    stmnt_runp f rs ar s rs' ar' ->
    forall r,
      max_reg_stmnt s < r ->
      (assoc_blocking rs) ! r = (assoc_blocking rs') ! r.
Proof.
  induction 1; crush;
  try solve [repeat destruct_match; apply IHstmnt_runp; try lia; auto].
  assert (X: (assoc_blocking asr1) ! r = (assoc_blocking asr2) ! r) by (apply IHstmnt_runp2; lia).
  assert (X2: (assoc_blocking asr0) ! r = (assoc_blocking asr1) ! r) by (apply IHstmnt_runp1; lia).
  congruence.
  inv H. simplify. rewrite AssocMap.gso by lia; auto.
Qed.

Lemma max_reg_stmnt_not_modified_nb :
  forall s f rs ar rs' ar',
    stmnt_runp f rs ar s rs' ar' ->
    forall r,
      max_reg_stmnt s < r ->
      (assoc_nonblocking rs) ! r = (assoc_nonblocking rs') ! r.
Proof.
  induction 1; crush;
  try solve [repeat destruct_match; apply IHstmnt_runp; try lia; auto].
  assert (X: (assoc_nonblocking asr1) ! r = (assoc_nonblocking asr2) ! r) by (apply IHstmnt_runp2; lia).
  assert (X2: (assoc_nonblocking asr0) ! r = (assoc_nonblocking asr1) ! r) by (apply IHstmnt_runp1; lia).
  congruence.
  inv H. simplify. rewrite AssocMap.gso by lia; auto.
Qed.

Lemma int_eq_not_changed :
  forall ar ar' r r2 b,
    Int.eq (ar # r) (ar # r2) = b ->
    ar ! r = ar' ! r ->
    ar ! r2 = ar' ! r2 ->
    Int.eq (ar' # r) (ar' # r2) = b.
Proof.
  unfold find_assocmap, AssocMapExt.get_default. intros.
  rewrite <- H0. rewrite <- H1. auto.
Qed.

Lemma merge_find_assocmap :
  forall ran rab x,
    ran ! x = None ->
    (merge_regs ran rab) # x = rab # x.
Proof.
  unfold merge_regs, find_assocmap, AssocMapExt.get_default.
  intros. destruct (rab ! x) eqn:?.
  erewrite AssocMapExt.merge_correct_2; eauto.
  erewrite AssocMapExt.merge_correct_3; eauto.
Qed.

Lemma max_reg_module_datapath_gt :
  forall m i v p,
    (mod_datapath m) ! i = Some v ->
    max_reg_module m < p ->
    max_reg_stmnt v < p.
Proof.
  intros. unfold max_reg_module in *.
  apply max_reg_stmnt_le_stmnt_tree in H. lia.
Qed.

Lemma merge_arr_empty2 :
  forall m ar ar',
    match_empty_size m ar' ->
    match_arrs ar ar' ->
    match_arrs ar (merge_arrs (empty_stack (mod_stk m) (mod_stk_len m)) ar').
Proof.
  inversion 1; subst; inversion 1; subst.
  econstructor; intros. apply H4 in H6; inv_exists. simplify_local.
  eapply merge_arr_empty'' in H6; eauto.
  apply H5 in H6. pose proof H6. apply H2 in H7.
  unfold merge_arrs. rewrite AssocMap.gcombine; auto. setoid_rewrite H6.
  setoid_rewrite H7. auto.
Qed.
#[local] Hint Resolve merge_arr_empty2 : mgen.

Lemma find_assocmap_gso :
  forall ar x y v, x <> y -> (ar # y <- v) # x = ar # x.
Proof.
  unfold find_assocmap, AssocMapExt.get_default; intros; rewrite AssocMap.gso; auto.
Qed.

Lemma find_assocmap_gss :
  forall ar x v, (ar # x <- v) # x = v.
Proof.
  unfold find_assocmap, AssocMapExt.get_default; intros; rewrite AssocMap.gss; auto.
Qed.

Lemma expr_lt_max_module_datapath :
  forall m x,
    max_reg_stmnt x <= max_stmnt_tree (mod_datapath m) ->
    max_reg_stmnt x < max_reg_module m + 1.
Proof. unfold max_reg_module. lia. Qed.

(* Lemma expr_lt_max_module_controllogic : *)
(*   forall m x, *)
(*     max_reg_stmnt x <= max_stmnt_tree (mod_controllogic m) -> *)
(*     max_reg_stmnt x < max_reg_module m + 1. *)
(* Proof. unfold max_reg_module. lia. Qed. *)

Lemma int_eq_not :
  forall x y, Int.eq x y = true -> Int.eq x (Int.not y) = false.
Proof.
  intros. pose proof (Int.eq_spec x y). rewrite H in H0. subst.
  apply int_eq_not_false.
Qed.

Lemma match_assocmaps_gt2 :
  forall (p s : positive) (ra ra' : assocmap) (v : value),
  p <= s -> match_assocmaps p ra ra' -> match_assocmaps p (ra # s <- v) ra'.
Proof.
  intros; inv H0; constructor; intros.
  destruct (Pos.eq_dec r s); subst. lia.
  rewrite AssocMap.gso by lia. auto.
Qed.

Lemma match_assocmaps_switch_neq :
  forall p ra ra' r v' s v,
    match_assocmaps p ra ((ra' # r <- v') # s <- v) ->
    s <> r ->
    match_assocmaps p ra ((ra' # s <- v) # r <- v').
Proof.
  inversion 1; constructor; simplify.
  destruct (Pos.eq_dec r0 s); destruct (Pos.eq_dec r0 r); subst; try lia.
  rewrite AssocMap.gso by lia. specialize (H0 s). apply H0 in H5.
  rewrite AssocMap.gss in H5. rewrite AssocMap.gss. auto.
  rewrite AssocMap.gss. apply H0 in H5. rewrite AssocMap.gso in H5 by lia.
  rewrite AssocMap.gss in H5. auto.
  repeat rewrite AssocMap.gso by lia.
  apply H0 in H5. repeat rewrite AssocMap.gso in H5 by lia.
  auto.
Qed.

Lemma match_assocmaps_duplicate :
  forall p ra ra' v' s v,
    match_assocmaps p ra (ra' # s <- v) ->
    match_assocmaps p ra ((ra' # s <- v') # s <- v).
Proof.
  inversion 1; constructor; simplify.
  destruct (Pos.eq_dec r s); subst.
  rewrite AssocMap.gss. apply H0 in H4. rewrite AssocMap.gss in H4. auto.
  repeat rewrite AssocMap.gso by lia. apply H0 in H4. rewrite AssocMap.gso in H4 by lia.
  auto.
Qed.

Lemma assocmap_merge_equiv :
  forall A (a: AssocMap.t A) b c d r,
    a ! r = c ! r ->
    b ! r = d ! r ->
    (AssocMapExt.merge _ a b) ! r = (AssocMapExt.merge _ c d) ! r.
Proof.
  intros.
  unfold AssocMapExt.merge. rewrite ! AssocMap.gcombine; auto.
  rewrite H. rewrite H0. auto.
Qed.

Ltac tac0 :=
  repeat match goal with
    | H: match_reg_assocs _ _ _ |- _ => inv H
    | H: match_arr_assocs _ _ |- _ => inv H
    end.

Lemma translation_correct_unchanged :
  forall (m : module)
  (asr : AssocMap.tree value)
  (basr2 nasr2 : AssocMap.t value)
  (nasa2 basa2 : AssocMap.t arr)
  (asr'0 : assocmap_reg)
  (asa'0 : assocmap_arr)
  (res' : list stackframe)
  (st : positive)
  (tge : genv)
  (pstval : positive)
  (sf : list stackframe)
  (asa : AssocMap.t arr)
  (data : stmnt)
  (f : fext)
  (H : asr ! (mod_reset m) = Some (ZToValue 0))
  (H0 : asr ! (mod_finish m) = Some (ZToValue 0))
  (H1 : asr ! (mod_st m) = Some (posToValue st))
  (H2 : (mod_datapath m) ! st = Some data)
  (H3 : stmnt_runp f {| assoc_blocking := asr; assoc_nonblocking := empty_assocmap |}
         {| assoc_blocking := asa; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} data
         {| assoc_blocking := basr2; assoc_nonblocking := nasr2 |}
         {| assoc_blocking := basa2; assoc_nonblocking := nasa2 |})
  (H5 : (merge_regs empty_assocmap (merge_regs nasr2 basr2)) ! (mod_st m) = Some (posToValue pstval))
  (H6 : (Z.pos pstval <= 4294967295)%Z)
  (H8 : mod_ram m = None)
  (ASSOC : match_assocmaps (max_reg_module m + 1) asr asr'0)
  (ARRS : match_arrs asa asa'0)
  (STACKS : list_forall2 match_stackframes sf res')
  (ARRS_SIZE : match_empty_size m asa)
  (ARRS_SIZE2 : match_empty_size m asa'0)
  (DISABLE_RAM : disable_ram (mod_ram (transf_module m)) asr'0)
  (Learn : Learnt H8)
  (x : positive)
  (H7 : alt_unchanged (mod_datapath m) (mod_datapath (transf_module m)) st),
  exists R2 : state,
    Smallstep.plus step tge (State res' (transf_module m) st asr'0 asa'0) Events.E0 R2 /\
    match_states
      (State sf m pstval (merge_regs empty_assocmap (merge_regs nasr2 basr2))
         (merge_arrs (empty_stack (mod_stk m) (mod_stk_len m)) (merge_arrs nasa2 basa2))) R2.
Proof.
  intros.
  unfold alt_unchanged in *; simplify_local.
    assert (MATCH_SIZE2: match_empty_size m nasa2 /\ match_empty_size m basa2).
    { eapply match_arrs_size_stmnt_preserved2; mgen_crush. } simplify_local.
    assert (MATCH_ARR3: match_arrs_size nasa2 basa2) by eauto with mgen.
    exploit match_states_same; try solve [apply H3 | eapply max_stmnt_lt_module; eauto
                                          | econstructor; eauto with mgen];
    intros; repeat inv_exists; simplify_local; try lia; tac0.
    assert (MATCH_SIZE1': match_empty_size m ran'0 /\ match_empty_size m rab'0).
    { eapply match_arrs_size_stmnt_preserved2; eauto. rewrite empty_stack_transf.
      unfold match_empty_size. constructor; intros; intuition eauto. } simplify_local.
    assert (MATCH_ARR3': match_arrs_size ran'0 rab'0) by (eauto with mgen).
    do 2 econstructor. apply Smallstep.plus_one. econstructor.
    eauto with mgen. eauto with mgen. eauto with mgen.
    rewrite <- H7. eassumption.
    eauto.
    rewrite empty_stack_transf. unfold transf_module; repeat destruct_match; try discriminate.
    econstructor. simplify.
    unfold disable_ram in *. unfold transf_module in DISABLE_RAM.
    repeat destruct_match; try discriminate; []. simplify.
    pose proof H11 as R1. apply max_reg_stmnt_not_modified with (r := max_reg_module m + 2) in R1.
    pose proof H11 as R2. eapply max_reg_stmnt_not_modified_nb with (r := max_reg_module m + 2) in R2.
    pose proof H11 as R1'. apply max_reg_stmnt_not_modified with (r := max_reg_module m + 6) in R1'.
    pose proof H11 as R2'. eapply max_reg_stmnt_not_modified_nb with (r := max_reg_module m + 6) in R2'.
    simplify.
    pose proof DISABLE_RAM as DISABLE_RAM1.
    eapply int_eq_not_changed with (ar' := rab') in DISABLE_RAM; try congruence.
    rewrite AssocMap.gempty in R2. rewrite AssocMap.gempty in R2'.
    eapply int_eq_not_changed in DISABLE_RAM; auto. repeat (rewrite merge_find_assocmap; try congruence).
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    auto. auto. eauto with mgen. auto.
    econstructor; mgen_crush_local. apply merge_arr_empty; mgen_crush_local.
    unfold disable_ram in *. unfold transf_module in DISABLE_RAM.
    repeat destruct_match; crush_local. unfold transf_module in Heqo; repeat destruct_match; crush_local.
    pose proof H11 as R1. apply max_reg_stmnt_not_modified with (r := max_reg_module m + 2) in R1; try lia.
    pose proof H11 as R2. eapply max_reg_stmnt_not_modified_nb with (r := max_reg_module m + 2) in R2.
    pose proof H11 as R1'. apply max_reg_stmnt_not_modified with (r := max_reg_module m + 6) in R1'.
    pose proof H11 as R2'. eapply max_reg_stmnt_not_modified_nb with (r := max_reg_module m + 6) in R2'.
    simplify_local.
    pose proof DISABLE_RAM as DISABLE_RAM1.
    eapply int_eq_not_changed with (ar' := rab') in DISABLE_RAM; try congruence.
    unfold empty_assocmap, merge_regs.
    rewrite AssocMap.gempty in R2. rewrite AssocMap.gempty in R2'.
    eapply int_eq_not_changed in DISABLE_RAM; auto. repeat (rewrite merge_find_assocmap; try congruence).
    apply AssocMap.gempty. apply AssocMap.gempty.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
    eapply max_reg_module_datapath_gt; eauto; remember (max_reg_module m); lia.
Qed.

Lemma translation_correct_store :
  forall (m : module)
  (asr : AssocMap.tree value)
  (basr2 nasr2 : AssocMap.t value)
  (nasa2 basa2 : AssocMap.t arr)
  (asr'0 : assocmap_reg)
  (asa'0 : assocmap_arr)
  (res' : list stackframe)
  (st : positive)
  (tge : genv)
  (pstval : positive)
  (sf : list stackframe)
  (asa : AssocMap.t arr)
  (data : stmnt)
  (f : fext)
  (H : asr ! (mod_reset m) = Some (ZToValue 0))
  (H0 : asr ! (mod_finish m) = Some (ZToValue 0))
  (H1 : asr ! (mod_st m) = Some (posToValue st))
  (H2 : (mod_datapath m) ! st = Some data)
  (H3 : stmnt_runp f {| assoc_blocking := asr; assoc_nonblocking := empty_assocmap |}
         {| assoc_blocking := asa; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} data
         {| assoc_blocking := basr2; assoc_nonblocking := nasr2 |}
         {| assoc_blocking := basa2; assoc_nonblocking := nasa2 |})
  (H5 : (merge_regs empty_assocmap (merge_regs nasr2 basr2)) ! (mod_st m) = Some (posToValue pstval))
  (H6 : (Z.pos pstval <= 4294967295)%Z)
  (H8 : mod_ram m = None)
  (ASSOC : match_assocmaps (max_reg_module m + 1) asr asr'0)
  (ARRS : match_arrs asa asa'0)
  (STACKS : list_forall2 match_stackframes sf res')
  (ARRS_SIZE : match_empty_size m asa)
  (ARRS_SIZE2 : match_empty_size m asa'0)
  (DISABLE_RAM : disable_ram (mod_ram (transf_module m)) asr'0)
  (Learn : Learnt H8)
  (x : positive)
  (H4 : alt_store
         {|
           ram_size := mod_stk_len m;
           ram_mem := mod_stk m;
           ram_en := max_reg_module m + 2;
           ram_u_en := max_reg_module m + 6;
           ram_addr := max_reg_module m + 1;
           ram_wr_en := max_reg_module m + 5;
           ram_d_in := max_reg_module m + 3;
           ram_d_out := max_reg_module m + 4;
           ram_ordering := ram_wf (max_reg_module m)
         |} (mod_datapath m) (mod_datapath (transf_module m)) st),
  exists R2 : state,
    Smallstep.plus step tge (State res' (transf_module m) st asr'0 asa'0) Events.E0 R2 /\
    match_states
      (State sf m pstval (merge_regs empty_assocmap (merge_regs nasr2 basr2))
         (merge_arrs (empty_stack (mod_stk m) (mod_stk_len m)) (merge_arrs nasa2 basa2))) R2.
Proof.
  intros.
  unfold alt_store in *; simplify_local. inv H3. inv H17. inv H18. inv H16. simplify_local.
  exploit match_states_same; try solve [eapply H14 | eapply max_stmnt_lt_module; eauto
                                        | econstructor; eauto with mgen].
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
    cbn; lia.
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
  intros; repeat inv_exists; simplify_local; tac0.
  do 2 econstructor. apply Smallstep.plus_one. econstructor. solve [eauto with mgen]. solve [eauto with mgen].
  solve [eauto with mgen]. eassumption.
  econstructor; eauto.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  auto. auto. auto. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor.
  eapply expr_runp_matches2. eassumption.
  2: { cbn. instantiate (1 := max_reg_module m + 1). repeat (apply match_assocmaps_gt; [lia|]).
       assumption. }
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  }
  auto.
  econstructor. econstructor. eapply expr_runp_matches2; eauto.
  { instantiate (1 := max_reg_module m + 1).
    apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  }
  cbn.
  repeat (apply match_assocmaps_gt; [lia|]). auto.

  rewrite empty_stack_transf.
  unfold transf_module; repeat destruct_match; try discriminate; simplify; [].
  eapply exec_ram_Some_write.
  3: {
    cbn. rewrite merge_get_default2.
    unfold "#", AssocMapExt.get_default. 
    repeat rewrite AssocMap.gso by lia.
    fold (AssocMapExt.get_default _ (ZToValue 0) (max_reg_module m + 2) rab').
    fold (find_assocmap 32 (max_reg_module m + 2) rab').
    solve [eauto].
    exploit max_reg_stmnt_not_modified_nb. apply H7.
    { instantiate (1 := max_reg_module m + 2).
      apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
      transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
      cbn; lia. 
      eapply max_reg_stmnt_le_stmnt_tree; eauto.
      transitivity (max_reg_module m + 1); [|lia].
      apply max_module_stmnts.
    }
    cbn; intros. rewrite <- H11. auto.
  }
  3: {
    cbn. unfold merge_regs.
    simplify. unfold merge_regs. repeat rewrite AssocMapExt.merge_add_assoc.
    repeat rewrite AssocMap.gso by lia. 
    rewrite merge_get_default3.
    repeat rewrite AssocMap.gso by lia.
    rewrite AssocMap.gss. auto.
    exploit max_reg_stmnt_not_modified_nb. apply H7.
    { instantiate (1 := max_reg_module m + 6).
      apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
      transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
      cbn; lia. 
      eapply max_reg_stmnt_le_stmnt_tree; eauto.
      transitivity (max_reg_module m + 1); [|lia].
      apply max_module_stmnts.
    }
    cbn; intros. rewrite <- H11. auto.
  }
  { unfold disable_ram in *. unfold transf_module in DISABLE_RAM;
                             repeat destruct_match; try discriminate.
    simplify.
    pose proof H7 as X2.
    pose proof H7 as X4.
    apply max_reg_stmnt_not_modified with (r := max_reg_module m + 2) in X2.
    apply max_reg_stmnt_not_modified with (r := max_reg_module m + 6) in X4.
    assert (forall ar ar' x, ar ! x = ar' ! x -> ar # x = ar' # x).
    { intros * HTMP. unfold find_assocmap, AssocMapExt.get_default. rewrite HTMP. auto. }
    apply H11 in X2. apply H11 in X4. simplify_local. rewrite <- X4. rewrite <- X2.
    apply int_eq_not. auto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
      transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
      cbn; lia. 
      eapply max_reg_stmnt_le_stmnt_tree; eauto.
      transitivity (max_reg_module m + 1); try lia.
      apply max_module_stmnts.
    }
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
      transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
      cbn; lia. 
      eapply max_reg_stmnt_le_stmnt_tree; eauto.
      transitivity (max_reg_module m + 1); try lia.
      apply max_module_stmnts.
    }
  }
  2: {
    pose proof H7 as X4.
    apply max_reg_stmnt_not_modified_nb with (r := max_reg_module m + 5) in X4.
    assert (HTMP2: forall ar ar' x, ar ! x = ar' ! x -> ar # x = ar' # x).
    { intros * HTMP. unfold find_assocmap, AssocMapExt.get_default. rewrite HTMP. auto. }
    apply HTMP2 in X4.
    cbn.
    unfold merge_regs. rewrite merge_get_default3.
    repeat rewrite AssocMap.gso by lia.
    rewrite AssocMap.gss; auto.
    { exploit max_reg_stmnt_not_modified_nb. apply H7.
      { instantiate (1 := max_reg_module m + 5).
        apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
        transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
        cbn; lia. 
        eapply max_reg_stmnt_le_stmnt_tree; eauto.
        transitivity (max_reg_module m + 1); [|lia].
        apply max_module_stmnts.
      }
      cbn; intros. rewrite <- H11. auto.
    }
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
      transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
      cbn; lia. 
      eapply max_reg_stmnt_le_stmnt_tree; eauto.
      transitivity (max_reg_module m + 1); [|lia].
      apply max_module_stmnts.
    } 
  }
  + solve [auto].
  + simplify_local. unfold merge_regs.
    rewrite merge_get_default3.
    repeat rewrite AssocMap.gso by lia. apply AssocMap.gss.
    { exploit max_reg_stmnt_not_modified_nb. apply H7.
      { instantiate (1 := max_reg_module m + 3).
        apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
        transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
        cbn; lia. 
        eapply max_reg_stmnt_le_stmnt_tree; eauto.
        transitivity (max_reg_module m + 1); [|lia].
        apply max_module_stmnts.
      }
      cbn; intros. rewrite <- H11. auto.
    }
  + simplify. unfold merge_regs. rewrite merge_get_default3.
    repeat rewrite AssocMap.gso by lia. apply AssocMap.gss.
    { exploit max_reg_stmnt_not_modified_nb. apply H7.
      { instantiate (1 := max_reg_module m + 1).
        apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
        transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
        cbn; lia. 
        eapply max_reg_stmnt_le_stmnt_tree; eauto.
        apply Pos.le_lt_trans with (max_reg_module m); [|lia].
        pose proof (max_module_stmnts m). lia.
      }
      cbn; intros. rewrite <- H11. auto.
    }
  + cbn. auto.
  + cbn. auto.
  + assert (mod_st (transf_module m) < max_reg_module m + 1).
  { unfold max_reg_module, transf_module; repeat destruct_match; try discriminate; simplify; lia. }
  
  unfold merge_regs.
  rewrite assocmap_merge_equiv with (c := empty_assocmap) (d := AssocMapExt.merge value ran' rab'); 
    (repeat rewrite merge_right_gso by lia; repeat rewrite AssocMap.gso by lia; auto).
  instantiate (1 := pstval).
  unfold transf_module; repeat destruct_match; try discriminate; simplify_local.
  eapply match_assocmaps_merge in H16.
  2: { apply H18. }
  unfold_merge. inv H16. rewrite <- H13.
  rewrite merge_get_default3 in H5; auto.
  apply mod_st_lt.
  + auto. 
  + econstructor; try solve [auto]. 
    * unfold merge_regs.
      remember (max_reg_module m) as p.
      constructor; intros. repeat unfold_merge.
      repeat rewrite PTree.gso by lia.
      unfold_merge.
      repeat rewrite merge_right_gso by lia.
      inv H16. inv H18. unfold AssocMapExt.merge. rewrite ! PTree.gcombine by auto.
      rewrite H13 by auto. now rewrite H15 by auto.
   * apply merge_arr_empty. apply match_empty_size_merge. cbn. 
     eapply match_arrs_size_stmnt_preserved in H14; inv H14; mgen_crush_local.
     eapply match_arrs_size_stmnt_preserved in H14; inv H14; mgen_crush_local.
     cbn.
     apply match_arrs_merge_set2; mgen_crush_local.
     all: eapply match_arrs_size_stmnt_preserved in H14; inv H14; mgen_crush_local.
     all: eapply match_arrs_size_stmnt_preserved in H7; inv H7; try rewrite empty_stack_transf; mgen_crush_local.
   * cbn.
     apply merge_arr_empty_match.
     apply match_empty_size_merge. apply match_empty_assocmap_set.
     all: eapply match_arrs_size_stmnt_preserved in H14; inv H14; mgen_crush_local.
   * apply match_empty_size_merge. apply match_empty_assocmap_set.
     mgen_crush_local.
     apply match_empty_size_merge.
     all: eapply match_arrs_size_stmnt_preserved in H7; inv H7; try rewrite empty_stack_transf; mgen_crush_local.
   * unfold disable_ram. unfold transf_module; repeat destruct_match; try discriminate; simplify_local.
     unfold merge_regs, empty_assocmap.
     unfold AssocMapExt.merge. unfold "#", AssocMapExt.get_default. rewrite ! PTree.gcombine by auto.
     rewrite ! AssocMap.gss. cbn.
     repeat rewrite ! AssocMap.gso by lia.
     rewrite ! AssocMap.gss.
     rewrite ! AssocMap.gempty.
     cbn. replace (ran' ! (max_reg_module m + 6)) with (@None value); cbn.
     apply Int.eq_true.
     { exploit max_reg_stmnt_not_modified_nb. apply H7.
      { instantiate (1 := max_reg_module m + 6).
        apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
        transitivity (max_reg_stmnt (Vseq x2 (Vnonblock (Vvari (mod_stk m) x0) x1))).
        cbn; lia. 
        eapply max_reg_stmnt_le_stmnt_tree; eauto.
        apply Pos.le_lt_trans with (max_reg_module m); [|lia].
        pose proof (max_module_stmnts m). lia.
      }
      cbn; intros. rewrite <- H11. auto.
    }
Qed.

Lemma translation_correct_load :
  forall 
      (m : module)
  (asr : AssocMap.tree value)
  (basr2 nasr2 : AssocMap.t value)
  (nasa2 basa2 : AssocMap.t arr)
  (asr'0 : assocmap_reg)
  (asa'0 : assocmap_arr)
  (res' : list stackframe)
  (st : positive)
  (tge : genv)
  (pstval : positive)
  (sf : list stackframe)
  (asa : AssocMap.t arr)
  (data : stmnt)
  (f : fext)
  (H : asr ! (mod_reset m) = Some (ZToValue 0))
  (H0 : asr ! (mod_finish m) = Some (ZToValue 0))
  (H1 : asr ! (mod_st m) = Some (posToValue st))
  (H2 : (mod_datapath m) ! st = Some data)
  (H3 : stmnt_runp f {| assoc_blocking := asr; assoc_nonblocking := empty_assocmap |}
         {| assoc_blocking := asa; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} data
         {| assoc_blocking := basr2; assoc_nonblocking := nasr2 |}
         {| assoc_blocking := basa2; assoc_nonblocking := nasa2 |})
  (H5 : (merge_regs empty_assocmap (merge_regs nasr2 basr2)) ! (mod_st m) = Some (posToValue pstval))
  (H6 : (Z.pos pstval <= 4294967295)%Z)
  (H8 : mod_ram m = None)
  (ASSOC : match_assocmaps (max_reg_module m + 1) asr asr'0)
  (ARRS : match_arrs asa asa'0)
  (STACKS : list_forall2 match_stackframes sf res')
  (ARRS_SIZE : match_empty_size m asa)
  (ARRS_SIZE2 : match_empty_size m asa'0)
  (DISABLE_RAM : disable_ram (mod_ram (transf_module m)) asr'0)
  (Learn : Learnt H8)
  (x : positive)
  (H4 : alt_load (mod_st m)
         {|
           ram_size := mod_stk_len m;
           ram_mem := mod_stk m;
           ram_en := max_reg_module m + 2;
           ram_u_en := max_reg_module m + 6;
           ram_addr := max_reg_module m + 1;
           ram_wr_en := max_reg_module m + 5;
           ram_d_in := max_reg_module m + 3;
           ram_d_out := max_reg_module m + 4;
           ram_ordering := ram_wf (max_reg_module m)
         |} (mod_datapath m) (mod_datapath (transf_module m)) st x),
  exists R2 : state,
    Smallstep.plus step tge (State res' (transf_module m) st asr'0 asa'0) Events.E0 R2 /\
    match_states
      (State sf m pstval (merge_regs empty_assocmap (merge_regs nasr2 basr2))
         (merge_arrs (empty_stack (mod_stk m) (mod_stk_len m)) (merge_arrs nasa2 basa2))) R2.
Proof.
  intros.
  unfold alt_load in *; simplify_local. inv H3. inv H22.
    2: { match goal with H: context[location_is] |- _ => inv H end. }
    match goal with H: context[location_is] |- _ => inv H end.
    inv H19. 2: { match goal with H: context[location_is] |- _ => inv H end. }
    match goal with H: context[location_is] |- _ => inv H end.
    inv H24. simplify_local.
    do 2 econstructor. eapply Smallstep.plus_two.
    + econstructor. mgen_crush. mgen_crush. mgen_crush. eassumption.
    econstructor. econstructor. simplify_local. econstructor. cbn. econstructor.
    econstructor. econstructor. cbn; econstructor.
    cbn; econstructor. econstructor. auto. auto. auto.
    econstructor. econstructor. cbn. econstructor.
    cbn; econstructor. econstructor. cbn; econstructor. cbn.
    cbn.
    eapply expr_runp_matches2 with (p := mod_st m); auto. eassumption.
    pose proof (mod_st_lt m).
    repeat (apply match_assocmaps_gt; [lia|]).
    repeat (apply match_assocmaps_gt2; [lia|]).
    eapply match_assocmaps_ge. eauto. lia.
    auto.

    simplify_local. rewrite empty_stack_transf. unfold transf_module; repeat destruct_match; crush_local.
    eapply exec_ram_Some_read; simplify_local.
    2: {
      pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default2 by auto.
      repeat rewrite find_assocmap_gso by lia. auto.
    }
    2: {
      pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default3 by auto.
      repeat rewrite AssocMap.gso by lia. 
      rewrite AssocMap.gss. auto.
    }
    { unfold disable_ram, transf_module in DISABLE_RAM;
      repeat destruct_match; try discriminate. simplify. apply int_eq_not. auto. }
    { pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default3 by auto.
      repeat rewrite AssocMap.gso by lia. 
      rewrite AssocMap.gss. auto. }
    { pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default3 by auto.
      repeat rewrite AssocMap.gso by lia. 
      rewrite AssocMap.gss. auto. }
    { eapply match_arrs_read. eauto. apply merge_arr_empty2; auto.
    }
    { cbn. unfold merge_regs. auto. }
    { auto. }
    { cbn. unfold transf_module; destruct_match; try discriminate; cbn. 
      pose proof (mod_st_lt m).
      rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
      rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia. 
      apply AssocMap.gss.
    }
    auto.
    + econstructor.
      - pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H13.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn. 
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        inv ASSOC. now rewrite <- H15 by lia.
      - pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H13.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn. 
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        inv ASSOC. now rewrite <- H15 by lia.
      - pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H13.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn. 
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        apply AssocMap.gss.
      - eassumption.
      - econstructor. econstructor. cbn. econstructor.
        cbn. eapply expr_runp_matches. eassumption.
        pose proof (mod_st_lt m).
        { constructor; intros.
          rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
          rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
          inv ASSOC. apply H15. lia.
        }
        { repeat apply merge_arr_empty2; auto.
          apply match_empty_size_merge; auto.
          mgen_crush_local.
        }
        cbn.
        econstructor. econstructor. econstructor. 
        cbn. unfold AssocMapExt.merge. 
        unfold find_assocmap, AssocMapExt.get_default.
        pose proof (mod_st_lt m).
        rewrite PTree.gso by lia.
        rewrite PTree.gcombine by auto. rewrite PTree.gso by lia.
        rewrite PTree.gss. cbn. auto.
      - cbn.
        simplify_local. rewrite empty_stack_transf.
        unfold transf_module; repeat destruct_match; try discriminate; cbn.
        econstructor. cbn.
        pose proof (mod_st_lt m).
        rewrite ! merge_get_default2 by auto.
        repeat rewrite find_assocmap_gso by lia.
        rewrite merge_get_default with (x := (Int.not (find_assocmap 32 (max_reg_module m + 6) asr'0))).
        rewrite ! merge_get_default2.
        repeat rewrite find_assocmap_gso by lia.
        rewrite find_assocmap_gss.
        apply Int.eq_true.
        auto.
        now repeat rewrite AssocMap.gso by lia.
        apply AssocMap.gss.
      - auto.
      - auto.
      - unfold transf_module; destruct_match; try discriminate; cbn.
        pose proof (mod_st_lt m).
        repeat unfold_merge.
        repeat rewrite PTree.gso by lia.
        rewrite PTree.gss.
        rewrite merge_get_default3 in H5 by auto.
        rewrite merge_get_default3 in H5 by (now repeat rewrite AssocMap.gso by lia).
        rewrite AssocMap.gss in H5. inv H5. auto.
      - auto.
    + auto.
    + econstructor.
      - constructor; intros.
        unfold merge_regs. 
        repeat rewrite ! merge_get_default3 by auto.
        symmetry; repeat rewrite ! merge_get_default3 by auto. symmetry.
        pose proof (mod_st_lt m).
        destruct (peq r0 r); subst.
        { rewrite PTree.gss. unfold AssocMapExt.merge. rewrite PTree.gcombine by auto.
          rewrite PTree.gss. now cbn. }
        repeat rewrite PTree.gso by lia.
        destruct (peq r0 (mod_st m)); subst.
        { rewrite PTree.gss. rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
          apply PTree.gss. }
        repeat rewrite PTree.gso by lia.
        repeat rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        repeat rewrite PTree.gso by lia. inv ASSOC.
        apply H15. lia.
      - repeat apply merge_arr_empty2; mgen_crush_local.
      - auto.
      - mgen_crush_local.
      - mgen_crush_local.
      - unfold disable_ram. unfold transf_module; destruct_match; try discriminate; cbn in *.
        rewrite H8 in *. cbn in *. inv Heqo. cbn. 2: { auto. }
        pose proof (mod_st_lt m).
        rewrite ! merge_get_default2 by auto.        
        repeat rewrite find_assocmap_gso by lia.
        rewrite merge_get_default with (x := (Int.not (find_assocmap 32 (max_reg_module m + 6) asr'0))).
        rewrite ! merge_get_default2.
        repeat rewrite find_assocmap_gso by lia.
        rewrite find_assocmap_gss.
        apply Int.eq_true.
        auto.
        now repeat rewrite AssocMap.gso by lia.
        apply AssocMap.gss.
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

Lemma match_arrs_trans :
  forall asa1 asa2 asa3, 
    match_arrs asa1 asa2 -> match_arrs asa2 asa3 -> match_arrs asa1 asa3.
Proof.
  inversion 1. inversion 1; subst.
  econstructor; eauto.
  intros. eapply H0 in H2. simplify. eapply H5 in H2; simplify.
  econstructor; split; eauto. split; congruence.
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

Lemma merge_arr_empty3 :
  forall m ar ar' n v,
    match_empty_size m ar ->
    match_arrs (merge_arrs (arr_assocmap_set m.(mod_stk) n v (empty_stack (mod_stk m) (mod_stk_len m))) ar) ar' ->
    match_arrs (arr_assocmap_set m.(mod_stk) n v ar) ar'.
Proof.
  intros. eapply match_arrs_trans; eauto. clear H0. inversion H; subst.
  econstructor; intros.
  2: { pose proof H3 as H3'. eapply arr_assocmap_set_gs2' in H3. unfold merge_arrs. rewrite PTree.gcombine by auto.
       rewrite H3. rewrite arr_assocmap_set_gs2; auto. now eapply H2. }
  destruct (peq s (mod_stk m)); subst.
  2: { assert ((empty_stack (mod_stk m) (mod_stk_len m)) ! s = None).
       unfold empty_stack. rewrite PTree.gso by auto. auto. 
       pose proof H4 as H4'. eapply H2 in H4.
       eapply arr_assocmap_set_gs2 in H4. rewrite H4 in H3. discriminate.
       }
  assert ((empty_stack (mod_stk m) (mod_stk_len m)) ! (mod_stk m) = Some (arr_repeat None (mod_stk_len m))).
  { unfold empty_stack. rewrite PTree.gss. auto. }
  eapply H0 in H4. simplify.
  erewrite arr_assocmap_set_gss in H3 by eauto. inv H3. eexists; split; [|split].
  - unfold merge_arrs. rewrite PTree.gcombine by auto.
    setoid_rewrite H4.
    erewrite arr_assocmap_set_gss.
    2: { unfold empty_stack. rewrite PTree.gss; eauto. }
    cbn. eauto.
  - intros. destruct (Nat.eq_dec addr n); subst.
    destruct (dec_lt n (arr_length x)).
    + rewrite array_get_error_set_bound by auto.
      erewrite combine_lookup_second; eauto.
      rewrite array_get_error_set_bound; auto.
      cbn in *. lia.
    + rewrite !array_get_error_bound_gt; auto.
      rewrite combine_length. rewrite <- array_set_len. cbn; lia.
      rewrite <- array_set_len. cbn. lia. rewrite <- array_set_len.
      lia.
    + rewrite array_gso by auto. rewrite combine_array_set.
      rewrite array_gso by auto. rewrite combine_none2. auto. 
      rewrite list_repeat_len in H6. auto. cbn. auto.
  - rewrite <- array_set_len. rewrite combine_length. rewrite <- array_set_len. cbn; lia.
    rewrite <- array_set_len. cbn; lia.
Qed.
      
#[local] Hint Resolve merge_arr_empty2 : mgen.

Lemma translation_correct_store_cond :
    forall (m : module)
  (asr : AssocMap.tree value)
  (basr2 nasr2 : AssocMap.t value)
  (nasa2 basa2 : AssocMap.t arr)
  (asr'0 : assocmap_reg)
  (asa'0 : assocmap_arr)
  (res' : list stackframe)
  (st : positive)
  (tge : genv)
  (pstval : positive)
  (sf : list stackframe)
  (asa : AssocMap.t arr)
  (data : stmnt)
  (f : fext)
  (H : asr ! (mod_reset m) = Some (ZToValue 0))
  (H0 : asr ! (mod_finish m) = Some (ZToValue 0))
  (H1 : asr ! (mod_st m) = Some (posToValue st))
  (H2 : (mod_datapath m) ! st = Some data)
  (H3 : stmnt_runp f {| assoc_blocking := asr; assoc_nonblocking := empty_assocmap |}
         {| assoc_blocking := asa; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} data
         {| assoc_blocking := basr2; assoc_nonblocking := nasr2 |}
         {| assoc_blocking := basa2; assoc_nonblocking := nasa2 |})
  (H5 : (merge_regs empty_assocmap (merge_regs nasr2 basr2)) ! (mod_st m) = Some (posToValue pstval))
  (H6 : (Z.pos pstval <= 4294967295)%Z)
  (H8 : mod_ram m = None)
  (ASSOC : match_assocmaps (max_reg_module m + 1) asr asr'0)
  (ARRS : match_arrs asa asa'0)
  (STACKS : list_forall2 match_stackframes sf res')
  (ARRS_SIZE : match_empty_size m asa)
  (ARRS_SIZE2 : match_empty_size m asa'0)
  (DISABLE_RAM : disable_ram (mod_ram (transf_module m)) asr'0)
  (Learn : Learnt H8)
  (x : positive)
  (H4 : alt_store_cond
         {|
           ram_size := mod_stk_len m;
           ram_mem := mod_stk m;
           ram_en := max_reg_module m + 2;
           ram_u_en := max_reg_module m + 6;
           ram_addr := max_reg_module m + 1;
           ram_wr_en := max_reg_module m + 5;
           ram_d_in := max_reg_module m + 3;
           ram_d_out := max_reg_module m + 4;
           ram_ordering := ram_wf (max_reg_module m)
         |} (mod_datapath m) (mod_datapath (transf_module m)) st),
  exists R2 : state,
    Smallstep.plus step tge (State res' (transf_module m) st asr'0 asa'0) Events.E0 R2 /\
    match_states
      (State sf m pstval (merge_regs empty_assocmap (merge_regs nasr2 basr2))
         (merge_arrs (empty_stack (mod_stk m) (mod_stk_len m)) (merge_arrs nasa2 basa2))) R2.
Proof.
  intros.
  unfold alt_store_cond in *; simplify_local. inv H3. inv H17. 2: { inv H16. } inv H18. simplify_local.
  inv H14. inv H13. inv H17.
  - inv H20. inv H16. inv H16. cbn in *. econstructor; split.
    + apply Smallstep.plus_one. econstructor. solve [eauto with mgen]. solve [eauto with mgen]. solve [eauto with mgen]. solve [eauto with mgen]. econstructor. econstructor. econstructor. econstructor. econstructor. econstructor.
    econstructor.
    cbn. eapply expr_runp_matches2; eauto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } econstructor. cbn. eauto. cbn. econstructor. eauto. cbn. eauto.
    econstructor. econstructor. econstructor. econstructor. econstructor. econstructor.
    econstructor. econstructor. econstructor. econstructor. econstructor.
    cbn. eapply expr_runp_matches2; eauto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto. cbn.
  cbn. eapply expr_runp_matches2; eauto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto. eauto.
  econstructor. econstructor. econstructor.
  cbn. eapply expr_runp_matches2; eauto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto.
  cbn. eapply expr_runp_matches2; eauto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto. eauto.
  econstructor. econstructor. cbn. inv H19. econstructor.

  rewrite empty_stack_transf.
  unfold transf_module; repeat destruct_match; try discriminate; []; cbn in *.
  eapply exec_ram_Some_write.
  3: { cbn.
    assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. } 
    rewrite merge_find_assocmap by (unfold empty_assocmap; apply PTree.gempty).
    rewrite !assocmap_gso by lia. eauto. }
    3: { cbn.
      assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
    unfold merge_regs, AssocMapExt.merge, empty_assocmap. rewrite PTree.gcombine by auto; cbn.
    rewrite PTree.gempty. cbn. rewrite !PTree.gso by lia. rewrite PTree.gss. eauto. }
    3: { cbn.
      assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
    unfold merge_regs, AssocMapExt.merge, empty_assocmap. rewrite PTree.gcombine by auto; cbn.
    rewrite PTree.gempty. cbn. rewrite !PTree.gso by lia. rewrite PTree.gss. eauto. }
3: { cbn.
      assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
    unfold merge_regs, AssocMapExt.merge, empty_assocmap. rewrite PTree.gcombine by auto; cbn.
    rewrite PTree.gempty. cbn. rewrite !PTree.gso by lia. rewrite PTree.gss. eauto. }
    3: { cbn.
      assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
    unfold merge_regs, AssocMapExt.merge, empty_assocmap. rewrite PTree.gcombine by auto; cbn.
    rewrite PTree.gempty. cbn. rewrite !PTree.gso by lia. rewrite PTree.gss. eauto. }
    assert ((Int.eq vc (ZToValue 0)) = false).
    { unfold valueToBool in *. destruct_match; try discriminate.
      eapply Z.eqb_neq in Heqb. unfold uvalueToZ in *. 
      unfold Int.eq. destruct_match; auto. exfalso. unfold ZToValue in *. eapply Heqb.
      clear Heqs.
      rewrite Int.unsigned_repr in e by crush. auto. }
      rewrite H3. cbn. unfold boolToValue, natToValue. unfold Int.xor.
      unfold Int.neg.
      replace (Int.unsigned (Int.repr (Z.of_nat 1))) with 1%Z by auto. cbn.
      replace (Int.repr (-1)) with Int.mone by auto.
      rewrite Z.lxor_comm.
      replace (Int.repr (Z.lxor (Int.unsigned (find_assocmap 32 (max_reg_module m + 6) asr'0)) (Int.unsigned Int.mone))) with
      (Int.not (find_assocmap 32 (max_reg_module m + 6) asr'0)) by auto.
      apply int_eq_not. 
      unfold disable_ram in DISABLE_RAM.
  unfold transf_module in *; repeat destruct_match; try discriminate. auto. cbn in *.
  inv Heqo1. cbn in *; assumption. auto.
    cbn. auto. cbn. auto.
    eapply mod_st_modify; eauto.
    assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
    eapply match_assocmaps_merge. repeat (eapply match_assocmaps_gt; [lia|]).
  eapply match_assocmaps_equiv. eapply match_assocmaps_merge.
  eapply match_assocmaps_equiv.
  eapply match_assocmaps_gss.
  repeat (eapply match_assocmaps_gt; [lia|]). eauto. auto.
    + econstructor.
      * eapply match_assocmaps_merge. repeat (eapply match_assocmaps_gt; [lia|]).
  eapply match_assocmaps_equiv. eapply match_assocmaps_merge.
  eapply match_assocmaps_equiv.
  eapply match_assocmaps_gss.
  repeat (eapply match_assocmaps_gt; [lia|]). eauto.
      * eapply merge_arr_empty. eapply merge_arr_empty_match; eauto. 
        eapply match_empty_assocmap_set; eauto. eapply merge_arr_empty.
        eapply match_empty_assocmap_set; eauto.
        eapply merge_arr_empty3. eauto. eapply match_arrs_merge_set2; eauto.
        eapply match_arrs_size_equiv. eapply match_arrs_size_equiv. 
        eapply match_arrs_equiv.
      * eauto.
      * eapply match_empty_size_merge. eapply match_arrs_size_equiv.
        eapply match_empty_size_merge. eapply match_arrs_size_equiv.
        eapply match_empty_assocmap_set; eauto.
      * eapply match_empty_size_merge. eapply match_empty_assocmap_set; eauto. 
        eapply match_arrs_size_equiv.
        eapply match_empty_size_merge. eapply match_arrs_size_equiv. eauto.
      * unfold disable_ram in *.
        unfold transf_module in *; repeat destruct_match; try discriminate. auto. cbn in *.
        inv Heqo. cbn.
        assert (r < max_reg_module m + 1).
        { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
          transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
          cbn; lia. 
          eapply max_reg_stmnt_le_stmnt_tree; eauto.
          apply max_module_stmnts. }
        unfold find_assocmap, AssocMapExt.get_default.
        unfold merge_regs, empty_assocmap, AssocMapExt.merge.
        rewrite !PTree.gcombine by auto.
        rewrite !PTree.gss.
        rewrite !PTree.gso by lia.
        rewrite !PTree.gss.
        cbn. rewrite !PTree.gempty. cbn.
        assert ((Int.eq vc (ZToValue 0)) = false).
    { unfold valueToBool in *. destruct_match; try discriminate.
      eapply Z.eqb_neq in Heqb. unfold uvalueToZ in *. 
      unfold Int.eq. destruct_match; auto. exfalso. unfold ZToValue in *. eapply Heqb.
      clear Heqs.
      rewrite Int.unsigned_repr in e by crush. auto. } rewrite H7. cbn. unfold boolToValue.
      apply Int.eq_true.
  - inv H20. cbn in *. econstructor. split.
    + apply Smallstep.plus_one. econstructor. solve [eauto with mgen]. solve [eauto with mgen]. solve [eauto with mgen]. solve [eauto with mgen]. econstructor. econstructor. econstructor. econstructor. econstructor.
    econstructor. econstructor.
    cbn. eapply expr_runp_matches2; eauto.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } econstructor. cbn. eauto.
  econstructor. econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. cbn. econstructor. econstructor. econstructor. econstructor. econstructor. cbn.
  eapply erun_Vternary_false. cbn.
  eapply expr_runp_matches2. eassumption.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto. eauto.
  econstructor. eauto. eauto. 
  econstructor. econstructor. cbn. 
  eapply erun_Vternary_false.
  eapply expr_runp_matches2. eassumption.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto. eauto.
  econstructor. eauto. eauto. econstructor. cbn. econstructor.
  cbn.
eapply expr_runp_matches2. eassumption.
    { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts.
  } repeat (apply match_assocmaps_gt; [lia|]). eauto. eauto.
  cbn. 

  rewrite empty_stack_transf.
  unfold transf_module; repeat destruct_match; try discriminate. cbn.
  
  eapply exec_ram_Some_idle; cbn. 
  rewrite !merge_get_default2 by (unfold empty_assocmap; apply PTree.gempty).
  assert (r < max_reg_module m + 1).
  { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
    transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
    cbn; lia. 
    eapply max_reg_stmnt_le_stmnt_tree; eauto.
    apply max_module_stmnts. }
  rewrite !find_assocmap_gso by lia.
  rewrite find_assocmap_gss.
  unfold valueToBool in H18. destruct_match; try discriminate. eapply Z.eqb_eq in Heqb. 
  unfold uvalueToZ in Heqb. unfold ZToValue, boolToValue, Int.eq. rewrite Heqb.
  rewrite Int.unsigned_repr by crush. cbn. unfold natToValue.
  unfold Int.xor. cbn. replace (Int.unsigned (Int.repr 0)) with 0%Z by auto.
  rewrite Z.lxor_0_l. rewrite Int.repr_unsigned.
  unfold disable_ram in DISABLE_RAM.
  unfold transf_module in *; repeat destruct_match; try discriminate. auto. cbn in *.
  inv Heqo1. cbn in *. unfold Int.eq in *. destruct_match; discriminate.
  eauto. eauto. pose proof (mod_st_lt m).
  eapply mod_st_modify; eauto. eapply match_assocmaps_merge.
  eapply match_assocmaps_equiv. eapply match_assocmaps_merge.
  eapply match_assocmaps_equiv.
  eapply match_assocmaps_gss.
  repeat (eapply match_assocmaps_gt; [lia|]). eauto. eauto.
  + econstructor; eauto.
    -- eapply match_assocmaps_merge.
       eapply match_assocmaps_equiv. eapply match_assocmaps_merge.
       eapply match_assocmaps_equiv.
       eapply match_assocmaps_gss.
       repeat (eapply match_assocmaps_gt; [lia|]). eauto.
    -- eapply match_arrs_merge.
       eapply merge_arr_empty_match; eauto.
       eapply match_arrs_equiv.
       eapply match_arrs_merge. eauto.
       eapply match_arrs_equiv. eauto.
    -- eapply merge_arr_empty_match; eauto. eapply merge_arr_empty_match; eauto.
    -- eapply merge_arr_empty_match; eauto. eapply merge_arr_empty_match; eauto.
    -- unfold transf_module in *; repeat destruct_match; try discriminate. auto. cbn in *.
       unfold empty_assocmap. rewrite !merge_find_assocmap by (eapply PTree.gempty).
       assert (r < max_reg_module m + 1).
       { apply Pos.le_lt_trans with (m := max_stmnt_tree (mod_datapath m)).
         transitivity (max_reg_stmnt (Vseq (Vseq Vskip (Vcond x3 (Vblock (Vvari (mod_stk m) x0) x1) Vskip)) (Vblock (Vvar r) (Vlit x2)))).
         cbn; lia. 
         eapply max_reg_stmnt_le_stmnt_tree; eauto.
         apply max_module_stmnts. }
         rewrite !find_assocmap_gso by lia.
         rewrite !find_assocmap_gss by lia.
         unfold valueToBool in H18. destruct_match; try discriminate. eapply Z.eqb_eq in Heqb. 
         unfold uvalueToZ in Heqb. unfold ZToValue, boolToValue, natToValue. unfold Int.eq at 2. rewrite Heqb.
         rewrite Int.unsigned_repr by crush. cbn. unfold natToValue.
         unfold Int.xor. cbn. replace (Int.unsigned (Int.repr 0)) with 0%Z by auto.
         rewrite Z.lxor_0_l. rewrite Int.repr_unsigned. eauto.
Qed.        

Lemma translation_correct_load_cond :
  forall 
      (m : module)
  (asr : AssocMap.tree value)
  (basr2 nasr2 : AssocMap.t value)
  (nasa2 basa2 : AssocMap.t arr)
  (asr'0 : assocmap_reg)
  (asa'0 : assocmap_arr)
  (res' : list stackframe)
  (st : positive)
  (tge : genv)
  (pstval : positive)
  (sf : list stackframe)
  (asa : AssocMap.t arr)
  (data : stmnt)
  (f : fext)
  (H : asr ! (mod_reset m) = Some (ZToValue 0))
  (H0 : asr ! (mod_finish m) = Some (ZToValue 0))
  (H1 : asr ! (mod_st m) = Some (posToValue st))
  (H2 : (mod_datapath m) ! st = Some data)
  (H3 : stmnt_runp f {| assoc_blocking := asr; assoc_nonblocking := empty_assocmap |}
         {| assoc_blocking := asa; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} data
         {| assoc_blocking := basr2; assoc_nonblocking := nasr2 |}
         {| assoc_blocking := basa2; assoc_nonblocking := nasa2 |})
  (H5 : (merge_regs empty_assocmap (merge_regs nasr2 basr2)) ! (mod_st m) = Some (posToValue pstval))
  (H6 : (Z.pos pstval <= 4294967295)%Z)
  (H8 : mod_ram m = None)
  (ASSOC : match_assocmaps (max_reg_module m + 1) asr asr'0)
  (ARRS : match_arrs asa asa'0)
  (STACKS : list_forall2 match_stackframes sf res')
  (ARRS_SIZE : match_empty_size m asa)
  (ARRS_SIZE2 : match_empty_size m asa'0)
  (DISABLE_RAM : disable_ram (mod_ram (transf_module m)) asr'0)
  (Learn : Learnt H8)
  (x : positive)
  (H4 : alt_load_cond (mod_st m)
         {|
           ram_size := mod_stk_len m;
           ram_mem := mod_stk m;
           ram_en := max_reg_module m + 2;
           ram_u_en := max_reg_module m + 6;
           ram_addr := max_reg_module m + 1;
           ram_wr_en := max_reg_module m + 5;
           ram_d_in := max_reg_module m + 3;
           ram_d_out := max_reg_module m + 4;
           ram_ordering := ram_wf (max_reg_module m)
         |} (mod_datapath m) (mod_datapath (transf_module m)) st x),
  exists R2 : state,
    Smallstep.plus step tge (State res' (transf_module m) st asr'0 asa'0) Events.E0 R2 /\
    match_states
      (State sf m pstval (merge_regs empty_assocmap (merge_regs nasr2 basr2))
         (merge_arrs (empty_stack (mod_stk m) (mod_stk_len m)) (merge_arrs nasa2 basa2))) R2.
Proof.
  intros.
  unfold alt_load_cond in *; simplify_local. inv H3. inv H23.
    2: { match goal with H: context[location_is] |- _ => inv H end. }
    match goal with H: context[location_is] |- _ => inv H end.
    inv H20. inv H19. inv H25. inv H23. 2: { match goal with H: context[location_is] |- _ => inv H end. }
    match goal with H: context[location_is] |- _ => inv H end.
    inv H24.
  - inv H22. simplify_local.
    do 2 econstructor. eapply Smallstep.plus_two.
    + econstructor. mgen_crush. mgen_crush. mgen_crush. eassumption.
    econstructor. econstructor. simplify_local. econstructor. cbn. econstructor.
    econstructor. econstructor. cbn; econstructor.
    cbn; econstructor. econstructor. auto. auto. auto.
    econstructor. 
    eapply expr_runp_matches2 with (p := mod_st m); auto. eassumption.
    pose proof (mod_st_lt m).
    repeat (apply match_assocmaps_gt; [lia|]).
    repeat (apply match_assocmaps_gt2; [lia|]).
    eapply match_assocmaps_ge. eauto. lia.
    auto. econstructor. cbn. eauto. eauto. eauto. 
    econstructor. cbn. pose proof (mod_st_lt m). rewrite assocmap_gso by lia. eauto.
    cbn. eauto. econstructor.
    cbn; econstructor. econstructor. econstructor.  econstructor.  econstructor. 
    econstructor. 
    eapply expr_runp_matches2 with (p := mod_st m); auto. eassumption.
    pose proof (mod_st_lt m).
    repeat (apply match_assocmaps_gt; [lia|]).
    repeat (apply match_assocmaps_gt2; [lia|]).
    eapply match_assocmaps_ge. eauto. lia.
    auto.
    eapply expr_runp_matches2 with (p := mod_st m); auto. eassumption.
    pose proof (mod_st_lt m).
    repeat (apply match_assocmaps_gt; [lia|]).
    repeat (apply match_assocmaps_gt2; [lia|]).
    eapply match_assocmaps_ge. eauto. lia.
    auto. eauto.

    simplify_local. rewrite empty_stack_transf. unfold transf_module; repeat destruct_match; crush_local.
    eapply exec_ram_Some_read; simplify_local.
    2: {
      pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default2 by auto.
      repeat rewrite find_assocmap_gso by lia. auto.
    }
    2: {
      pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default3 by auto.
      repeat rewrite AssocMap.gso by lia.
      rewrite AssocMap.gss. auto.
    }
    { unfold disable_ram, transf_module in DISABLE_RAM;
      repeat destruct_match; try discriminate. simplify.
      assert ((Int.eq vc (ZToValue 0)) = false). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_neq in Heqb. rewrite e in Heqb.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in Heqb by auto. lia. }
      rewrite H3. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 1))) with (Int.mone) by auto.
      rewrite Int.xor_commut.
      apply int_eq_not. auto. }
    { pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default3 by auto.
      repeat rewrite AssocMap.gso by lia.
      rewrite AssocMap.gss. auto. }
    { pose proof (mod_st_lt m).
      unfold merge_regs, empty_assocmap. repeat rewrite find_assocmap_gso by lia.
      rewrite merge_get_default3 by auto.
      repeat rewrite AssocMap.gso by lia.
      rewrite AssocMap.gss. auto. }
    { eapply match_arrs_read. eauto. apply merge_arr_empty2; auto.
    }
    { cbn. unfold merge_regs. auto. }
    { auto. }
    { cbn. unfold transf_module; destruct_match; try discriminate; cbn.
      pose proof (mod_st_lt m).
      rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
      rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
      apply AssocMap.gss.
    }
    auto.
    + econstructor.
      * pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H14.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn.
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        inv ASSOC. now rewrite <- H16 by lia.
      * pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H14.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn.
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        inv ASSOC. now rewrite <- H16 by lia.
      * pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H14.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn.
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        apply AssocMap.gss.
      * eassumption.
      * econstructor. econstructor. cbn. econstructor. econstructor.
        econstructor. cbn. econstructor. econstructor; eauto.
        cbn. eapply expr_runp_matches. eassumption.
        pose proof (mod_st_lt m).
        { constructor; intros.
          rewrite AssocMap.gso by lia.
          rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
          rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
          inv ASSOC. apply H16. lia.
        }
        { repeat apply merge_arr_empty2; auto.
          apply match_empty_size_merge; auto.
          mgen_crush_local.
        }
        cbn.
        econstructor. econstructor.
      * cbn.
        simplify_local. rewrite empty_stack_transf.
        unfold transf_module; repeat destruct_match; try discriminate; cbn.
        econstructor. cbn.
        pose proof (mod_st_lt m).
        rewrite ! merge_get_default2 by auto.
        repeat rewrite find_assocmap_gso by lia.
        rewrite merge_get_default with (x := (Int.not (find_assocmap 32 (max_reg_module m + 6) asr'0))).
        rewrite ! merge_get_default2.
        repeat rewrite find_assocmap_gso by lia.
        rewrite find_assocmap_gss.
        assert ((Int.eq vc (ZToValue 0)) = false). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_neq in Heqb. rewrite e in Heqb.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in Heqb by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 1))) with (Int.mone) by auto.
      rewrite Int.xor_commut.
        apply Int.eq_true.
        auto.
        now repeat rewrite AssocMap.gso by lia.
        rewrite AssocMap.gss. 
        assert ((Int.eq vc (ZToValue 0)) = false). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_neq in Heqb. rewrite e in Heqb.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in Heqb by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 1))) with (Int.mone) by auto.
      rewrite Int.xor_commut. auto.
      * auto.
      * auto.
      * unfold transf_module; destruct_match; try discriminate; cbn.
        pose proof (mod_st_lt m).
        repeat unfold_merge.
        repeat rewrite PTree.gso by lia.
        rewrite PTree.gss.
        rewrite merge_get_default3 in H5 by auto.
        rewrite merge_get_default3 in H5 by (now repeat rewrite AssocMap.gso by lia).
        rewrite AssocMap.gss in H5. inv H5. auto.
      * auto.
    + auto.
    + econstructor.
      * constructor; intros.
        unfold merge_regs.
        repeat rewrite ! merge_get_default3 by auto.
        symmetry; repeat rewrite ! merge_get_default3 by auto. symmetry.
        pose proof (mod_st_lt m).
        destruct (peq r0 r); subst.
        { rewrite PTree.gss. unfold AssocMapExt.merge. rewrite !PTree.gso by lia. rewrite PTree.gss. 
          unfold find_assocmap, AssocMapExt.get_default, empty_assocmap.
          rewrite !PTree.gso by lia.
          rewrite PTree.gcombine by auto.
          rewrite !PTree.gso by lia. rewrite PTree.gss. now cbn. }
        repeat rewrite PTree.gso by lia.
        destruct (peq r0 (mod_st m)); subst.
        { rewrite PTree.gss. rewrite !PTree.gso by lia.
          rewrite PTree.gss. auto. }
        repeat rewrite PTree.gso by lia.
        repeat rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        repeat rewrite PTree.gso by lia. inv ASSOC.
        apply H16. lia.
      * repeat apply merge_arr_empty2; mgen_crush_local.
      * auto.
      * mgen_crush_local.
      * mgen_crush_local.
      * unfold disable_ram. unfold transf_module; destruct_match; try discriminate; cbn in *.
        rewrite H8 in *. cbn in *. inv Heqo. cbn. 2: { auto. }
        pose proof (mod_st_lt m).
        rewrite ! merge_get_default2 by auto.
        repeat rewrite find_assocmap_gso by lia.
        rewrite merge_get_default with (x := (Int.not (find_assocmap 32 (max_reg_module m + 6) asr'0))).
        rewrite ! merge_get_default2.
        repeat rewrite find_assocmap_gso by lia.
        rewrite find_assocmap_gss.
        assert ((Int.eq vc (ZToValue 0)) = false). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_neq in Heqb. rewrite e in Heqb.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in Heqb by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 1))) with (Int.mone) by auto.
      rewrite Int.xor_commut.
        apply Int.eq_true.
        auto.
        now repeat rewrite AssocMap.gso by lia.
        rewrite AssocMap.gss. 
        assert ((Int.eq vc (ZToValue 0)) = false). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_neq in Heqb. rewrite e in Heqb.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in Heqb by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 1))) with (Int.mone) by auto.
      rewrite Int.xor_commut. auto.
  - inv H22. simplify_local.
    do 2 econstructor. eapply Smallstep.plus_two.
    + econstructor. mgen_crush. mgen_crush. mgen_crush. eassumption.
    econstructor. econstructor. simplify_local. econstructor. cbn. econstructor.
    econstructor. econstructor. cbn; econstructor.
    cbn; econstructor. econstructor. econstructor. 
    eapply expr_runp_matches2 with (p := mod_st m); auto. eassumption.
    pose proof (mod_st_lt m).
    repeat (apply match_assocmaps_gt; [lia|]).
    repeat (apply match_assocmaps_gt2; [lia|]).
    eapply match_assocmaps_ge. eauto. lia. auto.
    econstructor. cbn. eauto. eauto. eauto.
    econstructor. pose proof (mod_st_lt m).
    rewrite assocmap_gso by lia. auto. cbn. eauto.
    econstructor. econstructor. cbn. econstructor.
    cbn; econstructor. econstructor. cbn; econstructor. cbn.
    eapply erun_Vternary_false.
    eapply expr_runp_matches2 with (p := mod_st m); auto. eassumption.
    pose proof (mod_st_lt m).
    repeat (apply match_assocmaps_gt; [lia|]).
    repeat (apply match_assocmaps_gt2; [lia|]).
    eapply match_assocmaps_ge. eauto. lia.
    auto. econstructor. pose proof (mod_st_lt m). rewrite !assocmap_gso by lia. eauto. eauto.

    simplify_local. rewrite empty_stack_transf. unfold transf_module; repeat destruct_match; crush_local.
    eapply exec_ram_Some_idle; simplify_local.
    * unfold empty_assocmap. rewrite !merge_find_assocmap by (apply PTree.gempty).
      rewrite !assocmap_gso by lia. pose proof (mod_st_lt m). 
      rewrite !assocmap_gso by lia. rewrite assocmap_gss.
      assert ((Int.eq vc (ZToValue 0)) = true). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_eq in Heqb. clear Heqs. rewrite Heqb in n.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in n by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue.
      replace (Int.neg (Int.repr (Z.of_nat 0))) with (Int.repr 0) by auto.
      rewrite Int.xor_zero_l. unfold disable_ram, transf_module in *.
      repeat destruct_match; try discriminate.  cbn in *. inv Heqo1. cbn in *. eassumption.
    * eauto.
    * eauto.
    * { cbn. unfold transf_module; destruct_match; try discriminate; cbn.
      pose proof (mod_st_lt m).
      rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
      rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
      apply AssocMap.gss.
      }
    * eauto.
+ econstructor.
      * pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H14.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn.
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        inv ASSOC. now rewrite <- H16 by lia.
      * pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H14.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn.
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        inv ASSOC. now rewrite <- H16 by lia.
      * pose proof (mod_reset_lt m).
        pose proof (mod_ordering_wf m).
        unfold module_ordering in H14.
        cbn. unfold transf_module; destruct_match; try discriminate; cbn.
        rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
        apply AssocMap.gss.
      * eassumption.
      * econstructor. econstructor. cbn. econstructor. econstructor.
        econstructor. cbn. econstructor. eapply erun_Vternary_false; eauto.
        cbn. eapply expr_runp_matches. eassumption.
        pose proof (mod_st_lt m).
        { constructor; intros.
          rewrite AssocMap.gso by lia.
          rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
          rewrite merge_get_default3 by auto. repeat rewrite AssocMap.gso by lia.
          inv ASSOC. apply H16. lia.
        }
        { repeat apply merge_arr_empty2; auto.
          apply match_empty_size_merge; auto.
          mgen_crush_local.
        }
        cbn.
        econstructor. econstructor.
      * cbn.
        simplify_local. rewrite empty_stack_transf.
        unfold transf_module; repeat destruct_match; try discriminate; cbn.
        econstructor. cbn.
        pose proof (mod_st_lt m).
        rewrite ! merge_get_default2 by auto.
        repeat rewrite find_assocmap_gso by lia.
        unfold empty_assocmap.
        rewrite !merge_get_default2; auto.
        rewrite !assocmap_gso by lia. rewrite assocmap_gss.
        assert ((Int.eq vc (ZToValue 0)) = true). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_eq in Heqb. clear Heqs. rewrite Heqb in n.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in n by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 0))) with (Int.zero) by auto.
      rewrite Int.xor_commut. rewrite Int.xor_zero.
      unfold disable_ram, transf_module in DISABLE_RAM;
      repeat destruct_match; try discriminate. cbn in *. inv Heqo0. assumption.
      * auto.
      * auto.
      * unfold transf_module; destruct_match; try discriminate; cbn.
        pose proof (mod_st_lt m).
        repeat unfold_merge.
        repeat rewrite PTree.gso by lia.
        rewrite PTree.gss.
        rewrite merge_get_default3 in H5 by auto.
        rewrite merge_get_default3 in H5 by (now repeat rewrite AssocMap.gso by lia).
        rewrite AssocMap.gss in H5. inv H5. auto.
      * auto.
    + auto.
    + econstructor.
      * constructor; intros.
        unfold merge_regs.
        repeat rewrite ! merge_get_default3 by auto.
        symmetry; repeat rewrite ! merge_get_default3 by auto. symmetry.
        pose proof (mod_st_lt m).
        destruct (peq r0 r); subst.
        { rewrite PTree.gss. unfold AssocMapExt.merge. rewrite !PTree.gso by lia. rewrite PTree.gss. 
          unfold find_assocmap, AssocMapExt.get_default, empty_assocmap.
          rewrite !PTree.gso by lia.
          rewrite !PTree.gcombine by auto. rewrite !PTree.gempty. cbn.
          rewrite !PTree.gso by lia. inv ASSOC. rewrite H16 by lia. now cbn. }
        repeat rewrite PTree.gso by lia.
        destruct (peq r0 (mod_st m)); subst.
        { rewrite PTree.gss. rewrite !PTree.gso by lia.
          rewrite PTree.gss. auto. }
        repeat rewrite PTree.gso by lia.
        repeat rewrite merge_get_default3 by (now repeat rewrite AssocMap.gso by lia).
        repeat rewrite PTree.gso by lia. inv ASSOC.
        apply H16. lia.
      * repeat apply merge_arr_empty2; mgen_crush_local.
      * auto.
      * mgen_crush_local.
      * mgen_crush_local.
      * unfold disable_ram. unfold transf_module; destruct_match; try discriminate; cbn in *.
        rewrite H8 in *. cbn in *. inv Heqo. cbn. 2: { auto. }
        pose proof (mod_st_lt m).
        rewrite ! merge_get_default2 by auto.
        repeat rewrite find_assocmap_gso by lia.
        unfold empty_assocmap.
        rewrite !merge_get_default2; auto.
        rewrite !assocmap_gso by lia. rewrite assocmap_gss.
        assert ((Int.eq vc (ZToValue 0)) = true). {
      unfold Int.eq.
      unfold valueToBool, uvalueToZ in *. destruct_match; try discriminate; auto. 
      destruct_match; try discriminate. eapply Z.eqb_eq in Heqb. clear Heqs. rewrite Heqb in n.
      replace (Int.unsigned (ZToValue 0)) with 0%Z in n by auto. lia. }
      rewrite H14. cbn. unfold boolToValue, natToValue. cbn. unfold Int.neg.
      replace (Int.repr (- Int.unsigned (Int.repr 0))) with (Int.zero) by auto.
      rewrite Int.xor_commut. rewrite Int.xor_zero.
      unfold disable_ram, transf_module in DISABLE_RAM;
      repeat destruct_match; try discriminate. cbn in *. inv Heqo. assumption.
Qed.


Lemma translation_correct :
  forall m asr basr2 nasr2 nasa2 basa2 nasr3 basr3
         nasa3 basa3 asr'0 asa'0 res' st tge pstval sf asa data f,
    asr ! (mod_reset m) = Some (ZToValue 0) ->
    asr ! (mod_finish m) = Some (ZToValue 0) ->
    asr ! (mod_st m) = Some (posToValue st) ->
    (mod_datapath m) ! st = Some data ->
    stmnt_runp f {| assoc_blocking := asr; assoc_nonblocking := empty_assocmap |}
               {| assoc_blocking := asa; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} data
               {| assoc_blocking := basr2; assoc_nonblocking := nasr2 |}
               {| assoc_blocking := basa2; assoc_nonblocking := nasa2 |} ->
    exec_ram {| assoc_blocking := merge_regs nasr2 basr2; assoc_nonblocking := empty_assocmap |}
             {| assoc_blocking := merge_arrs nasa2 basa2; assoc_nonblocking := empty_stack (mod_stk m) (mod_stk_len m) |} None
             {| assoc_blocking := basr3; assoc_nonblocking := nasr3 |}
             {| assoc_blocking := basa3; assoc_nonblocking := nasa3 |} ->
    (merge_regs nasr3 basr3) ! (mod_st m) = Some (posToValue pstval) ->
    (Z.pos pstval <= 4294967295)%Z ->
    match_states (State sf m st asr asa) (State res' (transf_module m) st asr'0 asa'0) ->
    mod_ram m = None ->
    exists R2 : state,
      Smallstep.plus step tge (State res' (transf_module m) st asr'0 asa'0) Events.E0 R2 /\
      match_states (State sf m pstval (merge_regs nasr3 basr3) (merge_arrs nasa3 basa3)) R2.
Proof.
  intros.
  repeat match goal with
  | H: match_states _ _ |- _ => inv H
  | H: context[exec_ram] |- _ => inv H
  | H: mod_ram _ = None |- _ =>
    let H2 := fresh "TRANSF" in learn H as H2; apply transf_module_code in H2
  end.
  eapply transf_code_alternatives in TRANSF; eauto; simplify_local; unfold alternatives in *.
  repeat match goal with H: _ \/ _ |- _ => inv H end.
  - eapply translation_correct_unchanged; eassumption.
  - eapply translation_correct_store; eassumption.
  - eapply translation_correct_load; eassumption.
  - eapply translation_correct_store_cond; eassumption.
  - eapply translation_correct_load_cond; eassumption.
Qed.

Lemma exec_ram_resets_en :
  forall rs ar rs' ar' r,
    exec_ram rs ar (Some r) rs' ar' ->
    assoc_nonblocking rs = empty_assocmap ->
    Int.eq ((assoc_blocking (merge_reg_assocs rs')) # (ram_en r, 32))
           ((assoc_blocking (merge_reg_assocs rs')) # (ram_u_en r, 32)) = true.
Proof.
  inversion 1; intros; subst; unfold merge_reg_assocs; simplify_local.
  - rewrite H6. repeat rewrite merge_get_default2 by auto. auto.
  - unfold merge_regs. rewrite H12. pose proof (ram_ordering r).
    erewrite 1 ! merge_get_default; [erewrite 1 ! merge_get_default2|];
      [| rewrite AssocMap.gso by lia | rewrite AssocMap.gss ]; auto.
    unfold "#", AssocMapExt.get_default. rewrite H4.
    apply Int.eq_true.
  - unfold merge_regs. rewrite H11.
    pose proof (ram_ordering r).
    erewrite 1 ! merge_get_default;
      [erewrite 1 ! merge_get_default2|];
      [| now repeat rewrite AssocMap.gso by lia | now rewrite AssocMap.gss].
    unfold "#", AssocMapExt.get_default. rewrite H3.
    apply Int.eq_true.
Qed.

Lemma disable_ram_set_gso :
  forall rs r i v,
    disable_ram (Some r) rs ->
    i <> (ram_en r) -> i <> (ram_u_en r) ->
    disable_ram (Some r) (rs # i <- v).
Proof.
  unfold disable_ram, find_assocmap, AssocMapExt.get_default; intros;
  repeat rewrite AssocMap.gso by lia; auto.
Qed.
#[local] Hint Resolve disable_ram_set_gso : mgen.

Lemma disable_ram_None rs : disable_ram None rs.
Proof. unfold disable_ram; auto. Qed.
#[local] Hint Resolve disable_ram_None : mgen.

Lemma init_regs_equal_empty l st :
  Forall (Pos.gt st) l -> (init_regs nil l) ! st = None.
Proof. induction l; simplify; apply AssocMap.gempty. Qed.

Lemma forall_lt_num :
  forall l p p', Forall (Pos.gt p) l -> p < p' -> Forall (Pos.gt p') l.
Proof. induction l; crush; inv H; constructor; [lia | eauto]. Qed.

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
        exists R2, Smallstep.plus step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    Ltac transf_step_correct_assum :=
      match goal with
      | H: match_states _ _ |- _ => let H2 := fresh "MATCH" in learn H as H2; inv H2
      | H: mod_ram ?m = Some ?r |- _ =>
        let H2 := fresh "RAM" in learn H;
          pose proof (transf_module_code_ram m r H) as H2
      | H: mod_ram ?m = None |- _ =>
        let H2 := fresh "RAM" in learn H;
          pose proof (transf_module_code m H) as H2
      end.
    Ltac transf_step_correct_tac :=
      match goal with
      | |- Smallstep.plus _ _ _ _ _ => apply Smallstep.plus_one
      end.
    induction 1; destruct (mod_ram m) eqn:RAM; simplify; repeat transf_step_correct_assum;
      repeat transf_step_correct_tac.
    - (* assert (MATCH_SIZE1: match_empty_size m nasa1 /\ match_empty_size m basa1). *)
      (* { eapply match_arrs_size_stmnt_preserved2; eauto. unfold match_empty_size; mgen_crush. } *)
      (* simplify. *)
      assert (MATCH_SIZE2: match_empty_size m nasa2 /\ match_empty_size m basa2).
      { eapply match_arrs_size_stmnt_preserved2; mgen_crush. } simplify.
      assert (MATCH_SIZE3: match_empty_size m nasa3 /\ match_empty_size m basa3).
      { eapply match_arrs_size_ram_preserved2; mgen_crush. } simplify.
      assert (MATCH_ARR3: match_arrs_size nasa3 basa3) by mgen_crush.
      exploit match_states_same. eauto with mgen. eauto with mgen.
      econstructor; eauto. econstructor; eauto. econstructor; eauto. econstructor; eauto.
      intros. repeat inv_exists. simplify. inv H13. inv H16.
      exploit exec_ram_same; eauto. eauto with mgen.
      econstructor. eapply match_assocmaps_merge; eauto. eauto with mgen.
      econstructor.
      apply match_arrs_merge; eauto with mgen. eauto with mgen.
      intros. repeat inv_exists. simplify. inv H13. inv H18.
      econstructor; simplify. apply Smallstep.plus_one. econstructor.
      mgen_crush. mgen_crush. mgen_crush. rewrite RAM0; eassumption. rewrite RAM0; eassumption.
      rewrite ! RAM0 in H15. rewrite ! RAM0. rewrite H5. 
      eassumption. eauto. eauto. eauto with mgen. eauto.
      econstructor. mgen_crush. apply match_arrs_merge; mgen_crush. eauto.
      apply match_empty_size_merge; mgen_crush; mgen_crush.
      assert (MATCH_SIZE1': match_empty_size m ran'0 /\ match_empty_size m rab'0).
      { eapply match_arrs_size_stmnt_preserved2; eauto. unfold match_empty_size; mgen_crush. }
      simplify.
      assert (MATCH_SIZE2': match_empty_size m ran'2 /\ match_empty_size m rab'2).
      { eapply match_arrs_size_ram_preserved2; mgen_crush.
        unfold match_empty_size, transf_module, empty_stack.
        repeat destruct_match; crush. mgen_crush.  }
      apply match_empty_size_merge; mgen_crush; mgen_crush.
      unfold disable_ram.
      unfold transf_module; repeat destruct_match; crush.
      apply exec_ram_resets_en in H15.
      unfold merge_reg_assocs in H15.
      simplify. auto. auto.
    - eapply translation_correct; eauto.
    - do 2 econstructor. apply Smallstep.plus_one.
      apply step_finish; mgen_crush. constructor; eauto.
    - do 2 econstructor. apply Smallstep.plus_one.
      apply step_finish; mgen_crush. econstructor; eauto.
    - econstructor. econstructor. apply Smallstep.plus_one. econstructor.
      replace (mod_entrypoint (transf_module m)) with (mod_entrypoint m) by (rewrite RAM0; auto).
      replace (mod_reset (transf_module m)) with (mod_reset m) by (rewrite RAM0; auto).
      replace (mod_finish (transf_module m)) with (mod_finish m) by (rewrite RAM0; auto).
      replace (empty_stack (mod_stk (transf_module m)) (mod_stk_len (transf_module m))) with (empty_stack (mod_stk m) (mod_stk_len m)) by (rewrite RAM0; auto).
      replace (mod_params (transf_module m)) with (mod_params m) by (rewrite RAM0; auto).
      replace (mod_st (transf_module m)) with (mod_st m) by (rewrite RAM0; auto).
      repeat econstructor; mgen_crush.
      unfold disable_ram. unfold transf_module; repeat destruct_match; crush.
      pose proof (mod_ordering_wf m); unfold module_ordering in *.
      pose proof (mod_params_wf m).
      pose proof (mod_ram_wf m r Heqo0).
      pose proof (ram_ordering r).
      simplify.
      repeat rewrite find_assocmap_gso by lia.
      assert ((init_regs nil (mod_params m)) ! (ram_en r) = None).
      { apply init_regs_equal_empty. eapply forall_lt_num. eassumption. lia. }
      assert ((init_regs nil (mod_params m)) ! (ram_u_en r) = None).
      { apply init_regs_equal_empty. eapply forall_lt_num. eassumption. lia. }
      unfold find_assocmap, AssocMapExt.get_default. rewrite H7. rewrite H14. auto.
    - econstructor. econstructor. apply Smallstep.plus_one. econstructor.
      replace (mod_entrypoint (transf_module m)) with (mod_entrypoint m).
      replace (mod_reset (transf_module m)) with (mod_reset m).
      replace (mod_finish (transf_module m)) with (mod_finish m).
      replace (empty_stack (mod_stk (transf_module m)) (mod_stk_len (transf_module m))) with (empty_stack (mod_stk m) (mod_stk_len m)).
      replace (mod_params (transf_module m)) with (mod_params m).
      replace (mod_st (transf_module m)) with (mod_st m).
      all: try solve [unfold transf_module; repeat destruct_match; mgen_crush].
      repeat econstructor; mgen_crush.
      unfold disable_ram. unfold transf_module; repeat destruct_match; crush.
      unfold max_reg_module.
      repeat rewrite find_assocmap_gso by lia.
      assert (max_reg_module m + 1 > max_list (mod_params m)).
      { unfold max_reg_module. lia. }
      apply max_list_correct in H0.
      unfold find_assocmap, AssocMapExt.get_default.
      rewrite init_regs_equal_empty. rewrite init_regs_equal_empty. auto.
      eapply forall_lt_num. eassumption. unfold max_reg_module. lia.
      eapply forall_lt_num. eassumption. unfold max_reg_module. lia.
    - inv STACKS. destruct b1; subst.
      econstructor. econstructor. apply Smallstep.plus_one.
      econstructor. eauto.
      clear Learn. inv H0. inv H3. inv STACKS. inv H3. constructor.
      constructor. intros.
      rewrite RAM0.
      destruct (Pos.eq_dec r res); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss. auto.
      rewrite AssocMap.gso; auto.
      symmetry. rewrite AssocMap.gso; auto.
      destruct (Pos.eq_dec (mod_st m) r); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss. auto.
      rewrite AssocMap.gso; auto.
      symmetry. rewrite AssocMap.gso; auto. inv MATCH_ASSOC0. apply H1. auto.
      auto. auto. auto. auto.
      rewrite RAM0. rewrite RAM. rewrite RAM0 in DISABLE_RAM. rewrite RAM in DISABLE_RAM.
      apply disable_ram_set_gso.
      apply disable_ram_set_gso. auto.
      pose proof (mod_ordering_wf m); unfold module_ordering in *.
      pose proof (ram_ordering r0). simplify.
      pose proof (mod_ram_wf m r0 H). lia.
      pose proof (mod_ordering_wf m); unfold module_ordering in *.
      pose proof (ram_ordering r0). simplify.
      pose proof (mod_ram_wf m r0 H). lia.
      pose proof (mod_ordering_wf m); unfold module_ordering in *.
      pose proof (ram_ordering r0). simplify.
      pose proof (mod_ram_wf m r0 H). lia.
      pose proof (mod_ordering_wf m); unfold module_ordering in *.
      pose proof (ram_ordering r0). simplify.
      pose proof (mod_ram_wf m r0 H). lia.
    - inv STACKS. destruct b1; subst.
      econstructor. econstructor. apply Smallstep.plus_one.
      econstructor. eauto.
      clear Learn. inv H0. inv H3. inv STACKS. constructor.
      constructor. intros.
      unfold transf_module. repeat destruct_match; crush.
      destruct (Pos.eq_dec r res); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss. auto.
      rewrite AssocMap.gso; auto.
      symmetry. rewrite AssocMap.gso; auto.
      destruct (Pos.eq_dec (mod_st m) r); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss. auto.
      rewrite AssocMap.gso; auto.
      symmetry. rewrite AssocMap.gso; auto. inv MATCH_ASSOC. apply H. auto.
      auto. auto. auto. auto.
      Opaque disable_ram.
      unfold transf_module in *; repeat destruct_match; crush.
      apply disable_ram_set_gso.
      apply disable_ram_set_gso.
      auto.
      simplify. unfold max_reg_module. lia.
      simplify. unfold max_reg_module. lia.
      simplify. unfold max_reg_module. lia.
      simplify. unfold max_reg_module. lia.
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
    eapply Smallstep.forward_simulation_plus; mgen_crush.
    apply senv_preserved.
  Qed.

End CORRECTNESS.
