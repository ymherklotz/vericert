(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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
Require Import vericert.hls.HTL.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.

Local Open Scope positive.
Local Open Scope assocmap.

Definition max_pc_function (m: module) :=
  List.fold_left Pos.max (List.map fst (PTree.elements m.(mod_controllogic))) 1.

Fixpoint max_reg_expr (e: expr) :=
  match e with
  | Vlit _ => 1
  | Vvar r => r
  | Vvari r e => Pos.max r (max_reg_expr e)
  | Vrange r e1 e2 => Pos.max r (Pos.max (max_reg_expr e1) (max_reg_expr e2))
  | Vinputvar r => r
  | Vbinop _ e1 e2 => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  | Vunop _ e => max_reg_expr e
  | Vternary e1 e2 e3 => Pos.max (max_reg_expr e1) (Pos.max (max_reg_expr e2) (max_reg_expr e3))
  end.

Fixpoint max_reg_stmnt (st: stmnt) :=
  match st with
  | Vskip => 1
  | Vseq s1 s2 => Pos.max (max_reg_stmnt s1) (max_reg_stmnt s2)
  | Vcond e s1 s2 =>
    Pos.max (max_reg_expr e)
            (Pos.max (max_reg_stmnt s1) (max_reg_stmnt s2))
  | Vcase e stl None => Pos.max (max_reg_expr e) (max_reg_stmnt_expr_list stl)
  | Vcase e stl (Some s) =>
    Pos.max (max_reg_stmnt s)
            (Pos.max (max_reg_expr e) (max_reg_stmnt_expr_list stl))
  | Vblock e1 e2 => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  | Vnonblock e1 e2 => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  end
with max_reg_stmnt_expr_list (stl: stmnt_expr_list) :=
  match stl with
  | Stmntnil => 1
  | Stmntcons e s stl' =>
    Pos.max (max_reg_expr e)
            (Pos.max (max_reg_stmnt s)
                     (max_reg_stmnt_expr_list stl'))
  end.

Definition max_list := fold_right Pos.max 1.

Definition max_stmnt_tree t :=
  PTree.fold (fun i _ st => Pos.max (max_reg_stmnt st) i) t 1.

Definition max_reg_module m :=
  Pos.max (max_list (mod_params m))
   (Pos.max (max_stmnt_tree (mod_datapath m))
    (Pos.max (max_stmnt_tree (mod_controllogic m))
     (Pos.max (mod_st m)
      (Pos.max (mod_stk m)
       (Pos.max (mod_finish m)
        (Pos.max (mod_return m)
         (Pos.max (mod_start m)
          (Pos.max (mod_reset m) (mod_clk m))))))))).

Definition transf_maps state ram i (dc: node * PTree.t stmnt * PTree.t stmnt) :=
  match dc with
  | (n, d, c) =>
    match PTree.get i d, PTree.get i c with
    | Some d_s, Some c_s =>
      match d_s with
      | Vnonblock (Vvari r e1) e2 =>
        let nd := Vseq (Vnonblock (Vvar (ram_en ram)) (Vlit (ZToValue 1)))
                    (Vseq (Vnonblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                       (Vseq (Vnonblock (Vvar (ram_d_in ram)) e2)
                             (Vnonblock (Vvar (ram_addr ram)) e1)))
        in
        (n, PTree.set i nd d, c)
      | Vnonblock e1 (Vvari r e2) =>
        let nd :=
            Vseq (Vnonblock (Vvar (ram_en ram)) (Vlit (ZToValue 1)))
                 (Vseq (Vnonblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                       (Vnonblock (Vvar (ram_addr ram)) e2))
        in
        let aout := Vnonblock e1 (Vvar (ram_d_out ram)) in
        let redirect := Vnonblock (Vvar state) (Vlit (posToValue n)) in
        (n+1, PTree.set i nd (PTree.set n aout d),
         PTree.set i redirect (PTree.set n c_s c))
      | _ => dc
      end
    | _, _ => dc
    end
  end.

Lemma transf_maps_wf :
  forall state ram n d c n' d' c' i,
    map_well_formed c /\ map_well_formed d ->
    transf_maps state ram i (n, d, c) = (n', d', c') ->
    map_well_formed c' /\ map_well_formed d'.
Proof.
  unfold map_well_formed; simplify;
    repeat destruct_match;
    match goal with | H: (_, _, _) = (_, _, _) |- _ => inv H end; eauto;
      simplify.
  apply H2.
  exploit list_in_map_inv; eauto; intros.
  inv H0. destruct x. inv H3. simplify.
  replace p with (fst (p, s)) by auto.
  apply in_map.
  apply PTree.elements_correct.
  apply PTree.elements_complete in H4.
Abort.

Definition set_mod_datapath d c wf m :=
  mkmodule (mod_params m)
           d
           c
           (mod_entrypoint m)
           (mod_st m)
           (mod_stk m)
           (mod_stk_len m)
           (mod_finish m)
           (mod_return m)
           (mod_start m)
           (mod_reset m)
           (mod_clk m)
           (mod_scldecls m)
           (mod_arrdecls m)
           (mod_ram m)
           wf.

Lemma is_wf:
  forall A nc nd,
    @map_well_formed A nc /\ @map_well_formed A nd.
Admitted.

Definition max_pc {A: Type} (m: PTree.t A) :=
  fold_right Pos.max 1%positive (map fst (PTree.elements m)).

Definition transf_code state ram d c :=
  match fold_right (transf_maps state ram)
                   (max_pc d + 1, d, c)
                   (map fst (PTree.elements d)) with
  | (_, d', c') => (d', c')
  end.

Definition transf_module (m: module): module :=
  let max_reg := max_reg_module m in
  let addr := max_reg+1 in
  let en := max_reg+2 in
  let d_in := max_reg+3 in
  let d_out := max_reg+4 in
  let wr_en := max_reg+5 in
  let new_size := (2 ^ Nat.log2_up m.(mod_stk_len))%nat in
  let ram := mk_ram new_size (mod_stk m) en addr d_in d_out wr_en in
  match transf_code (mod_st m) ram (mod_datapath m) (mod_controllogic m), (mod_ram m) with
  | (nd, nc), None =>
    mkmodule m.(mod_params)
                 nd
                 nc
                 (mod_entrypoint m)
                 (mod_st m)
                 (mod_stk m)
                 (mod_stk_len m)
                 (mod_finish m)
                 (mod_return m)
                 (mod_start m)
                 (mod_reset m)
                 (mod_clk m)
                 (AssocMap.set en (None, VScalar 32)
                  (AssocMap.set wr_en (None, VScalar 32)
                   (AssocMap.set d_out (None, VScalar 32)
                    (AssocMap.set d_in (None, VScalar 32)
                     (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls))))))
                      (AssocMap.set m.(mod_stk) (None, VArray 32 new_size)%nat m.(mod_arrdecls))
                 (Some ram)
                 (is_wf _ nc nd)
  | _, _ => m
  end.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : program) :=
  transform_program transf_fundef p.

Inductive match_assocmaps : positive -> assocmap -> assocmap -> Prop :=
  match_assocmap: forall p rs rs',
    (forall r, r < p -> rs!r = rs'!r) ->
    match_assocmaps p rs rs'.

Inductive match_arrs : assocmap_arr -> assocmap_arr -> Prop :=
  match_assocmap_arr: forall ar ar',
    (forall s arr,
        ar ! s = Some arr ->
        exists arr',
          ar' ! s = Some arr'
          /\ (forall addr,
                 array_get_error addr arr = array_get_error addr arr')
          /\ arr_length arr = arr_length arr')%nat ->
    match_arrs ar ar'.

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr' asa',
      match_assocmaps (max_reg_module m + 1) asr asr' ->
      match_arrs asa asa' ->
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r (transf_module m) pc asr' asa').

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa'
           (ASSOC: match_assocmaps (max_reg_module m + 1) asr asr')
           (ARRS: match_arrs asa asa')
           (STACKS: list_forall2 match_stackframes res res'),
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
Hint Constructors match_states : htlproof.

Definition empty_stack_ram r :=
  AssocMap.set (ram_mem r) (Array.arr_repeat None (ram_size r)) (AssocMap.empty arr).

Definition empty_stack' len st :=
  AssocMap.set st (Array.arr_repeat None len) (AssocMap.empty arr).

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
Hint Resolve match_assocmaps_equiv : mgen.

Lemma match_arrs_equiv : forall a, match_arrs a a.
Proof. econstructor; mgen_crush. Qed.
Hint Resolve match_arrs_equiv : mgen.

Lemma match_reg_assocs_equiv : forall p a, match_reg_assocs p a a.
Proof. destruct a; constructor; mgen_crush. Qed.
Hint Resolve match_reg_assocs_equiv : mgen.

Lemma match_arr_assocs_equiv : forall a, match_arr_assocs a a.
Proof. destruct a; constructor; mgen_crush. Qed.
Hint Resolve match_arr_assocs_equiv : mgen.

Lemma match_assocmaps_max1 :
  forall p p' a b,
    match_assocmaps (Pos.max p' p) a b ->
    match_assocmaps p a b.
Proof.
  intros. inv H. constructor. intros.
  apply H0. lia.
Qed.
Hint Resolve match_assocmaps_max1 : mgen.

Lemma match_assocmaps_max2 :
  forall p p' a b,
    match_assocmaps (Pos.max p p') a b ->
    match_assocmaps p a b.
Proof.
  intros. inv H. constructor. intros.
  apply H0. lia.
Qed.
Hint Resolve match_assocmaps_max2 : mgen.

Lemma match_assocmaps_ge :
  forall p p' a b,
    match_assocmaps p' a b ->
    p <= p' ->
    match_assocmaps p a b.
Proof.
  intros. inv H. constructor. intros.
  apply H1. lia.
Qed.
Hint Resolve match_assocmaps_ge : mgen.

Lemma match_reg_assocs_max1 :
  forall p p' a b,
    match_reg_assocs (Pos.max p' p) a b ->
    match_reg_assocs p a b.
Proof. intros; inv H; econstructor; mgen_crush. Qed.
Hint Resolve match_reg_assocs_max1 : mgen.

Lemma match_reg_assocs_max2 :
  forall p p' a b,
    match_reg_assocs (Pos.max p p') a b ->
    match_reg_assocs p a b.
Proof. intros; inv H; econstructor; mgen_crush. Qed.
Hint Resolve match_reg_assocs_max2 : mgen.

Lemma match_reg_assocs_ge :
  forall p p' a b,
    match_reg_assocs p' a b ->
    p <= p' ->
    match_reg_assocs p a b.
Proof. intros; inv H; econstructor; mgen_crush. Qed.
Hint Resolve match_reg_assocs_ge : mgen.

Definition forall_ram (P: reg -> Prop) ram :=
  P (ram_mem ram)
  /\ P (ram_en ram)
  /\ P (ram_addr ram)
  /\ P (ram_wr_en ram)
  /\ P (ram_d_in ram)
  /\ P (ram_d_out ram).

Definition exec_all d_s c_s rs1 ar1 rs3 ar3 :=
  exists f rs2 ar2,
    stmnt_runp f rs1 ar1 c_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 d_s rs3 ar3.

Definition exec_all_ram r d_s c_s rs1 ar1 rs4 ar4 :=
  exists f rs2 ar2 rs3 ar3,
    stmnt_runp f rs1 ar1 c_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 d_s rs3 ar3
    /\ exec_ram (merge_reg_assocs rs3) (merge_arr_assocs (ram_mem r) (ram_size r) ar3) (Some r) rs4 ar4.

Lemma merge_reg_idempotent :
  forall rs, merge_reg_assocs (merge_reg_assocs rs) = merge_reg_assocs rs.
Proof. auto. Qed.
Hint Rewrite merge_reg_idempotent : mgen.

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
  split; simplify; eauto.
  unfold merge_arrs.
  rewrite AssocMap.gcombine by reflexivity.
  unfold empty_stack'.
  rewrite AssocMap.gss.
  setoid_rewrite merge_arr_empty2; auto.
  rewrite AssocMap.gcombine by reflexivity.
  unfold merge_arr, arr.
  rewrite H. rewrite H0. auto.
  unfold combine.
  simplify.
  rewrite list_combine_length.
  rewrite (arr_wf v). rewrite (arr_wf v').
  lia.
Qed.

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
  intros. unfold find_assocmap. unfold AssocMapExt.get_default.
  rewrite H. auto.
Qed.
Hint Resolve find_assoc_get : mgen.

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
    unfold arr in *. rewrite H1. inv H4.
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
Qed.
Hint Resolve expr_runp_matches : mgen.

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
Hint Resolve expr_runp_matches2 : mgen.

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
Hint Resolve match_assocmaps_gss : mgen.

Lemma match_reg_assocs_block :
  forall p rab rab' r rhsval,
    match_reg_assocs p rab rab' ->
    match_reg_assocs p (block_reg r rab rhsval) (block_reg r rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
Hint Resolve match_reg_assocs_block : mgen.

Lemma match_reg_assocs_nonblock :
  forall p rab rab' r rhsval,
    match_reg_assocs p rab rab' ->
    match_reg_assocs p (nonblock_reg r rab rhsval) (nonblock_reg r rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
Hint Resolve match_reg_assocs_nonblock : mgen.

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

Lemma match_arrs_gss :
  forall ar ar' r v i,
    match_arrs ar ar' ->
    match_arrs (arr_assocmap_set r i v ar) (arr_assocmap_set r i v ar').
Proof.
  intros. inv H. constructor. intros.
  unfold arr_assocmap_set in *.
  destruct (Pos.eq_dec s r); subst.
  destruct ar ! r eqn:?. rewrite AssocMap.gss in H. inv H.
  apply H0 in Heqo. inv Heqo. inv H.
  eexists. simplify.
  unfold arr in *.
  rewrite H1. rewrite AssocMap.gss. simplify.
  intros.
  Admitted.

Hint Resolve match_arrs_gss : mgen.

Lemma match_arr_assocs_block :
  forall rab rab' r i rhsval,
    match_arr_assocs rab rab' ->
    match_arr_assocs (block_arr r i rab rhsval) (block_arr r i rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
Hint Resolve match_arr_assocs_block : mgen.

Lemma match_arr_assocs_nonblock :
  forall rab rab' r i rhsval,
    match_arr_assocs rab rab' ->
    match_arr_assocs (nonblock_arr r i rab rhsval) (nonblock_arr r i rab' rhsval).
Proof. inversion 1; econstructor; eauto with mgen. Qed.
Hint Resolve match_arr_assocs_nonblock : mgen.

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

Definition behaviour_correct d c d' c' r :=
  forall p rs1 ar1 rs2 ar2 trs1 tar1 d_s c_s i v v',
    PTree.get i d = Some d_s ->
    PTree.get i c = Some c_s ->
    ram_present ar1 r v v' ->
    ram_present ar2 r v v' ->
    exec_all d_s c_s rs1 ar1 rs2 ar2 ->
    match_reg_assocs p rs1 trs1 ->
    match_arr_assocs ar1 tar1 ->
    Pos.max (max_stmnt_tree d) (max_stmnt_tree c) < p ->
    exists d_s' c_s' trs2 tar2,
      PTree.get i d' = Some d_s'
      /\ PTree.get i c' = Some c_s'
      /\ exec_all_ram r d_s' c_s' trs1 tar1 trs2 tar2
      /\ match_reg_assocs p (merge_reg_assocs rs2) (merge_reg_assocs trs2)
      /\ match_arr_assocs (merge_arr_assocs (ram_mem r) (ram_size r) ar2)
                          (merge_arr_assocs (ram_mem r) (ram_size r) tar2).

Lemma match_reg_assocs_merge :
  forall p rs rs',
    match_reg_assocs p rs rs' ->
    match_reg_assocs p (merge_reg_assocs rs) (merge_reg_assocs rs').
Proof. Admitted.
Hint Resolve match_reg_assocs_merge : mgen.

Lemma behaviour_correct_equiv :
  forall d c r,
    forall_ram (fun x => max_stmnt_tree d < x /\ max_stmnt_tree c < x) r ->
    behaviour_correct d c d c r.
Proof.
  intros; unfold behaviour_correct.
  intros. exists d_s. exists c_s.
  unfold exec_all in *. inv H3. inv H4. inv H3. inv H4. inv H3.
  exploit match_states_same.
  apply H4. instantiate (1 := p). admit.
  eassumption. eassumption. intros.
  inv H3. inv H11. inv H3. inv H12.
  exploit match_states_same.
  apply H10. instantiate (1 := p). admit.
  eassumption. eassumption. intros.
  inv H12. inv H14. inv H12. inv H15.
  econstructor. econstructor.
  simplify; auto.
  unfold exec_all_ram.
  do 5 econstructor.
  simplify.
  eassumption. eassumption.
  eapply exec_ram_Some_idle. admit.
  rewrite merge_reg_idempotent.
  eauto with mgen.
  admit.
(*  unfold find_assocmap. unfold AssocMapExt.get_default.
  assert ((assoc_blocking (merge_reg_assocs rs2)) ! (ram_en r) = None) by admit.
  destruct_match; try discriminate; auto.
  constructor; constructor; auto.
  constructor; constructor; crush.
  assert (Some arr = Some arr').
  {
    rewrite <- H8. rewrite <- H10.
    symmetry.
    assert (s = (ram_mem r)) by admit; subst.
    eapply merge_arr_idempotent.
    unfold ram_present in *.
    simplify.
    all: eauto.
  }
  inv H11; auto.*)
Admitted.
Hint Resolve behaviour_correct_equiv : mgen.

Lemma stmnt_runp_gtassoc :
  forall st rs1 ar1 rs2 ar2 f,
    stmnt_runp f rs1 ar1 st rs2 ar2 ->
    forall p v,
      max_reg_stmnt st < p ->
      (assoc_nonblocking rs1)!p = None ->
      exists rs2',
        stmnt_runp f (nonblock_reg p rs1 v) ar1 st rs2' ar2
        /\ match_reg_assocs p rs2 rs2'
        /\ (assoc_nonblocking rs2')!p = Some v.
Proof.
Abort.
(*  induction 1; simplify.
  - repeat econstructor. destruct (nonblock_reg p ar v) eqn:?; destruct ar. simplify.
    constructor. inv Heqa. mgen_crush.
    inv Heqa. constructor. intros.
  - econstructor; [apply IHstmnt_runp1; lia | apply IHstmnt_runp2; lia].
  - econstructor; eauto; apply IHstmnt_runp; lia.
  - eapply stmnt_runp_Vcond_false; eauto; apply IHstmnt_runp; lia.
  - econstructor; simplify; eauto; apply IHstmnt_runp;
    destruct def; lia.
  - eapply stmnt_runp_Vcase_match; simplify; eauto; apply IHstmnt_runp;
    destruct def; lia.
  - eapply stmnt_runp_Vcase_default; simplify; eauto; apply IHstmnt_runp; lia.
  -*)

Lemma transf_not_changed :
  forall state ram n d c i d_s c_s,
    (forall e1 e2 r, d_s <> Vnonblock (Vvari r e1) e2) ->
    (forall e1 e2 r, d_s <> Vnonblock e1 (Vvari r e2)) ->
    d!i = Some d_s ->
    c!i = Some c_s ->
    transf_maps state ram i (n, d, c) = (n, d, c).
Proof. intros; unfold transf_maps; repeat destruct_match; mgen_crush. Qed.

Lemma transf_not_changed_neq :
  forall state ram n d c n' d' c' i a d_s c_s,
    transf_maps state ram a (n, d, c) = (n', d', c') ->
    d!i = Some d_s ->
    c!i = Some c_s ->
    a <> i -> n <> i ->
    d'!i = Some d_s /\ c'!i = Some c_s.
Proof.
  unfold transf_maps; intros; repeat destruct_match; mgen_crush;
  match goal with [ H: (_, _, _) = (_, _, _) |- _ ] => inv H end;
  repeat (rewrite AssocMap.gso; auto).
Qed.

Lemma transf_gteq :
  forall state ram n d c n' d' c' i,
    transf_maps state ram i (n, d, c) = (n', d', c') -> n <= n'.
Proof.
  unfold transf_maps; intros; repeat destruct_match; mgen_crush;
  match goal with [ H: (_, _, _) = (_, _, _) |- _ ] => inv H end; lia.
Qed.

Lemma transf_fold_gteq :
  forall l state ram n d c n' d' c',
    fold_right (transf_maps state ram) (n, d, c) l = (n', d', c') -> n <= n'.
Proof.
  induction l; simplify;
    [match goal with [ H: (_, _, _) = (_, _, _) |- _ ] => inv H end; lia|].
  remember (fold_right (transf_maps state ram) (n, d, c) l). repeat destruct p.
  apply transf_gteq in H. symmetry in Heqp. eapply IHl in Heqp. lia.
Qed.

Lemma transf_fold_not_changed :
  forall l state ram d c d' c' n n',
    fold_right (transf_maps state ram) (n, d, c) l = (n', d', c') ->
    Forall (fun x => n > x) l ->
    list_norepet l ->
    (forall i d_s c_s,
        n > i ->
        (forall e1 e2 r, d_s <> Vnonblock (Vvari r e1) e2) ->
        (forall e1 e2 r, d_s <> Vnonblock e1 (Vvari r e2)) ->
        d!i = Some d_s ->
        c!i = Some c_s ->
        d'!i = Some d_s /\ c'!i = Some c_s).
Proof.
  induction l as [| a l IHl]; crush;
  repeat match goal with H: context[a :: l] |- _ => inv H end;
  destruct (Pos.eq_dec a i); subst;
  remember (fold_right (transf_maps state ram) (n, d, c) l);
  repeat destruct p; symmetry in Heqp;
  repeat match goal with
         | H: forall e1 e2 r, _ <> Vnonblock (Vvari _ _) _ |- _ =>
           let H12 := fresh "H" in
           let H13 := fresh "H" in
           pose proof H as H12;
           learn H as H13;
           eapply IHl in H13; eauto; inv H13;
           eapply transf_not_changed in H12; eauto
         | [ H: transf_maps _ _ _ _ = _, H2: transf_maps _ _ _ _ = _ |- _ ] =>
           rewrite H in H2; inv H2; solve [auto]
         | Hneq: a <> ?i, H: transf_maps _ _ _ _ = _ |- _ =>
           let H12 := fresh "H" in
           learn H as H12; eapply transf_not_changed_neq in H12; inv H12; eauto
         | Hneq: a <> ?i, H: fold_right _ _ _ = _ |- _ ! _ = Some _ =>
           eapply IHl in H; inv H; solve [eauto]
         | Hneq: a <> ?i, H: fold_right _ _ _ = _ |- _ <> _ =>
           apply transf_fold_gteq in H; lia
         end.
Qed.

Lemma forall_gt :
  forall l, Forall (fun x : positive => fold_right Pos.max 1 l + 1 > x) l.
Proof.
  induction l; auto.
  constructor. inv IHl; simplify; lia.
  simplify. destruct (Pos.max_dec a (fold_right Pos.max 1 l)).
  rewrite e. apply Pos.max_l_iff in e. apply Pos.le_ge in e.
  apply Forall_forall. rewrite Forall_forall in IHl.
  intros.
  assert (forall a b c, a >= c -> c > b -> a > b) by lia.
  assert (forall a b, a >= b -> a + 1 >= b + 1) by lia.
  apply H1 in e.
  apply H0 with (b := x) in e; auto.
  rewrite e; auto.
Qed.

Lemma max_index_list :
  forall A (l : list (positive * A)) i d_s,
    In (i, d_s) l ->
    list_norepet (map fst l) ->
    fold_right Pos.max 1 (map fst l) + 1 > i.
Proof.
  induction l; crush.
  inv H. inv H0. simplify. lia.
  inv H0.
  let H := fresh "H" in
  assert (H: forall a b c, b + 1 > c -> Pos.max a b + 1 > c) by lia;
  apply H; eapply IHl; eauto.
Qed.

Lemma max_index :
  forall A d i d_s,
    d ! i = Some d_s -> @max_pc A d + 1 > i.
Proof.
  unfold max_pc; eauto using max_index_list, PTree.elements_correct, PTree.elements_keys_norepet.
Qed.

Lemma transf_code_not_changed :
  forall state ram d c d' c' i d_s c_s,
    transf_code state ram d c = (d', c') ->
    (forall e1 e2 r, d_s <> Vnonblock (Vvari r e1) e2) ->
    (forall e1 e2 r, d_s <> Vnonblock e1 (Vvari r e2)) ->
    d!i = Some d_s ->
    c!i = Some c_s ->
    d'!i = Some d_s /\ c'!i = Some c_s.
Proof.
  unfold transf_code;
  intros; repeat destruct_match; inv H;
  eapply transf_fold_not_changed;
    eauto using forall_gt, PTree.elements_keys_norepet, max_index.
Qed.

Lemma transf_code_store :
  forall state ram d c d' c' i d_s c_s rs1 ar1 rs2 ar2 p trs1 tar1,
    transf_code state ram d c = (d', c') ->
    (forall r e1 e2,
        (forall e2 r, e1 <> Vvari r e2) ->
        d_s = Vnonblock (Vvari r e1) e2) ->
    d!i = Some d_s ->
    c!i = Some c_s ->
    exec_all d_s c_s rs1 ar1 rs2 ar2 ->
    match_reg_assocs p rs1 trs1 ->
    match_arr_assocs ar1 tar1 ->
    Pos.max (max_stmnt_tree c) (max_stmnt_tree d) < p ->
    exists d_s' c_s' trs2 tar2,
      d'!i = Some d_s' /\ c'!i = Some c_s'
      /\ exec_all_ram ram d_s' c_s' trs1 tar1 trs2 tar2
      /\ match_reg_assocs p (merge_reg_assocs rs2) (merge_reg_assocs trs2)
      /\ match_arr_assocs (merge_arr_assocs (ram_mem ram) (ram_size ram) ar2)
                          (merge_arr_assocs (ram_mem ram) (ram_size ram) tar2).
Proof.
  Admitted.

Lemma transf_code_all :
  forall state ram d c d' c' i d_s c_s rs1 ar1 rs2 ar2 tar1 trs1 p,
    transf_code state ram d c = (d', c') ->
    d!i = Some d_s ->
    c!i = Some c_s ->
    exec_all d_s c_s rs1 ar1 rs2 ar2 ->
    match_reg_assocs p rs1 trs1 ->
    match_arr_assocs ar1 tar1 ->
    Pos.max (max_stmnt_tree c) (max_stmnt_tree d) < p ->
    exists d_s' c_s' trs2 tar2,
      d'!i = Some d_s' /\ c'!i = Some c_s'
      /\ exec_all_ram ram d_s' c_s' trs1 tar1 trs2 tar2
      /\ match_reg_assocs p (merge_reg_assocs rs2) (merge_reg_assocs trs2)
      /\ match_arr_assocs (merge_arr_assocs (ram_mem ram) (ram_size ram) ar2)
                          (merge_arr_assocs (ram_mem ram) (ram_size ram) tar2).
Proof.
  Admitted.

Lemma transf_all :
  forall state d c d' c' ram,
    transf_code state ram d c = (d', c') ->
    behaviour_correct d c d' c' ram.
Proof. Abort.

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

Lemma exec_all_ram_Vskip :
  forall ram rs ar,
    (assoc_blocking rs)!(ram_en ram) = None ->
    (assoc_nonblocking rs)!(ram_en ram) = None ->
    exec_all_ram ram Vskip Vskip rs ar (merge_reg_assocs rs)
                 (merge_arr_assocs (ram_mem ram) (ram_size ram) ar).
Proof.
  unfold exec_all_ram.
  intros. repeat econstructor.
  unfold merge_reg_assocs.
  unfold merge_regs.
  unfold find_assocmap.
  unfold AssocMapExt.get_default.
  simplify.
  rewrite AssocMapExt.merge_correct_3; auto.
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

Lemma transf_maps_correct:
  forall state ram n d c n' d' c' i,
    transf_maps state ram i (n, d, c) = (n', d', c') ->
    behaviour_correct d c d' c' ram.
Proof. Abort.

Lemma transf_maps_correct2:
  forall state l ram n d c n' d' c',
    fold_right (transf_maps state ram) (n, d, c) l = (n', d', c') ->
    behaviour_correct d c d' c' ram.
Proof. Abort.
(*  induction l.
  - intros. simpl in *. inv H. mgen_crush.
  - intros. simpl in *.
    destruct (fold_right (transf_maps st addr d_in d_out wr_en) (n, d, c) l) eqn:?.
    destruct p.
    eapply behaviour_correct_trans.
    eapply transf_maps_correct.
    apply H. eapply IHl. apply Heqp.
Qed.*)

Lemma empty_arrs_match :
  forall m,
    match_arrs (empty_stack m) (empty_stack (transf_module m)).
Proof.
  unfold empty_stack. unfold transf_module.
  intros. destruct_match. econstructor. simplify. eexists.
  simplify. destruct_match; eauto. eauto. eauto.
Qed.
Hint Resolve empty_arrs_match : mgen.

Lemma max_module_stmnts :
  forall m,
    Pos.max (max_stmnt_tree (mod_controllogic m))
            (max_stmnt_tree (mod_datapath m)) < max_reg_module m + 1.
Proof. intros. unfold max_reg_module. lia. Qed.
Hint Resolve max_module_stmnts : mgen.

Lemma transf_module_code :
  forall m,
    mod_ram m = None ->
    transf_code (mod_st m)
                {| ram_size := 2 ^ Nat.log2_up (mod_stk_len m);
                   ram_mem := mod_stk m;
                   ram_en := max_reg_module m + 2;
                   ram_addr := max_reg_module m + 1;
                   ram_wr_en := max_reg_module m + 3;
                   ram_d_in := max_reg_module m + 4;
                   ram_d_out := max_reg_module m + 5 |}
                (mod_datapath m) (mod_controllogic m)
    = ((mod_datapath (transf_module m)), mod_controllogic (transf_module m)).
Proof. unfold transf_module; intros; repeat destruct_match; crush. Qed.
Hint Resolve transf_module_code : mgen.

Lemma transf_module_code_ram :
  forall m r, mod_ram m = Some r -> transf_module m = m.
Proof. unfold transf_module; intros; repeat destruct_match; crush. Qed.
Hint Resolve transf_module_code_ram : mgen.

Lemma mod_reset_lt : forall m, mod_reset m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
Hint Resolve mod_reset_lt : mgen.

Lemma mod_finish_lt : forall m, mod_finish m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
Hint Resolve mod_finish_lt : mgen.

Lemma mod_return_lt : forall m, mod_return m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
Hint Resolve mod_return_lt : mgen.

Lemma mod_start_lt : forall m, mod_start m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
Hint Resolve mod_start_lt : mgen.

Lemma mod_stk_lt : forall m, mod_stk m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
Hint Resolve mod_stk_lt : mgen.

Lemma mod_st_lt : forall m, mod_st m < max_reg_module m + 1.
Proof. intros; unfold max_reg_module; lia. Qed.
Hint Resolve mod_st_lt : mgen.

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
Hint Resolve mod_reset_modify : mgen.

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
Hint Resolve mod_finish_modify : mgen.

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
Hint Resolve mod_return_modify : mgen.

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
Hint Resolve mod_start_modify : mgen.

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
Hint Resolve mod_st_modify : mgen.

Section CORRECTNESS.

  Context (prog tprog: program).
  Context (TRANSL: match_prog prog tprog).

  Let ge : genv := Genv.globalenv prog.
  Let tge : genv := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.
  Hint Resolve symbols_preserved : mgen.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  Hint Resolve function_ptr_translated : mgen.

  Lemma functions_translated:
    forall (v: Values.val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transf_fundef f = tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  Hint Resolve functions_translated : mgen.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof (Genv.senv_transf TRANSL).
  Hint Resolve senv_preserved : mgen.

  Ltac inv_exists :=
    match goal with
    | H: exists _, _ |- _ => inv H
    end.

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
    - econstructor. econstructor. apply Smallstep.plus_one. econstructor; eauto with mgen.
      rewrite RAM0; eassumption. rewrite RAM0; eassumption. rewrite RAM0. admit. admit. admit. admit.
    - exploit transf_code_all; eauto. unfold exec_all.
      do 3 eexists. simplify. apply H4. apply H6. econstructor. apply ASSOC.
      instantiate (1 := empty_assocmap). econstructor. eauto. econstructor. eassumption.
      eauto with mgen.
      eauto with mgen.
      intros. simplify.
      unfold exec_all_ram in *. repeat inv_exists.
      destruct x4. destruct x5. destruct x6. destruct x7. destruct x1. destruct x2.
      econstructor. econstructor. apply Smallstep.plus_one. econstructor. simplify.
      eauto with mgen. eauto with mgen. eauto with mgen. eauto with mgen. eauto with mgen.
      unfold empty_stack in *. simplify. unfold transf_module in *.
      simplify. destruct_match. simplify. eassumption. simplify.
      admit.
      simplify. eassumption. simplify. unfold empty_stack in *. simplify.
      unfold merge_reg_assocs in *. unfold merge_arr_assocs in *. simplify.
      unfold empty_stack' in *. assert (2 ^ Nat.log2_up (mod_stk_len m) = (mod_stk_len m))%nat by admit.
      rewrite H18 in H19. unfold transf_module; repeat destruct_match; crush. rewrite H18. eassumption. auto. auto. simplify.
      instantiate (1 := pstval).
      admit. eassumption.
      admit.
    - intros. inv H1. inv ASSOC. inv ARRS.
      econstructor. econstructor. apply Smallstep.plus_one.
      apply step_finish; unfold transf_module; destruct_match; crush; eauto.
      unfold find_assocmap in *. unfold AssocMapExt.get_default in *.
      assert (mod_finish m < max_reg_module m + 1) by admit.
      apply H1 in H3. rewrite <- H3. auto.
      assert (mod_return m < max_reg_module m + 1) by admit.
      rewrite <- H1. eauto. auto. constructor. auto.
    - intros. inv H.
      econstructor. econstructor. apply Smallstep.plus_one. econstructor.
      replace (mod_entrypoint (transf_module m)) with (mod_entrypoint m).
      replace (mod_reset (transf_module m)) with (mod_reset m).
      replace (mod_finish (transf_module m)) with (mod_finish m).
      replace (empty_stack (transf_module m)) with (empty_stack m).
      replace (mod_params (transf_module m)) with (mod_params m).
      replace (mod_st (transf_module m)) with (mod_st m).
      econstructor; mgen_crush.
      all: try solve [unfold transf_module; destruct_match; crush].
      apply list_forall2_nil.
    - simplify. inv H0. inv STACKS. destruct b1. inv H1.
      econstructor. econstructor. apply Smallstep.plus_one.
      econstructor. unfold transf_module. destruct_match. simplify. eauto.
      econstructor; auto. econstructor. intros. inv H2.
      destruct (Pos.eq_dec r res); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss. auto.
      rewrite AssocMap.gso; auto.
      symmetry. rewrite AssocMap.gso; auto.
      destruct (Pos.eq_dec (mod_st m) r); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss. auto.
      rewrite AssocMap.gso; auto.
      symmetry. rewrite AssocMap.gso; auto.
  Admitted.
  Hint Resolve transf_step_correct : mgen.

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
  Hint Resolve transf_initial_states : mgen.

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
  Hint Resolve transf_final_states : mgen.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (semantics prog) (semantics tprog).
  Proof using TRANSL.
    eapply Smallstep.forward_simulation_plus; eauto with mgen.
    apply senv_preserved.
    eapply transf_final_states.
  Qed.

End CORRECTNESS.
