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

Definition max_reg_ram r :=
  match r with
  | None => 1
  | Some ram => Pos.max (ram_mem ram)
                (Pos.max (ram_en ram)
                 (Pos.max (ram_addr ram)
                  (Pos.max (ram_addr ram)
                   (Pos.max (ram_wr_en ram)
                    (Pos.max (ram_d_in ram) (ram_d_out ram))))))
  end.

Definition max_reg_module m :=
  Pos.max (max_list (mod_params m))
   (Pos.max (max_stmnt_tree (mod_datapath m))
    (Pos.max (max_stmnt_tree (mod_controllogic m))
     (Pos.max (mod_st m)
      (Pos.max (mod_stk m)
       (Pos.max (mod_finish m)
        (Pos.max (mod_return m)
         (Pos.max (mod_start m)
          (Pos.max (mod_reset m)
           (Pos.max (mod_clk m) (max_reg_ram (mod_ram m))))))))))).

Lemma max_fold_lt :
  forall m l n, m <= n -> m <= (fold_left Pos.max l n).
Proof. induction l; crush; apply IHl; lia. Qed.

Lemma max_fold_lt2 :
  forall (l: list (positive * stmnt)) v n,
    v <= n ->
    v <= fold_left (fun a p => Pos.max (max_reg_stmnt (snd p)) a) l n.
Proof. induction l; crush; apply IHl; lia. Qed.

Lemma max_fold_lt3 :
  forall (l: list (positive * stmnt)) v v',
    v <= v' ->
    fold_left (fun a0 p => Pos.max (max_reg_stmnt (snd p)) a0) l v
    <= fold_left (fun a0 p => Pos.max (max_reg_stmnt (snd p)) a0) l v'.
Proof. induction l; crush; apply IHl; lia. Qed.

Lemma max_fold_lt4 :
  forall (l: list (positive * stmnt)) (a: positive * stmnt),
    fold_left (fun a0 p => Pos.max (max_reg_stmnt (snd p)) a0) l 1
    <= fold_left (fun a0 p => Pos.max (max_reg_stmnt (snd p)) a0) l
                 (Pos.max (max_reg_stmnt (snd a)) 1).
Proof. intros; apply max_fold_lt3; lia. Qed.

Lemma max_reg_stmnt_lt_stmnt_tree':
  forall l (i: positive) v,
    In (i, v) l ->
    list_norepet (map fst l) ->
    max_reg_stmnt v <= fold_left (fun a p => Pos.max (max_reg_stmnt (snd p)) a) l 1.
Proof.
  induction l; crush. inv H; inv H0; simplify. apply max_fold_lt2. lia.
  transitivity (fold_left (fun (a : positive) (p : positive * stmnt) =>
                             Pos.max (max_reg_stmnt (snd p)) a) l 1).
  eapply IHl; eauto. apply max_fold_lt4.
Qed.

Lemma max_reg_stmnt_le_stmnt_tree :
  forall d i v,
    d ! i = Some v ->
    max_reg_stmnt v <= max_stmnt_tree d.
Proof.
  intros. unfold max_stmnt_tree. rewrite PTree.fold_spec.
  apply PTree.elements_correct in H.
  eapply max_reg_stmnt_lt_stmnt_tree'; eauto.
  apply PTree.elements_keys_norepet.
Qed.
Hint Resolve max_reg_stmnt_le_stmnt_tree : mgen.

Lemma max_reg_stmnt_lt_stmnt_tree :
  forall d i v,
    d ! i = Some v ->
    max_reg_stmnt v < max_stmnt_tree d + 1.
Proof. intros. apply max_reg_stmnt_le_stmnt_tree in H; lia. Qed.
Hint Resolve max_reg_stmnt_lt_stmnt_tree : mgen.

Lemma max_stmnt_lt_module :
  forall m d i,
    (mod_controllogic m) ! i = Some d \/ (mod_datapath m) ! i = Some d ->
    max_reg_stmnt d < max_reg_module m + 1.
Proof.
  inversion 1 as [ Hv | Hv ]; unfold max_reg_module;
  apply max_reg_stmnt_le_stmnt_tree in Hv; lia.
Qed.
Hint Resolve max_stmnt_lt_module : mgen.

Definition transf_maps state ram i (dc: node * PTree.t stmnt * PTree.t stmnt) :=
  match dc with
  | (n, d, c) =>
    match PTree.get i d, PTree.get i c with
    | Some d_s, Some c_s =>
      match d_s with
      | Vnonblock (Vvari r e1) e2 =>
        if r =? (ram_mem ram) then
          let nd := Vseq (Vnonblock (Vvar (ram_en ram)) (Vlit (ZToValue 1)))
                         (Vseq (Vnonblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                               (Vseq (Vnonblock (Vvar (ram_d_in ram)) e2)
                                     (Vnonblock (Vvar (ram_addr ram)) e1)))
          in
          (n, PTree.set i nd d, c)
        else dc
      | Vnonblock e1 (Vvari r e2) =>
        if r =? (ram_mem ram) then
          let nd :=
              Vseq (Vnonblock (Vvar (ram_en ram)) (Vlit (ZToValue 1)))
                   (Vseq (Vnonblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                         (Vnonblock (Vvar (ram_addr ram)) e2))
          in
          let aout := Vnonblock e1 (Vvar (ram_d_out ram)) in
          let redirect := Vnonblock (Vvar state) (Vlit (posToValue n)) in
          (n+1, PTree.set i nd (PTree.set n aout d),
           PTree.set i redirect (PTree.set n c_s c))
        else dc
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
  let new_size := (mod_stk_len m) in
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
                      (AssocMap.set m.(mod_stk) (None, VArray 32 (2 ^ Nat.log2_up new_size))%nat m.(mod_arrdecls))
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
  match_arrs_size (empty_stack m) ar.
Hint Unfold match_empty_size : mgen.

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr' asa',
      match_assocmaps (max_reg_module m + 1) asr asr' ->
      match_arrs asa asa' ->
      match_empty_size m asa ->
      match_empty_size m asa' ->
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r (transf_module m) pc asr' asa').

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa'
           (ASSOC: match_assocmaps (max_reg_module m + 1) asr asr')
           (ARRS: match_arrs asa asa')
           (STACKS: list_forall2 match_stackframes res res')
           (ARRS_SIZE: match_empty_size m asa)
           (ARRS_SIZE2: match_empty_size m asa'),
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

Definition match_empty_size' l s (ar : assocmap_arr) : Prop :=
  match_arrs_size (empty_stack' l s) ar.
Hint Unfold match_empty_size : mgen.

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

Lemma match_arrs_size_equiv : forall a, match_arrs_size a a.
Proof. intros; repeat econstructor; eauto. Qed.
Hint Resolve match_arrs_size_equiv : mgen.

Lemma match_stacks_equiv :
  forall m s l,
    mod_stk m = s ->
    mod_stk_len m = l ->
    empty_stack' l s = empty_stack m.
Proof. unfold empty_stack', empty_stack; mgen_crush. Qed.
Hint Rewrite match_stacks_equiv : mgen.

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
  P (ram_en ram)
  /\ P (ram_addr ram)
  /\ P (ram_wr_en ram)
  /\ P (ram_d_in ram)
  /\ P (ram_d_out ram).

Definition ram_ordering ram :=
  ram_addr ram < ram_en ram
  /\ ram_en ram < ram_d_in ram
  /\ ram_d_in ram < ram_d_out ram
  /\ ram_d_out ram < ram_wr_en ram.

Lemma forall_ram_lt :
  forall m r,
    (mod_ram m) = Some r ->
    forall_ram (fun x => x < max_reg_module m + 1) r.
Proof.
  assert (X: forall a b c, a < b + 1 -> a < Pos.max c b + 1) by lia.
  unfold forall_ram; simplify; unfold max_reg_module; repeat apply X;
  unfold max_reg_ram; rewrite H; lia.
Qed.
Hint Resolve forall_ram_lt : mgen.

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

Lemma empty_arr :
  forall m s,
    (exists l, (empty_stack m) ! s = Some (arr_repeat None l))
    \/ (empty_stack m) ! s = None.
Proof.
  unfold empty_stack. simplify.
  destruct (Pos.eq_dec s (mod_stk m)); subst.
  left. eexists. apply AssocMap.gss.
  right. rewrite AssocMap.gso; auto. apply AssocMap.gempty.
Qed.

Lemma merge_arr_empty':
  forall m ar s v,
    match_empty_size m ar ->
    (merge_arrs (empty_stack m) ar) ! s = v ->
    ar ! s = v.
Proof.
  inversion 1; subst.
  pose proof (empty_arr m s).
  simplify.
  destruct (merge_arrs (empty_stack m) ar) ! s eqn:?; subst.
  - inv H3. inv H4.
    learn H3 as H5. apply H0 in H5. inv H5. simplify.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H3 in Heqo. erewrite merge_arr_empty2 in Heqo. auto. eauto.
    rewrite list_repeat_len in H6. auto.
    learn H4 as H6. apply H2 in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H4 in Heqo. unfold Verilog.arr in *. rewrite H6 in Heqo.
    discriminate.
  - inv H3. inv H4. learn H3 as H4. apply H0 in H4. inv H4. simplify.
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
    match_arrs (merge_arrs (empty_stack m) ar) ar'.
Proof.
  inversion 1; subst; inversion 1; subst;
  econstructor; intros; apply merge_arr_empty' in H6; auto.
Qed.
Hint Resolve merge_arr_empty : mgen.

Lemma merge_arr_empty'':
  forall m ar s v,
    match_empty_size m ar ->
    ar ! s = v ->
    (merge_arrs (empty_stack m) ar) ! s = v.
Proof.
  inversion 1; subst.
  pose proof (empty_arr m s).
  simplify.
  destruct (merge_arrs (empty_stack m) ar) ! s eqn:?; subst.
  - inv H3. inv H4.
    learn H3 as H5. apply H0 in H5. inv H5. simplify.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H3 in Heqo. erewrite merge_arr_empty2 in Heqo. auto. eauto.
    rewrite list_repeat_len in H6. auto.
    learn H4 as H6. apply H2 in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto.
    rewrite H4 in Heqo. unfold Verilog.arr in *. rewrite H6 in Heqo.
    discriminate.
  - inv H3. inv H4. learn H3 as H4. apply H0 in H4. inv H4. simplify.
    rewrite list_repeat_len in H6.
    unfold merge_arrs in *. rewrite AssocMap.gcombine in Heqo; auto. rewrite H3 in Heqo.
    unfold Verilog.arr in *. rewrite H4 in Heqo.
    discriminate.
    apply H2 in H4; auto.
Qed.

Lemma merge_arr_empty_match :
  forall m ar,
    match_empty_size m ar ->
    match_empty_size m (merge_arrs (empty_stack m) ar).
Proof.
  inversion 1; subst.
  constructor; simplify.
  learn H3 as H4. apply H0 in H4. inv H4. simplify.
  eexists; split; eauto. apply merge_arr_empty''; eauto.
  apply merge_arr_empty' in H3; auto.
  split; simplify.
  unfold merge_arrs in H3. rewrite AssocMap.gcombine in H3; auto.
  unfold merge_arr in *.
  destruct (empty_stack m) ! s eqn:?;
           destruct ar ! s; try discriminate; eauto.
  apply merge_arr_empty''; auto. apply H2 in H3; auto.
Qed.
Hint Resolve merge_arr_empty_match : mgen.

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
Hint Resolve find_assoc_get : mgen.

Lemma find_assoc_get2 :
  forall rs p r v trs,
    (forall r, r < p -> rs ! r = trs ! r) ->
    r < p ->
    rs # r = v ->
    trs # r = v.
Proof.
  intros; unfold find_assocmap, AssocMapExt.get_default; rewrite <- H; auto.
Qed.
Hint Resolve find_assoc_get2 : mgen.

Lemma get_assoc_gt :
  forall A (rs : AssocMap.t A) p r v trs,
    (forall r, r < p -> rs ! r = trs ! r) ->
    r < p ->
    rs ! r = v ->
    trs ! r = v.
Proof. intros. rewrite <- H; auto. Qed.
Hint Resolve get_assoc_gt : mgen.

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

Lemma match_assocmaps_gt :
  forall p s ra ra' v,
    p <= s ->
    match_assocmaps p ra ra' ->
    match_assocmaps p ra (ra' # s <- v).
Proof.
  intros. inv H0. constructor.
  intros. rewrite AssocMap.gso; try lia. apply H1; auto.
Qed.
Hint Resolve match_assocmaps_gt : mgen.

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
Hint Resolve array_get_error_bound_gt : mgen.

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
Hint Resolve array_get_error_each : mgen.

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

(*Definition behaviour_correct d c d' c' r :=
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
*)

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
Hint Resolve match_reg_assocs_merge : mgen.

(*Lemma behaviour_correct_equiv :
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
*)

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
  unfold max_pc;
  eauto using max_index_list,
  PTree.elements_correct, PTree.elements_keys_norepet.
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

(*Lemma transf_all :
  forall state d c d' c' ram,
    transf_code state ram d c = (d', c') ->
    behaviour_correct d c d' c' ram.
Proof. Abort.*)

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

(*Lemma transf_maps_correct:
  forall state ram n d c n' d' c' i,
    transf_maps state ram i (n, d, c) = (n', d', c') ->
    behaviour_correct d c d' c' ram.
Proof. Abort.*)

(*Lemma transf_maps_correct2:
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
Qed.*)*)

Lemma empty_arrs_match :
  forall m,
    match_arrs (empty_stack m) (empty_stack (transf_module m)).
Proof.
  unfold empty_stack. unfold transf_module.
  intros. destruct_match. econstructor. simplify. eexists.
  simplify. destruct_match; eauto. eauto. eauto.
  intros. destruct_match. auto. simplify. auto.
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
                {| ram_size := mod_stk_len m;
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
Hint Resolve match_arrs_read : mgen.

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
      [eapply exec_ram_Some_write; [ apply H1 | apply H2 | | | | ] | | ];
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
Hint Resolve match_assocmaps_merge : mgen.

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
Hint Resolve match_empty_size_match : mgen.

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
Hint Resolve match_get_merge : mgen.

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
Hint Resolve match_empty_assocmap_set : mgen.

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
Hint Resolve match_arrs_size_stmnt_preserved2 : mgen.

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
  masrp_tac. apply H7 in H9; inv_exists; simplify. repeat masrp_tac. auto.
  repeat masrp_tac.
  repeat masrp_tac.
  repeat masrp_tac.
  destruct (Pos.eq_dec (ram_mem r) s); subst; repeat masrp_tac.
  destruct (Pos.eq_dec (ram_mem r) s); subst; repeat masrp_tac.
  apply H8 in H17; auto. apply H8 in H17; auto.
  Unshelve. eauto.
Qed.
Hint Resolve match_arrs_size_ram_preserved : mgen.

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
Hint Resolve match_arrs_size_ram_preserved2 : mgen.

(*Lemma match_arrs_merge_set' :
  forall s i v l m ran ran' rab',
    match_empty_size' l m rab ->
    match_empty_size' l m ran ->
    match_arrs ran (merge_arrs (arr_assocmap_set s i v (empty_stack' l m)) (merge_arrs ran' rab')) ->
.
Proof.
  inversion 1; inversion 1; unfold merge_arrs, arr_assocmap_set; subst; simplify.
  destruct (empty_stack' l m) ! s eqn:?. do 5 masrp_tac.
  Admitted.

Lemma set_merge_assoc :
  forall s i v ran rab,
    arr_assocmap_set s i v (merge_arrs ran rab) = merge_arrs (arr_assocmap_set s i v ran) rab.
Admitted.

Lemma merge_arrs_idem :
  forall l m s i v ran rab,
    merge_arrs (empty_stack' l m) (merge_arrs (arr_assocmap_set s i v ran) rab)
    = merge_arrs (arr_assocmap_set s i v ran) rab.
Admitted.*)

Lemma empty_stack_m :
  forall m, empty_stack m = empty_stack' (mod_stk_len m) (mod_stk m).
Proof. unfold empty_stack, empty_stack'; mgen_crush. Qed.
Hint Rewrite empty_stack_m : mgen.

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
  simpl in H. invert H.
  destruct n; simpl in *.
  invert H0. simpl. reflexivity.
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
  simpl in H. invert H.
  destruct n; simpl in *.
  invert H0. simpl. reflexivity.
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
    exists v', (empty_stack m) ! s = Some v' /\ arr_length v = arr_length v'.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_empty_size_exists_None :
  forall m rab s,
    match_empty_size m rab ->
    rab ! s = None ->
    (empty_stack m) ! s = None.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_empty_size_exists_None' :
  forall m rab s,
    match_empty_size m rab ->
    (empty_stack m) ! s = None ->
    rab ! s = None.
Proof. inversion 1; intros; repeat masrp_tac. Qed.

Lemma match_empty_size_exists_Some' :
  forall m rab s v,
    match_empty_size m rab ->
    (empty_stack m) ! s = Some v ->
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
  | H: match_empty_size _ _, H2: (empty_stack _) ! _ = Some _ |- _ =>
    let H3 := fresh "H" in
    learn H as H3; eapply match_empty_size_exists_Some' in H3;
    [| eassumption]; inv_exists; simplify
  | H: match_arrs ?ar _, H2: ?ar ! _ = Some _ |- _ =>
    let H3 := fresh "H" in
    learn H as H3; eapply match_arrs_Some in H3;
    [| eassumption]; inv_exists; simplify
  | H: match_empty_size _ _, H2: (empty_stack _) ! _ = None |- _ =>
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
Hint Resolve match_arrs_size_assoc : mgen.

Lemma match_arrs_merge_set2 :
  forall rab rab' ran ran' s m i v,
    match_empty_size m rab ->
    match_empty_size m ran ->
    match_empty_size m rab' ->
    match_empty_size m ran' ->
    match_arrs rab rab' ->
    match_arrs ran ran' ->
    match_arrs (merge_arrs (arr_assocmap_set s i v ran) rab)
               (merge_arrs (arr_assocmap_set s i v (empty_stack m))
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
  apply merge_arr_empty''; mgen_crush. apply match_empty_size_merge; auto.
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
Hint Unfold all_match_empty_size : mgen.

Definition match_module_to_ram m ram :=
  ram_size ram = mod_stk_len m /\ ram_mem ram = mod_stk m.
Hint Unfold match_module_to_ram : mgen.

Lemma transf_not_store' :
  forall m state ram n i c_s d' c' n' tar1 trs1 p ar1 ar2 rs1 rs2 r e1 e2,
    all_match_empty_size m ar1 ->
    all_match_empty_size m tar1 ->
    match_module_to_ram m ram ->
    ram_ordering ram ->
    (mod_datapath m)!i = Some (Vnonblock (Vvari r e1) e2) ->
    (mod_controllogic m)!i = Some c_s ->
    transf_maps state ram i (n, mod_datapath m, mod_controllogic m) = (n', d', c') ->
    exec_all (Vnonblock (Vvari (ram_mem ram) e1) e2) c_s rs1 ar1 rs2 ar2 ->
    match_reg_assocs p rs1 trs1 ->
    match_arr_assocs ar1 tar1 ->
    max_reg_module m < p ->
    exists d_s' c_s' trs2 tar2,
      d'!i = Some d_s' /\ c'!i = Some c_s'
      /\ exec_all_ram ram d_s' c_s' trs1 tar1 trs2 tar2
      /\ match_reg_assocs p (merge_reg_assocs rs2) (merge_reg_assocs trs2)
      /\ match_arr_assocs (merge_arr_assocs (ram_mem ram) (ram_size ram) ar2)
                          (merge_arr_assocs (ram_mem ram) (ram_size ram) tar2).
Proof.
  (*intros; unfold transf_maps; simplify; repeat destruct_match; mgen_crush.
  inv H1. unfold exec_all in *. repeat inv_exists. simplify.
  exploit match_states_same. apply H0. instantiate (1 := p).
  apply max_reg_stmnt_le_stmnt_tree in Heqo0. lia.
  eassumption. eassumption. intros.
  repeat inv_exists. simplify.
  inv H1. inv H12. inv H12.
  inv H. inv H7. simplify.
  do 4 econstructor.
  simplify. rewrite AssocMap.gss. auto. eauto.
  unfold exec_all_ram.
  do 5 econstructor. simplify. eassumption.
  econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. eapply expr_runp_matches2.
  eassumption.
  apply max_reg_stmnt_le_stmnt_tree in Heqo.
  unfold max_reg_stmnt in Heqo. assert (max_reg_expr e2 < p) by lia; eauto.
  unfold nonblock_reg. simplify. auto. auto.
  econstructor. econstructor. unfold nonblock_reg. simplify.
  eapply expr_runp_matches2. eassumption.
  apply max_reg_stmnt_le_stmnt_tree in Heqo. unfold max_reg_stmnt in Heqo. simplify.
  assert (max_reg_expr e1 < p) by lia. eauto.
  auto. auto.
  eapply exec_ram_Some_write.
  3: {
    unfold nonblock_reg. simplify. unfold merge_regs.
    apply AssocMapExt.merge_correct_1. rewrite AssocMap.gso by admit.
    rewrite AssocMap.gso by admit. rewrite AssocMap.gso by admit.
    rewrite AssocMap.gss. auto.
  }
  crush.
  2: {
    unfold nonblock_reg; simplify. apply AssocMapExt.merge_correct_1.
    rewrite AssocMap.gso by admit. rewrite AssocMap.gso by admit.
    rewrite AssocMap.gss. auto.
  }
  crush.
  unfold nonblock_reg; simplify.
  apply AssocMapExt.merge_correct_1.
  rewrite AssocMap.gso by admit. rewrite AssocMap.gss. auto.
  unfold nonblock_reg; simplify.
  apply AssocMapExt.merge_correct_1.
  rewrite AssocMap.gss. auto.
  unfold nonblock_reg; simplify.
  unfold merge_reg_assocs. simplify. econstructor.
  unfold merge_regs. mgen_crush. apply match_assocmaps_merge.
  apply match_assocmaps_gt. admit.
  apply match_assocmaps_gt. admit.
  apply match_assocmaps_gt. admit.
  apply match_assocmaps_gt. admit. auto. auto. auto with mgen.
  constructor. unfold nonblock_arr. simplify.
  assert (exists m, ram_size ram = mod_stk_len m
         /\ ram_mem ram = mod_stk m) by admit.
  inv H7. inv H9. rewrite H7. rewrite H11.
  rewrite <- empty_stack_m.
  apply match_arrs_merge_set2. admit. admit. admit. admit. auto. auto.
  auto with mgen.*)
Admitted.

Lemma transf_code_store' :
  forall l m state ram d' c' n n',
    fold_right (transf_maps state ram) (n, mod_datapath m, mod_controllogic m) l = (n', d', c') ->
    Forall (fun x => n > x) l ->
    list_norepet l ->
    (forall p i c_s rs1 ar1 rs2 ar2 trs1 tar1 r e1 e2,
        n > i ->
        all_match_empty_size m ar1 ->
        all_match_empty_size m tar1 ->
        match_module_to_ram m ram ->
        ram_ordering ram ->
        (mod_datapath m)!i = Some (Vnonblock (Vvari r e1) e2) ->
        (mod_controllogic m)!i = Some c_s ->
        match_reg_assocs p rs1 trs1 ->
        match_arr_assocs ar1 tar1 ->
        max_reg_module m < p ->
        exists d_s' c_s' trs2 tar2,
          d'!i = Some d_s' /\ c'!i = Some c_s'
          /\ exec_all_ram ram d_s' c_s' trs1 tar1 trs2 tar2
          /\ match_reg_assocs p (merge_reg_assocs rs2) (merge_reg_assocs trs2)
          /\ match_arr_assocs (merge_arr_assocs (ram_mem ram) (ram_size ram) ar2)
                              (merge_arr_assocs (ram_mem ram) (ram_size ram) tar2)).
Proof.

Lemma transf_code_store :
  forall state ram d c d' c' i d_s c_s rs1 ar1 rs2 ar2 p trs1 tar1 r e1 e2,
    transf_code state ram d c = (d', c') ->
    d!i = Some (Vnonblock (Vvari r e1) e2) ->
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
    - assert (MATCH_SIZE1: match_empty_size m nasa1 /\ match_empty_size m basa1).
      { eapply match_arrs_size_stmnt_preserved2; eauto. unfold match_empty_size; mgen_crush. }
      simplify.
      assert (MATCH_SIZE2: match_empty_size m nasa2 /\ match_empty_size m basa2).
      { eapply match_arrs_size_stmnt_preserved2; mgen_crush. } simplify.
      assert (MATCH_SIZE2: match_empty_size m nasa3 /\ match_empty_size m basa3).
      { eapply match_arrs_size_ram_preserved2; mgen_crush. unfold match_empty_size. mgen_crush.
      unfold match_empty_size. mgen_crush. apply match_empty_size_merge; mgen_crush. } simplify.
      assert (MATCH_ARR3: match_arrs_size nasa3 basa3) by mgen_crush.
      exploit match_states_same. apply H4. eauto with mgen.
      econstructor; eauto. econstructor; eauto. econstructor; eauto. econstructor; eauto.
      intros. repeat inv_exists. simplify. inv H18. inv H21.
      exploit match_states_same. apply H6. eauto with mgen.
      econstructor; eauto. econstructor; eauto. intros. repeat inv_exists. simplify. inv H18. inv H23.
      exploit exec_ram_same; eauto. eauto with mgen.
      econstructor. eapply match_assocmaps_merge; eauto. eauto with mgen.
      econstructor.
      apply match_arrs_merge; eauto with mgen. eauto with mgen.
      intros. repeat inv_exists. simplify. inv H18. inv H28.
      econstructor; simplify. apply Smallstep.plus_one. econstructor.
      mgen_crush. mgen_crush. mgen_crush. rewrite RAM0; eassumption. rewrite RAM0; eassumption.
      rewrite RAM0. eassumption. mgen_crush. eassumption. rewrite RAM0 in H21. rewrite RAM0.
      rewrite RAM. eassumption. eauto. eauto. eauto with mgen. eauto.
      econstructor. mgen_crush. apply match_arrs_merge; mgen_crush. eauto.
      apply match_empty_size_merge; mgen_crush; mgen_crush.
      assert (MATCH_SIZE1': match_empty_size m ran'0 /\ match_empty_size m rab'0).
      { eapply match_arrs_size_stmnt_preserved2; eauto. unfold match_empty_size; mgen_crush. }
      simplify.
      assert (MATCH_SIZE2': match_empty_size m ran'2 /\ match_empty_size m rab'2).
      { eapply match_arrs_size_stmnt_preserved2; mgen_crush. } simplify.
      assert (MATCH_SIZE2': match_empty_size m ran'4 /\ match_empty_size m rab'4).
      { eapply match_arrs_size_ram_preserved2; mgen_crush.
        unfold match_empty_size, transf_module, empty_stack.
        repeat destruct_match; crush. mgen_crush. unfold match_empty_size. mgen_crush.
      unfold match_empty_size. mgen_crush. apply match_empty_size_merge; mgen_crush. }
      apply match_empty_size_merge; mgen_crush; mgen_crush.
    - exploit transf_code_all; eauto. unfold exec_all.
      do 3 eexists. simplify. apply H4. apply H6. econstructor. apply ASSOC. eauto with mgen.
      econstructor. apply ARRS.
      eauto with mgen.
      eauto with mgen.
      intros. simplify. inv H15. inv H17.
      unfold exec_all_ram in *. repeat inv_exists. simplify. inv H7.
      destruct x4. destruct x5. destruct x6. destruct x7. destruct x1. destruct x2.
      econstructor. econstructor. apply Smallstep.plus_one.
      econstructor; eauto with mgen; simplify.
      assert (assoc_blocking ! (mod_st (transf_module m)) = Some (posToValue st)) by admit; auto.
      unfold empty_stack in *. simplify. unfold transf_module in *.
      simplify. repeat destruct_match; crush.
      unfold merge_arr_assocs, merge_reg_assocs, empty_stack' in *. simplify. eassumption.
      econstructor. mgen_crush. simplify.
      assert (match_empty_size m (merge_arrs nasa2 basa2)) by admit.
      eauto with mgen. auto.
      assert (match_empty_size m (merge_arrs nasa2 basa2)) by admit.
      eauto with mgen.
      admit.
    - do 2 econstructor. apply Smallstep.plus_one.
      apply step_finish; mgen_crush. constructor; eauto.
    - do 2 econstructor. apply Smallstep.plus_one.
      apply step_finish; mgen_crush. econstructor; eauto.
    - econstructor. econstructor. apply Smallstep.plus_one. econstructor.
      replace (mod_entrypoint (transf_module m)) with (mod_entrypoint m) by (rewrite RAM0; auto).
      replace (mod_reset (transf_module m)) with (mod_reset m) by (rewrite RAM0; auto).
      replace (mod_finish (transf_module m)) with (mod_finish m) by (rewrite RAM0; auto).
      replace (empty_stack (transf_module m)) with (empty_stack m) by (rewrite RAM0; auto).
      replace (mod_params (transf_module m)) with (mod_params m) by (rewrite RAM0; auto).
      replace (mod_st (transf_module m)) with (mod_st m) by (rewrite RAM0; auto).
      repeat econstructor; mgen_crush.
    - econstructor. econstructor. apply Smallstep.plus_one. econstructor.
      replace (mod_entrypoint (transf_module m)) with (mod_entrypoint m).
      replace (mod_reset (transf_module m)) with (mod_reset m).
      replace (mod_finish (transf_module m)) with (mod_finish m).
      replace (empty_stack (transf_module m)) with (empty_stack m).
      replace (mod_params (transf_module m)) with (mod_params m).
      replace (mod_st (transf_module m)) with (mod_st m).
      all: try solve [unfold transf_module; repeat destruct_match; mgen_crush].
      repeat econstructor; mgen_crush.
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
      symmetry. rewrite AssocMap.gso; auto. inv H8. apply H1. auto.
      auto. auto. auto. auto.
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
      symmetry. rewrite AssocMap.gso; auto. inv H6. apply H. auto.
      auto. auto. auto. auto.
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
    eapply Smallstep.forward_simulation_plus; mgen_crush.
    apply senv_preserved.
  Qed.

End CORRECTNESS.
