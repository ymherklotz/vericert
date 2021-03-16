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
  | Vblock e1 e2 => Pos.max (max_reg_expr e2) (max_reg_expr e2)
  | Vnonblock e1 e2 => Pos.max (max_reg_expr e2) (max_reg_expr e2)
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
                   (max_pc c + 1, d, c)
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
  match transf_code (mod_st m) ram (mod_datapath m) (mod_controllogic m) with
  | (nd, nc) =>
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
  end.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : program) :=
  transform_program transf_fundef p.

Inductive match_assocmaps : assocmap -> assocmap -> Prop :=
  match_assocmap: forall rs rs',
    (forall r v, rs!r = Some v -> rs'!r = Some v) ->
    match_assocmaps rs rs'.

Inductive match_arrs : assocmap_arr -> assocmap_arr -> Prop :=
  match_assocmap_arr: forall ar ar',
    (forall s arr arr',
        ar!s = Some arr ->
        ar'!s = Some arr' ->
        forall addr,
          array_get_error addr arr = array_get_error addr arr') ->
    match_arrs ar ar'.

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr' asa',
      match_assocmaps asr asr' ->
      match_arrs asa asa' ->
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r (transf_module m) pc asr' asa').

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa'
           (ASSOC: match_assocmaps asr asr')
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

Inductive match_reg_assocs : reg_associations -> reg_associations -> Prop :=
  match_reg_association:
    forall rab rab' ran ran',
      match_assocmaps rab rab' ->
      match_assocmaps ran ran' ->
      match_reg_assocs (mkassociations rab ran) (mkassociations rab' ran').

Inductive match_arr_assocs : arr_associations -> arr_associations -> Prop :=
  match_arr_association:
    forall rab rab' ran ran',
      match_arrs rab rab' ->
      match_arrs ran ran' ->
      match_arr_assocs (mkassociations rab ran) (mkassociations rab' ran').

Ltac mgen_crush := crush; eauto with mgen.

Lemma match_assocmaps_equiv : forall a, match_assocmaps a a.
Proof. constructor; auto. Qed.
Hint Resolve match_assocmaps_equiv : mgen.

Lemma match_arrs_equiv : forall a, match_arrs a a.
Proof. constructor; mgen_crush. Qed.
Hint Resolve match_arrs_equiv : mgen.

Lemma match_reg_assocs_equiv : forall a, match_reg_assocs a a.
Proof. destruct a; constructor; mgen_crush. Qed.
Hint Resolve match_reg_assocs_equiv : mgen.

Lemma match_arr_assocs_equiv : forall a, match_arr_assocs a a.
Proof. destruct a; constructor; mgen_crush. Qed.
Hint Resolve match_arr_assocs_equiv : mgen.

Definition forall_ram (P: reg -> Prop) ram :=
  P (ram_mem ram)
  /\ P (ram_en ram)
  /\ P (ram_addr ram)
  /\ P (ram_wr_en ram)
  /\ P (ram_d_in ram)
  /\ P (ram_d_out ram).

Definition exec_all d_s c_s rs1 ar1 rs3 ar3 :=
  exists f rs2 ar2,
    stmnt_runp f rs1 ar1 d_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 c_s rs3 ar3.

Definition exec_all_ram r d_s c_s rs1 ar1 rs4 ar4 :=
  exists f rs2 ar2 rs3 ar3,
    stmnt_runp f rs1 ar1 d_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 c_s rs3 ar3
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

Definition behaviour_correct d c d' c' r :=
  forall rs1 ar1 rs2 ar2 d_s c_s i v v',
    PTree.get i d = Some d_s ->
    PTree.get i c = Some c_s ->
    ram_present ar1 r v v' ->
    ram_present ar2 r v v' ->
    exec_all d_s c_s rs1 ar1 rs2 ar2 ->
    exists d_s' c_s' trs2 tar2,
      PTree.get i d' = Some d_s'
      /\ PTree.get i c' = Some c_s'
      /\ exec_all_ram r d_s' c_s' rs1 ar1 trs2 tar2
      /\ match_reg_assocs (merge_reg_assocs rs2) (merge_reg_assocs trs2)
      /\ match_arr_assocs (merge_arr_assocs (ram_mem r) (ram_size r) ar2)
                          (merge_arr_assocs (ram_mem r) (ram_size r) tar2).

Lemma behaviour_correct_equiv :
  forall d c r,
    forall_ram (fun x => max_stmnt_tree d < x /\ max_stmnt_tree c < x) r ->
    behaviour_correct d c d c r.
Proof.
  intros; unfold behaviour_correct.
  intros. exists d_s. exists c_s.
  unfold exec_all in *. inv H3. inv H4. inv H3. inv H4.
  econstructor. econstructor.
  simplify; auto.
  unfold exec_all_ram.
  exists x. exists x0. exists x1. econstructor. econstructor.
  simplify; eauto.
  econstructor.
  unfold find_assocmap. unfold AssocMapExt.get_default.
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
  inv H11; auto.
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
        /\ match_reg_assocs rs2 rs2'
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

Lemma transf_store :
  forall state ram n d c i c_s r e1 e2 rs1 ar1 rs2 ar2,
    d!i = Some (Vnonblock (Vvari r e1) e2) ->
    c!i = Some c_s ->
    exec_all (Vnonblock (Vvari r e1) e2) c_s rs1 ar1 rs2 ar2 ->
    exists n' d' c' d_s' c_s' trs2 tar2,
      transf_maps state ram i (n, d, c) = (n', d', c')
      /\ d'!i = Some d_s'
      /\ c'!i = Some c_s'
      /\ exec_all_ram ram d_s' c_s' rs1 ar1 trs2 tar2
      /\ match_reg_assocs (merge_reg_assocs rs2) (merge_reg_assocs trs2)
      /\ match_arr_assocs (merge_arr_assocs (ram_mem ram) (ram_size ram) ar2)
                          (merge_arr_assocs (ram_mem ram) (ram_size ram) tar2).
Proof.
Admitted.

Lemma transf_load :
  forall state n d c i c_s r e1 e2 ar1 rs1 ar2 rs2 ram,
    (forall e2 r, e1 <> Vvari r e2) ->
    d!i = Some (Vnonblock e1 (Vvari r e2)) ->
    c!i = Some c_s ->
    d!n = None ->
    c!n = None ->
    exists n' d' c' d_s' c_s' trs2 tar2,
      transf_maps state ram i (n, d, c) = (n', d', c')
      /\ d'!i = Some d_s'
      /\ c'!i = Some c_s'
      /\ exec_all_ram ram d_s' c_s' rs1 ar1 trs2 tar2
      /\ match_reg_assocs (merge_reg_assocs rs2) (merge_reg_assocs trs2)
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
  forall rs1 rs2 rs3,
    match_assocmaps rs1 rs2 ->
    match_assocmaps rs2 rs3 ->
    match_assocmaps rs1 rs3.
Proof.
  intros. inv H. inv H0. econstructor; eauto.
Qed.

Lemma match_reg_assocs_trans:
  forall rs1 rs2 rs3,
    match_reg_assocs rs1 rs2 ->
    match_reg_assocs rs2 rs3 ->
    match_reg_assocs rs1 rs3.
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

(*Lemma transf_maps_preserves_behaviour :
  forall ge m m' s addr d_in d_out wr_en n n' t stk rs ar d' c' wf' i,
    m' = mkmodule (mod_params m)
                  d'
                  c'
                  (mod_entrypoint m)
                  (mod_st m)
                  (mod_stk m)
                  (2 ^ Nat.log2_up m.(mod_stk_len))%nat
                  (mod_finish m)
                  (mod_return m)
                  (mod_start m)
                  (mod_reset m)
                  (mod_clk m)
                  (AssocMap.set wr_en (None, VScalar 32)
                                (AssocMap.set d_out (None, VScalar 32)
                                              (AssocMap.set d_in (None, VScalar 32)
                                                            (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))
                  (AssocMap.set (mod_stk m) (None, VArray 32 (2 ^ Nat.log2_up m.(mod_stk_len)))%nat m.(mod_arrdecls))
                  (Some (mk_ram (mod_stk_len m) (mod_stk m) addr wr_en d_in d_out))
                  wf' ->
    transf_maps m.(mod_st) addr d_in d_out wr_en i (n, mod_datapath m, mod_controllogic m) = (n', d', c') ->
    step ge (State stk m s rs ar) t (State stk m s rs ar) ->
    forall R1,
      match_states (State stk m s rs ar) R1 ->
      exists R2, step ge R1 t R2 /\ match_states (State stk m s rs ar) R2.
Proof. Abort.*)

(*Lemma fold_transf_maps_preserves_behaviour :
  forall ge m m' s addr d_in d_out wr_en n' t stk rs ar d' c' wf' l rs' ar' trs tar,
    fold_right (transf_maps m.(mod_st) addr d_in d_out wr_en)
               (max_pc_function m + 1, m.(mod_datapath), m.(mod_controllogic)) l = (n', d', c') ->
    m' = mkmodule (mod_params m)
                  d'
                  c'
                  (mod_entrypoint m)
                  (mod_st m)
                  (mod_stk m)
                  (2 ^ Nat.log2_up m.(mod_stk_len))%nat
                  (mod_finish m)
                  (mod_return m)
                  (mod_start m)
                  (mod_reset m)
                  (mod_clk m)
                  (AssocMap.set wr_en (None, VScalar 32)
                                (AssocMap.set d_out (None, VScalar 32)
                                              (AssocMap.set d_in (None, VScalar 32)
                                                            (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))
                  (AssocMap.set (mod_stk m) (None, VArray 32 (2 ^ Nat.log2_up m.(mod_stk_len)))%nat m.(mod_arrdecls))
                  (Some (mk_ram (mod_stk m) addr wr_en d_in d_out))
                  wf' ->
    match_arrs ar tar ->
    match_assocmaps rs trs ->
    step ge (State stk m s rs ar) t (State stk m s rs' ar') ->
    exists trs' tar', step ge (State stk m' s trs tar) t (State stk m' s trs' tar')
                      /\ match_arrs ar' tar'
                      /\ match_assocmaps rs' trs'.
Proof.
Admitted.*)

(*Lemma fold_transf_maps_preserves_behaviour2 :
  forall ge m m' s t stk rs ar rs' ar' trs tar s',
    transf_module m = m' ->
    match_arrs ar tar ->
    match_assocmaps rs trs ->
    step ge (State stk m s rs ar) t (State stk m s' rs' ar') ->
    exists trs' tar', step ge (State stk m' s trs tar) t (State stk m' s' trs' tar')
                      /\ match_arrs ar' tar'
                      /\ match_assocmaps rs' trs'.
Proof.
  intros.
  unfold transf_module in *. destruct_match. destruct_match. apply transf_maps_correct2 in Heqp. inv H2.
  unfold behaviour_correct in *. eexists. eexists. econstructor. econstructor; simplify; eauto.*)

(*Lemma add_stack_len_no_effect :
  forall ge m m' stk s rs ar t wr_en d_out d_in addr,
    m' = mkmodule (mod_params m)
                  (mod_datapath m)
                  (mod_controllogic m)
                  (mod_entrypoint m)
                  (mod_st m)
                  (mod_stk m)
                  (2 ^ Nat.log2_up m.(mod_stk_len))%nat
                  (mod_finish m)
                  (mod_return m)
                  (mod_start m)
                  (mod_reset m)
                  (mod_clk m)
                  (AssocMap.set wr_en (None, VScalar 32)
                                (AssocMap.set d_out (None, VScalar 32)
                                              (AssocMap.set d_in (None, VScalar 32)
                                                            (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))
                  (AssocMap.set m.(mod_stk) (None, VArray 32 (2 ^ Nat.log2_up m.(mod_stk_len)))%nat m.(mod_arrdecls))
                  (mod_ram m)
                  (mod_wf m) ->
    step ge (State stk m s rs ar) t (State stk m s rs ar) ->
    step ge (State stk m' s rs ar) t (State stk m' s rs ar).
Admitted.*)

Section CORRECTNESS.

  Context (prog tprog: program).
  Context (TRANSL: match_prog prog tprog).

  Let ge : HTL.genv := Genv.globalenv prog.
  Let tge : HTL.genv := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.
  Hint Resolve symbols_preserved : rtlgp.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transf_fundef f = tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof (Genv.senv_transf TRANSL).
  Hint Resolve senv_preserved : rtlgp.

  Theorem transf_step_correct:
    forall (S1 : state) t S2,
      step ge S1 t S2 ->
      forall R1,
        match_states S1 R1 ->
        exists R2, Smallstep.plus step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1.
    - intros. inv H12. inv ASSOC. inv ARRS.
      repeat destruct_match; try solve [crush].
      simplify.
      admit.
    - intros. inv H1. inv ASSOC. inv ARRS.
      econstructor. econstructor. apply Smallstep.plus_one.
      apply step_finish; unfold transf_module; destruct_match; crush; eauto.
      constructor. auto.
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
      rewrite AssocMap.gss in H. auto.
      rewrite AssocMap.gso; auto. rewrite AssocMap.gso in H; auto.
      destruct (Pos.eq_dec r (mod_st m)); subst.
      rewrite AssocMap.gss.
      rewrite AssocMap.gss in H. auto.
      rewrite AssocMap.gso; auto. rewrite AssocMap.gso in H; auto.
  Admitted.

End CORRECTNESS.
