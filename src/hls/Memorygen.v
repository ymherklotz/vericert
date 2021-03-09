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

Definition transf_maps ram i (dc: node * PTree.t stmnt * PTree.t stmnt) :=
  match dc with
  | (n, d, c) =>
    match PTree.get i d, PTree.get i c with
    | Some d_s, Some c_s =>
      match d_s with
      | Vnonblock (Vvari r e1) e2 =>
        let nd := Vseq (Vnonblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 1)))
                       (Vseq (Vnonblock (Vvar (ram_d_in ram)) e2)
                             (Vnonblock (Vvar (ram_addr ram)) e1))
        in
        (n, PTree.set i nd d, c)
      | Vnonblock e1 (Vvari r e2) =>
        let nd := Vseq (Vnonblock (Vvar (ram_wr_en ram)) (Vlit (ZToValue 0)))
                       (Vnonblock (Vvar (ram_addr ram)) e2)
        in
        let aout := Vnonblock e1 (Vvar (ram_d_out ram)) in
        let redirect := Vnonblock (Vvar (ram_mem ram)) (Vlit (posToValue n)) in
        (n+1, PTree.set i nd (PTree.set n aout d),
         PTree.set i redirect (PTree.set n c_s c))
      | _ => dc
      end
    | _, _ => dc
    end
  end.

Lemma transf_maps_wf :
  forall ram n d c n' d' c' i,
  map_well_formed c /\ map_well_formed d ->
  transf_maps ram i (n, d, c) = (n', d', c') ->
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

Definition transf_code ram d c :=
  match fold_right (transf_maps ram)
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
  let ram := mk_ram (mod_stk m) en addr d_in d_out wr_en in
  match transf_code ram (mod_datapath m) (mod_controllogic m) with
  | (nd, nc) =>
    mkmodule m.(mod_params)
             nd
             nc
             m.(mod_entrypoint)
             m.(mod_st)
             m.(mod_stk)
             (2 ^ Nat.log2_up m.(mod_stk_len))%nat
             m.(mod_finish)
             m.(mod_return)
             m.(mod_start)
             m.(mod_reset)
             m.(mod_clk)
             (AssocMap.set wr_en (None, VScalar 32)
              (AssocMap.set d_out (None, VScalar 32)
               (AssocMap.set d_in (None, VScalar 32)
                (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))
             (AssocMap.set m.(mod_stk) (None, VArray 32 (2 ^ Nat.log2_up m.(mod_stk_len)))%nat m.(mod_arrdecls))
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

Inductive match_states : HTL.state -> HTL.state -> Prop :=
| match_state :
    forall res m st asr asr' asa asa'
           (ASSOC: match_assocmaps asr asr')
           (ARRS: match_arrs asa asa'),
      match_states (HTL.State res m st asr asa)
                   (HTL.State res (transf_module m) st asr' asa')
| match_returnstate :
    forall res v,
      match_states (HTL.Returnstate res v) (HTL.Returnstate res v)
| match_initial_call :
    forall m,
      match_states (HTL.Callstate nil m nil)
      (HTL.Callstate nil (transf_module m) nil).
Hint Constructors match_states : htlproof.

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

Definition exec_all d_s c_s r rs1 ar1 rs4 ar4 :=
  exists f rs2 ar2 rs3 ar3,
    stmnt_runp f rs1 ar1 d_s rs2 ar2
    /\ stmnt_runp f rs2 ar2 c_s rs3 ar3
    /\ exec_ram
         (Verilog.mkassociations (Verilog.merge_regs nasr2 basr2) empty_assocmap)
         (Verilog.mkassociations (Verilog.merge_arrs nasa2 basa2) (empty_stack m))
         r rs4 ar4.

Definition behaviour_correct d c r d' c' r' :=
  forall rs1 ar1 rs4 ar4 d_s c_s i,
    PTree.get i d = Some d_s ->
    PTree.get i c = Some c_s ->
    exec_all d_s c_s r rs1 ar1 rs4 ar4 ->
    exists d_s' c_s' trs4 tar4,
      PTree.get i d' = Some d_s'
      /\ PTree.get i c' = Some c_s'
      /\ exec_all d_s' c_s' r' rs1 ar1 trs4 tar4
      /\ match_reg_assocs rs4 trs4
      /\ match_arr_assocs ar4 tar4.

Lemma behaviour_correct_equiv :
  forall d c r, behaviour_correct d c r d c r.
Proof. intros; unfold behaviour_correct; repeat (eexists; mgen_crush). Qed.
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
  Admitted.
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
  forall ram n d c i d_s c_s,
    (forall e1 e2 r, d_s <> Vnonblock (Vvari r e1) e2) ->
    (forall e1 e2 r, d_s <> Vnonblock e1 (Vvari r e2)) ->
    d!i = Some d_s ->
    c!i = Some c_s ->
    transf_maps ram i (n, d, c) = (n, d, c).
Proof. intros; unfold transf_maps; repeat destruct_match; mgen_crush. Qed.

Lemma transf_store :
  forall ram n d c i c_s r e1 e2,
    d!i = Some (Vnonblock (Vvari r e1) e2) ->
    c!i = Some c_s ->
    exists n' d' c' d_s' c_s',
      transf_maps ram i (n, d, c) = (n', d', c')
      /\ d'!i = d_s'
      /\ c'!i = c_s'
      /\ exec_all d_s' c_s'.
Proof.
  unfold transf_maps; intros; do 3 econstructor; repeat destruct_match; mgen_crush.
  unfold behaviour_correct. simplify.
  destruct (Pos.eq_dec i i0). subst.
    unfold exec_all in *.
  inv H1. inv H2. inv H1. inv H2. inv H1. inv H2. inv H3. inv H4.
  rewrite Heqo in H.
  rewrite Heqo0 in H0. inv H. inv H0.
  inv H1.
  simplify.
  do 4 econstructor.
  econstructor.
  apply PTree.gss.
  econstructor.
  eauto.
  split.
  do 5 econstructor.
  split. repeat econstructor.
  simplify. eauto. simplify.
  inv H6.
  split.
Qed.

Lemma transf_load :
  forall stk addr d_in d_out wr_en n d c d' c' i c_s r e1 e2 aout nd redirect,
    (forall e2 r, e1 <> Vvari r e2) ->
    d!i = Some (Vnonblock e1 (Vvari r e2)) ->
    c!i = Some c_s ->
    d!n = None ->
    c!n = None ->
    nd = Vseq (Vnonblock (Vvar wr_en) (Vlit (ZToValue 0)))
              (Vnonblock (Vvar addr) e2) ->
    aout = Vnonblock e1 (Vvar d_out) ->
    redirect = Vnonblock (Vvar stk) (Vlit (posToValue n)) ->
    d' = PTree.set i nd (PTree.set n aout d) ->
    c' = PTree.set i redirect (PTree.set n c_s c) ->
    (transf_maps stk addr d_in d_out wr_en i (n, d, c) = (n+1, d', c')
     ).
Proof. unfold transf_maps; intros; repeat destruct_match; crush. Qed.

Lemma transf_all :
  forall stk addr d_in d_out wr_en d c d' c',
    transf_code stk addr d_in d_out wr_en d c = (d', c') ->
    behaviour_correct d c d' c' (Some (mk_ram stk addr wr_en d_in d_out)).
Proof.

Lemma transf_code_correct:
  forall stk addr d_in d_out wr_en d c d' c',
    transf_code stk addr d_in d_out wr_en d c = (d', c') ->
    (forall i d_s c_s,
        d!i = Some d_s ->
        c!i = Some c_s ->
        tr_code stk addr d_in d_out wr_en d c d' c' i).
Proof.
  simplify.
  unfold transf_code in H.
  destruct_match. destruct_match. inv H.
  econstructor; eauto.

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
    exec_all Vskip Vskip None rs ar rs ar.
Proof.
  unfold exec_all.
  intros. repeat econstructor.
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
  forall st addr d_in d_out wr_en n d c n' d' c' i,
    transf_maps st addr d_in d_out wr_en i (n, d, c) = (n', d', c') ->
    behaviour_correct d c d' c' (Some (mk_ram st addr wr_en d_in d_out)).
Proof.
  Admitted.




Lemma transf_maps_correct2:
  forall l st addr d_in d_out wr_en n d c n' d' c',
    fold_right (transf_maps st addr d_in d_out wr_en) (n, d, c) l = (n', d', c') ->
    behaviour_correct d c d' c' (Some (mk_ram st addr wr_en d_in d_out)).
Proof.
  induction l.
  - intros. simpl in *. inv H. mgen_crush.
  - intros. simpl in *.
    destruct (fold_right (transf_maps st addr d_in d_out wr_en) (n, d, c) l) eqn:?.
    destruct p.
    eapply behaviour_correct_trans.
    eapply transf_maps_correct.
    apply H. eapply IHl. apply Heqp.
Qed.

Lemma transf_maps_preserves_behaviour :
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
                  (Some (mk_ram (mod_stk m) addr wr_en d_in d_out))
                  wf' ->
    transf_maps m.(mod_st) addr d_in d_out wr_en i (n, mod_datapath m, mod_controllogic m) = (n', d', c') ->
    step ge (State stk m s rs ar) t (State stk m s rs ar) ->
      forall R1,
        match_states (State stk m s rs ar) R1 ->
        exists R2, step ge R1 t R2 /\ match_states (State stk m s rs ar) R2.
Proof.
Admitted.

Lemma fold_transf_maps_preserves_behaviour :
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
Admitted.

Lemma fold_transf_maps_preserves_behaviour2 :
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
  unfold behaviour_correct in *. eexists. eexists. econstructor. econstructor; simplify; eauto.

Lemma add_stack_len_no_effect :
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
  Admitted.

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
      exploit fold_transf_maps_preserves_behaviour2.
      eauto. eauto. econstructor. eauto. econstructor. eauto. econstructor; eauto.
      intros.
      inv H12. inv H13.
      simplify.
      econstructor.
      econstructor.
      eapply Smallstep.plus_one.
      eapply H13.
      econstructor; eauto.
    - intros. inv H1. inv ASSOC. inv ARRS.
      repeat econstructor; eauto.

End CORRECTNESS.
