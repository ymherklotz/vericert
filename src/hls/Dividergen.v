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
Require Import compcert.common.Errors.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.HTL.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.

Local Open Scope positive.
Local Open Scope assocmap.

Hint Resolve max_reg_stmnt_le_stmnt_tree : mgen.
Hint Resolve max_reg_stmnt_lt_stmnt_tree : mgen.
Hint Resolve max_stmnt_lt_module : mgen.

Definition transf_maps state div in_ (dc: PTree.t stmnt * PTree.t stmnt) :=
  match dc, in_ with
  | (d, c), (i, n) =>
    match PTree.get i d, PTree.get i c with
    | Some (Vnonblock (Vvar e1) (Vbinop Vdiv a b)), Some (Vnonblock (Vvar st') e3) =>
      if (st' =? state) && (Z.pos n <=? Int.max_unsigned)%Z
         && (e1 <? state) && (max_reg_expr a <? state) && (max_reg_expr e3 <? state)
         && (max_reg_expr b <? state)
      then
        let nd :=
            Vseq (Vnonblock (Vvar (div_u_en div)) (Vunop Vnot (Vvar (div_u_en div))))
                 (Vseq (Vnonblock (Vvar (div_a div)) a)
                       (Vnonblock (Vvar (div_b div)) b))
        in
        let aout := Vnonblock (Vvar e1) (Vvar (div_q div)) in
        let redirect := Vnonblock (Vvar state) (Vlit (posToValue n)) in
        (PTree.set i nd (PTree.set n aout d),
         PTree.set i redirect (PTree.set n (Vnonblock (Vvar st') e3) c))
      else dc
    | _, _ => dc
    end
  end.

Lemma transf_maps_wf :
  forall state ram d c d' c' i,
    map_well_formed c /\ map_well_formed d ->
    transf_maps state ram i (d, c) = (d', c') ->
    map_well_formed c' /\ map_well_formed d'.
Admitted.

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

Definition transf_code state ram d c :=
  fold_right (transf_maps state ram) (d, c)
             (zip_range (Pos.max (max_pc c) (max_pc d) + 1)
                        (map fst (PTree.elements d))).

Lemma transf_code_wf' :
  forall l c d state ram c' d',
    map_well_formed c /\ map_well_formed d ->
    fold_right (transf_maps state ram) (d, c) l = (d', c') ->
    map_well_formed c' /\ map_well_formed d'.
Proof.
  induction l; intros; simpl in *. inv H0; auto.
  remember (fold_right (transf_maps state ram) (d, c) l). destruct p.
  apply transf_maps_wf in H0. auto. eapply IHl; eauto.
Qed.

Lemma transf_code_wf :
  forall c d state ram c' d',
    map_well_formed c /\ map_well_formed d ->
    transf_code state ram d c = (d', c') ->
    map_well_formed c' /\ map_well_formed d'.
Proof. eauto using transf_code_wf'. Qed.

Lemma module_div_wf' :
  forall m addr,
    addr = max_reg_module m + 1 ->
    mod_clk m < addr.
Proof. unfold max_reg_module in *; lia. Qed.

Lemma module_div_wf'' :
  forall m addr r,
    mod_ram m = Some r ->
    addr = max_reg_module m + 1 ->
    ram_u_en r < addr.
Proof.
  intros.
  assert (max_reg_module m + 1 <= addr) by lia. clear H0.
  unfold max_reg_module in *. unfold max_reg_ram in *.
  rewrite H in H1.
  assert (X: forall a b c, Pos.max a b + 1 <= c -> b + 1 <= c).
  { clear H1. lia. }
  repeat apply X in H1.
  lia.
Qed.

Lemma div_wf :
  forall x,
    x + 1 < x + 2 < x + 3 /\ x + 3 < x + 4 < x + 5 /\ x + 5 < x + 6 < x + 7.
Proof. lia. Qed.

Definition transf_module (m: module): res module.
  refine (
  let max_reg := max_reg_module m in
  let a := max_reg+1 in
  let b := max_reg+2 in
  let q := max_reg+3 in
  let r := max_reg+4 in
  let en := max_reg+5 in
  let u_en := max_reg+6 in
  let don := max_reg+7 in
  let div := @mk_div a b q r en u_en don ltac:(eauto using div_wf) in
  let tc := transf_code (mod_st m) div (mod_datapath m) (mod_controllogic m) in
  match mod_div m with
  | None =>
    OK (mkmodule m.(mod_params)
                 (fst tc)
                 (snd tc)
                 (mod_entrypoint m)
                 (mod_st m)
                 (mod_stk m)
                 (mod_stk_len m)
                 (mod_finish m)
                 (mod_return m)
                 (mod_start m)
                 (mod_reset m)
                 (mod_clk m)
                 (AssocMap.set a (None, VScalar 32)
                  (AssocMap.set b (None, VScalar 32)
                   (AssocMap.set q (None, VScalar 32)
                    (AssocMap.set r (None, VScalar 32)
                     (AssocMap.set en (None, VScalar 1)
                      (AssocMap.set u_en (None, VScalar 32)
                       (AssocMap.set don (None, VScalar 32)
                                     m.(mod_scldecls))))))))
                 m.(mod_arrdecls)
                 (mod_ram m)
                 (Some div)
                 _ (mod_ordering_wf m) (mod_ram_wf m) (mod_params_wf m) _ _)
  | _ => Error (msg "Hi.")
  end).
  eapply transf_code_wf. apply (mod_wf m). destruct tc eqn:?; simpl.
  rewrite <- Heqp. intuition.
  inversion 1; subst. auto using module_div_wf'.
  inversion 1. inversion 1; subst. eauto using module_div_wf''.
Defined.

Inductive tr_module : module -> module -> Prop :=
| tr_module_intro :
    forall m max_reg div t c wf1 wf2 wf3 wf,
    max_reg_module m = max_reg ->
    div = @mk_div (max_reg+1) (max_reg+2) (max_reg+3) (max_reg+4) (max_reg+5) (max_reg+6) (max_reg+7) wf ->
    (t, c) = transf_code (mod_st m) div (mod_datapath m) (mod_controllogic m) ->
    tr_module m
              (mkmodule m.(mod_params)
                 t c
                 (mod_entrypoint m)
                 (mod_st m)
                 (mod_stk m)
                 (mod_stk_len m)
                 (mod_finish m)
                 (mod_return m)
                 (mod_start m)
                 (mod_reset m)
                 (mod_clk m)
                 (AssocMap.set (max_reg+1) (None, VScalar 32)
                  (AssocMap.set (max_reg+2) (None, VScalar 32)
                   (AssocMap.set (max_reg+3) (None, VScalar 32)
                    (AssocMap.set (max_reg+4) (None, VScalar 32)
                     (AssocMap.set (max_reg+5) (None, VScalar 1)
                      (AssocMap.set (max_reg+6) (None, VScalar 32)
                       (AssocMap.set (max_reg+7) (None, VScalar 32)
                                     m.(mod_scldecls))))))))
                 m.(mod_arrdecls)
                 (mod_ram m)
                 (Some div)
                 wf1 (mod_ordering_wf m) (mod_ram_wf m) (mod_params_wf m) wf2 wf3).

Lemma tr_module_correct m m': transf_module m = OK m' -> tr_module m m'.
Admitted.

Definition transf_fundef := transf_partial_fundef transf_module.

Definition transf_program (p : program) :=
  transform_partial_program transf_fundef p.

Inductive match_assocmaps : positive -> assocmap -> assocmap -> Prop :=
  match_assocmap: forall p rs rs',
    (forall r, r < p -> rs!r = rs'!r) ->
    match_assocmaps p rs rs'.

Inductive match_arrs : assocmap_arr -> assocmap_arr -> Prop :=
| match_assocmap_arr_intro: forall ar ar',
    (forall s arr arr',
        ar ! s = Some arr ->
        ar' ! s = Some arr' ->
        (forall addr,
            array_get_error addr arr = array_get_error addr arr')) ->
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

Definition disable_div (div: option div) (asr : assocmap_reg) : Prop :=
  match div with
  | Some d => (Int.eq (asr # ((div_en d), 32)) (asr # ((div_u_en d), 32)) = true)
              /\ (asr # (div_done d, 32) = ZToValue 0)
  | None => True
  end.

Inductive match_stackframes : stackframe -> stackframe -> Prop :=
  match_stackframe_intro :
    forall r m pc asr asa asr' asa' m'
      (SUCC: tr_module m m')
      (DISABLE_RAM: disable_div (mod_div m') asr')
      (MATCH_ASSOC: match_assocmaps (max_reg_module m + 1) asr asr')
      (MATCH_ARRS: match_arrs asa asa')
      (MATCH_EMPT1: match_empty_size m asa)
      (MATCH_EMPT2: match_empty_size m asa')
      (MATCH_RES: r < mod_st m),
      match_stackframes (Stackframe r m pc asr asa)
                        (Stackframe r m' pc asr' asa').

Inductive match_states : state -> state -> Prop :=
| match_state :
    forall res res' m st asr asr' asa asa' m'
           (SUCC: tr_module m m')
           (ASSOC: match_assocmaps (max_reg_module m + 1) asr asr')
           (ARRS: match_arrs asa asa')
           (STACKS: list_forall2 match_stackframes res res')
           (ARRS_SIZE: match_empty_size m asa)
           (ARRS_SIZE2: match_empty_size m asa')
           (DISABLE_RAM: disable_div (mod_div m') asr'),
      match_states (State res m st asr asa)
                   (State res' m' st asr' asa')
| match_returnstate :
    forall res res' i
           (STACKS: list_forall2 match_stackframes res res'),
      match_states (Returnstate res i) (Returnstate res' i)
| match_initial_call :
    forall m m'
      (SUCC: tr_module m m'),
      match_states (Callstate nil m nil)
                   (Callstate nil m' nil).
Hint Constructors match_states : mgen.

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

Definition match_prog (p: program) (tp: program) :=
  Linking.match_program (fun cu f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p p', transf_program p = OK p' -> match_prog p p'.
Proof.
  intros. unfold transf_program, match_prog.
  apply Linking.match_transform_partial_program; auto.
Qed.

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
        Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  Hint Resolve function_ptr_translated : mgen.

  Lemma functions_translated:
    forall (v: Values.val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.
  Hint Resolve functions_translated : mgen.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof (Genv.senv_transf_partial TRANSL).
  Hint Resolve senv_preserved : mgen.

  Theorem transf_step_correct:
    forall (S1 : state) t S2,
      step ge S1 t S2 ->
      forall R1,
        match_states S1 R1 ->
        exists R2, Smallstep.plus step tge R1 t R2 /\ match_states S2 R2.
  Proof. Admitted.
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
    inv H4. unfold bind in *. destruct transf_module eqn:?. inv H5. 2: discriminate.
    econstructor. econstructor. econstructor.
    eapply (Genv.init_mem_match TRANSL); eauto.
    setoid_rewrite (Linking.match_program_main TRANSL).
    rewrite symbols_preserved. eauto.
    subst tge. eauto.
    econstructor. apply tr_module_correct. auto.
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
