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

Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require compcert.backend.Registers.
Require Import compcert.common.Linking.
Require Import compcert.common.Memory.
Require compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import vericert.common.IntegerExtra.
Require Import vericert.common.Vericertlib.
Require Import vericert.common.ZExtra.
Require Import vericert.hls.Array.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.DHTL.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSubPar.
Require Import vericert.hls.DHTLgen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require vericert.hls.Verilog.
Require Import vericert.common.Errormonad.
Require Import vericert.hls.DHTLgenproof0.
Import ErrorMonad.
Import ErrorMonadExtra.

Require Import Lia.

Local Open Scope assocmap.

Local Opaque Int.max_unsigned.

#[local] Hint Resolve AssocMap.gss : htlproof.
#[local] Hint Resolve AssocMap.gso : htlproof.

#[local] Hint Unfold find_assocmap AssocMapExt.get_default : htlproof.

Section CORRECTNESS.

  Variable prog : GibleSubPar.program.
  Variable tprog : DHTL.program.

  Hypothesis TRANSL : match_prog prog tprog.

  Let ge : GibleSubPar.genv := Globalenvs.Genv.globalenv prog.
  Let tge : DHTL.genv := Globalenvs.Genv.globalenv tprog.

  (* Lemma storev_stack_bounds : *)
  (*   forall m sp v dst m' hi, *)
  (*     Mem.storev Mint32 m (Values.Vptr sp (Ptrofs.repr v)) dst = Some m' -> *)
  (*     stack_bounds (Values.Vptr sp (Ptrofs.repr 0)) hi m -> *)
  (*     v mod 4 = 0 -> *)
  (*     0 <= v < hi. *)
  (* Proof. *)
  (*   intros. unfold stack_bounds in *. *)
  (*   assert (0 <= v < hi \/ hi <= ) *)

  Ltac tac :=
    repeat match goal with
           | [ _ : error _ _ = OK _ _ _ |- _ ] => discriminate
           | [ _ : context[if (?x && ?y) then _ else _] |- _ ] =>
             let EQ1 := fresh "EQ" in
             let EQ2 := fresh "EQ" in
             destruct x eqn:EQ1; destruct y eqn:EQ2; simpl in *
           | [ _ : context[if ?x then _ else _] |- _ ] =>
             let EQ := fresh "EQ" in
             destruct x eqn:EQ; simpl in *
           | [ H : ret _ _ = _  |- _ ] => inv H
           | [ _ : context[match ?x with | _ => _ end] |- _ ] => destruct x
           end.

  Ltac inv_arr_access :=
    match goal with
    | [ _ : translate_arr_access ?chunk ?addr ?args _ _ = OK ?c _ _ |- _] =>
      destruct c, chunk, addr, args; crush; tac; crush
    end.

  Lemma offset_expr_ok :
    forall v z, (Z.to_nat
                   (Integers.Ptrofs.unsigned
                      (Integers.Ptrofs.divu
                         (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ v))
                                              (Integers.Ptrofs.of_int (Integers.Int.repr z)))
                         (Integers.Ptrofs.repr 4)))
                 = valueToNat (Int.divu (Int.add v (ZToValue z)) (ZToValue 4))).
  Proof.
    simplify_val. unfold valueToNat. unfold Int.divu, Ptrofs.divu.
    pose proof Integers.Ptrofs.agree32_add as AGR.
    unfold Integers.Ptrofs.agree32 in AGR.
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (Int.unsigned v))
                                        (Ptrofs.repr (Int.unsigned (Int.repr z)))) =
            Int.unsigned (Int.add v (ZToValue z))).
    apply AGR; auto.
    apply Ptrofs.unsigned_repr. apply Int.unsigned_range_2.
    apply Ptrofs.unsigned_repr. apply Int.unsigned_range_2.
    rewrite H. replace (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
    replace (Int.unsigned (ZToValue 4)) with 4.
    pose proof Ptrofs.agree32_repr. unfold Ptrofs.agree32 in *.
    rewrite H0. trivial. auto.
    unfold ZToValue. symmetry. apply Int.unsigned_repr.
    unfold_constants. lia.
    unfold ZToValue. symmetry. apply Int.unsigned_repr.
    unfold_constants. lia.
  Qed.

  Lemma offset_expr_ok_2 :
    forall v0 v1 z0 z1,
      (Z.to_nat
         (Integers.Ptrofs.unsigned
            (Integers.Ptrofs.divu
               (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ v0))
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add
                                          (Integers.Int.mul (valueToInt v1) (Integers.Int.repr z1))
                                          (Integers.Int.repr z0)))) (Ptrofs.repr 4))))
      = valueToNat (Int.divu (Int.add (Int.add v0 (ZToValue z0))
                                      (Int.mul v1 (ZToValue z1))) (ZToValue 4)).
    intros. unfold ZToValue, valueToNat, valueToInt, Ptrofs.divu, Int.divu, Ptrofs.of_int.

    assert (H : (Ptrofs.unsigned
             (Ptrofs.add (Ptrofs.repr (uvalueToZ v0))
                (Ptrofs.of_int (Int.add (Int.mul (valueToInt v1) (Int.repr z1)) (Int.repr z0)))) /
           Ptrofs.unsigned (Ptrofs.repr 4))
                = (Int.unsigned (Int.add (Int.add v0 (Int.repr z0)) (Int.mul v1 (Int.repr z1))) /
           Int.unsigned (Int.repr 4))).
    { unfold ZToValue, valueToNat, valueToInt, Ptrofs.divu, Int.divu, Ptrofs.of_int.
      rewrite Ptrofs.unsigned_repr by (unfold_constants; lia).
      rewrite Int.unsigned_repr by (unfold_constants; lia).

      unfold Ptrofs.of_int. rewrite Int.add_commut.
      pose proof Integers.Ptrofs.agree32_add as AGR. unfold Ptrofs.agree32 in *.
      erewrite AGR.
      3: { unfold uvalueToZ. rewrite Ptrofs.unsigned_repr. trivial. apply Int.unsigned_range_2. }
      3: { rewrite Ptrofs.unsigned_repr. trivial. apply Int.unsigned_range_2. }
      rewrite Int.add_assoc. trivial. auto.
    }

    rewrite <- H. auto.

  Qed.

  Lemma offset_expr_ok_3 :
    forall OFFSET,
      Z.to_nat (Ptrofs.unsigned (Ptrofs.divu OFFSET (Ptrofs.repr 4)))
      = valueToNat (ZToValue (Ptrofs.unsigned OFFSET / 4)).
  Proof. auto. Qed.

  Lemma storev_mod_ok' :
    forall m sp' ptr src m',
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.storev Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) src = Some m' ->
      ptr mod 4 = 0.
  Proof.
    unfold Mem.storev; intros * BOUND **. repeat destruct_match; try discriminate.
    eapply Mem.store_valid_access_3 in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    inv Heqv. rewrite Ptrofs.add_unsigned in H1.
    rewrite ! Ptrofs.unsigned_repr in H1; try lia. auto.
    rewrite ! Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma loadv_mod_ok' :
    forall m sp' ptr v,
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.loadv Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) = Some v ->
      ptr mod 4 = 0.
  Proof.
    unfold Mem.loadv; intros * BOUND **. repeat destruct_match; try discriminate.
    eapply Mem.load_valid_access in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    inv Heqv0. rewrite Ptrofs.add_unsigned in H1.
    rewrite ! Ptrofs.unsigned_repr in H1; try lia. auto.
    rewrite ! Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma offset_ptr_equiv :
    forall sp' v,
      Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) v = Values.Vptr sp' v.
  Proof.
    unfold Values.Val.offset_ptr; intros.
    replace (Ptrofs.repr 0) with Ptrofs.zero by auto.
    now rewrite Ptrofs.add_zero_l.
  Qed.

  Lemma loadv_mod_ok :
    forall m sp' ptr v,
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.loadv Mint32 m (Values.Vptr sp' (Ptrofs.repr ptr)) = Some v ->
      ptr mod 4 = 0.
  Proof.
    intros. eapply loadv_mod_ok'; eauto.
    rewrite offset_ptr_equiv; eauto.
  Qed.

  Lemma storev_mod_ok :
    forall m sp' ptr src m',
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.storev Mint32 m (Values.Vptr sp' (Ptrofs.repr ptr)) src = Some m' ->
      ptr mod 4 = 0.
  Proof.
    intros. eapply storev_mod_ok'; eauto.
    rewrite offset_ptr_equiv; eauto.
  Qed.

  Lemma loadv_mod_ok2 :
    forall m sp' v v',
      Mem.loadv Mint32 m (Values.Vptr sp' v) = Some v' ->
      (Ptrofs.unsigned v) mod 4 = 0.
  Proof.
    unfold Mem.loadv; intros. repeat destruct_match; try discriminate.
    eapply Mem.load_valid_access in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    auto.
  Qed.

  Lemma storev_mod_ok2 :
    forall m sp' src m' v,
      Mem.storev Mint32 m (Values.Vptr sp' v) src = Some m' ->
      (Ptrofs.unsigned v) mod 4 = 0.
  Proof.
    unfold Mem.storev; intros. repeat destruct_match; try discriminate.
    eapply Mem.store_valid_access_3 in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    auto.
  Qed.

  Lemma storev_exists_ptr:
    forall m v src m',
      Mem.storev Mint32 m v src = Some m' ->
      exists sp v', v = Values.Vptr sp v'.
  Proof.
    intros.
    unfold Mem.storev in *. destruct_match; try discriminate.
    subst. eauto.
  Qed.

  Lemma loadv_exists_ptr:
    forall m v m',
      Mem.loadv Mint32 m v = Some m' ->
      exists sp v', v = Values.Vptr sp v'.
  Proof using.
    intros.
    unfold Mem.loadv in *. destruct_match; try discriminate.
    subst. eauto.
  Qed.

  Lemma val_add_stack_based :
    forall v1 v2 sp,
      stack_based v1 sp ->
      stack_based v2 sp ->
      stack_based (Values.Val.add v1 v2) sp.
  Proof.
    intros. destruct v1, v2; auto.
    inv H. inv H0. cbn; auto.
  Qed.

  Lemma val_mul_stack_based :
    forall v1 v2 sp,
      stack_based v1 sp ->
      stack_based v2 sp ->
      stack_based (Values.Val.mul v1 v2) sp.
  Proof.
    intros. destruct v1, v2; auto.
    inv H. inv H0. cbn; auto.
  Qed.

  Lemma ptrofs_unsigned_add_0:
    forall x0,
      Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr (Ptrofs.unsigned x0))) = Ptrofs.unsigned x0.
  Proof.
    intros. replace (Ptrofs.repr 0) with (Ptrofs.zero) by auto.
    rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr; auto.
    apply Ptrofs.unsigned_range_2.
  Qed.

  Lemma exists_ptr_add_int :
    forall a b sp' x0,
      Values.Val.add a (Values.Vint b) = Values.Vptr sp' x0 ->
      exists a', a = Values.Vptr sp' a'.
  Proof.
    intros. destruct a; eauto; cbn in *; try discriminate.
    assert (Xx: Archi.ptr64 = false) by auto. rewrite Xx in H. inv H. eauto.
  Qed.

  Lemma transl_arr_access_correct :
    forall addr args e rs ps m sp a chnk src m' s f pc s' m_ asr arr,
      translate_arr_access chnk addr args m_.(DHTL.mod_stk) = OK e ->
      Op.eval_addressing ge sp addr (List.map (fun r => Registers.Regmap.get r rs) args) = Some a ->
      Mem.storev chnk m a (Registers.Regmap.get src rs) = Some m' ->
      match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr arr) ->
      exists x, expr_runp tt asr arr e x.
  Proof.
    assert (HARCH: Archi.ptr64 = false) by auto.
    intros. unfold translate_arr_access in *. repeat destr.
    destruct_match; try discriminate; repeat destr.
    - inv H. cbn in *. unfold Op.eval_addressing in *. rewrite HARCH in H0.
      cbn in *. inv H0. inv H2. unfold stack_bounds in *.
      exploit storev_exists_ptr; eauto. simplify.
      assert (stack_based (Values.Vint (Int.repr z)) sp') by (cbn; auto).
      assert (stack_based (rs !! r) sp') by (cbn; auto).
      eapply val_add_stack_based in H0; eauto. rewrite H in H0. cbn in *. inv H0.
      rewrite H in H1. exploit storev_mod_ok2; eauto; intros.
      specialize (BOUNDS (Ptrofs.unsigned x0) rs !! src).
      pose proof (ptrofs_unsigned_lt_int_max x0).
      assert (0 <= Ptrofs.unsigned x0 < fn_stacksize f \/ fn_stacksize f <= Ptrofs.unsigned x0 <= Int.max_unsigned) by lia.
      inv H4.
      + inv MARR. inv H4. eexists. econstructor. econstructor. econstructor. econstructor.
        eauto. econstructor. cbn. eauto. econstructor. cbn. unfold ZToValue.
        unfold Int.zero. unfold Int.eq. rewrite ! Int.unsigned_repr by crush.
        cbn. eauto. (* exploit exists_ptr_add_int; eauto. intros (a & HPTR). *)
        (* rewrite HPTR in H. cbn in H. *)
        assert (HARCHI: Archi.ptr64 = false) by auto.
        unfold arr_assocmap_lookup. setoid_rewrite H6. eauto.
      + apply BOUNDS in H5; auto. inv H5. rewrite ptrofs_unsigned_add_0 in H6.
        unfold Mem.storev in H1. rewrite H6 in H1. discriminate.
    - inv H. inv H2. inv MARR. inv H. repeat econstructor. unfold arr_assocmap_lookup.
      setoid_rewrite H2. auto.
    - inv H. inv H2. inv MARR. inv H. repeat econstructor. unfold arr_assocmap_lookup.
      setoid_rewrite H2. auto.
  Qed.

  Lemma stack_correct_transl:
    forall f m_,
      transl_module f = OK m_ ->
      0 <= fn_stacksize f /\ fn_stacksize f < Ptrofs.modulus /\ fn_stacksize f mod 4 = 0.
  Proof.
    intros; unfold transl_module, Errors.bind, ret in *; repeat destr. inv H.
    cbn in *. eapply stack_correct_inv; eauto.
  Qed.

  Lemma stack_correct_match_states:
    forall s f sp pc rs pr s' m_ asr asa m,
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      0 <= fn_stacksize f /\ fn_stacksize f < Ptrofs.modulus /\ fn_stacksize f mod 4 = 0.
  Proof.
    inversion 1; subst. unfold transl_module, Errors.bind, ret in *; repeat destr. inv TF.
    cbn in *. eapply stack_correct_inv; eauto.
  Qed.

  Lemma load_exists_pointer_offset :
    forall s f pc rs pr m v v' sp s' m_ asr asa,
      stack_based v sp ->
      Mem.loadv Mint32 m v = Some v' ->
      match_states (GibleSubPar.State s f (Values.Vptr sp (Ptrofs.repr 0)) pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists ptr, 0 <= ptr < fn_stacksize f / 4 /\ v = Values.Val.offset_ptr (Values.Vptr sp (Ptrofs.repr 0)) (Ptrofs.repr (4 * ptr)).
  Proof.
    intros * HSTACK HMEM HMATCH.
    exploit loadv_exists_ptr; eauto. intros (sp0 & v0 & HVAL).
    unfold Values.Val.offset_ptr. subst; exploit loadv_mod_ok2; eauto.
    intros. inv HMATCH. unfold stack_bounds in *.
    specialize (BOUNDS (Ptrofs.unsigned v0)).
    pose proof (ptrofs_unsigned_lt_int_max v0) as HY.
    assert (HX: 0 <= Ptrofs.unsigned v0 < fn_stacksize f \/ fn_stacksize f <= Ptrofs.unsigned v0 <= Int.max_unsigned) by lia.
    inv HX.
    + inv MARR. 
      assert (Ptrofs.unsigned v0 = (Ptrofs.unsigned v0 / 4) * 4).
      { erewrite Z_div_mod_eq_full at 1. rewrite H. lia. }
      assert (fn_stacksize f = (fn_stacksize f / 4) * 4).
      { erewrite Z_div_mod_eq_full at 1. exploit stack_correct_transl; eauto; intros (STK1 & STK2 & STK3). rewrite STK3. lia. }
      assert (0 <= Ptrofs.unsigned v0 / 4 < fn_stacksize f / 4) by lia. eexists; split; eauto.
      replace (4 * (Ptrofs.unsigned v0 / 4)) with (Ptrofs.unsigned v0) by lia.
      rewrite Ptrofs.repr_unsigned by eauto. rewrite Ptrofs.add_zero_l.
      inv SP. cbn in HSTACK; subst. auto.
    + apply BOUNDS in H0; auto. inv H0. rewrite ptrofs_unsigned_add_0 in H2.
      unfold Mem.loadv in HMEM. inv SP. cbn in HSTACK. subst. rewrite HMEM in H2. discriminate.
  Qed.

  Lemma div_ineq :
    forall a x y, 0 <= x <= a -> 0 <= y <= a -> y <> 0 -> 0 <= x / y <= a.
  Proof.
    intros. pose proof (Z_div_pos x y ltac:(lia) ltac:(lia)). split; auto.
    pose proof (Z.div_le_mono x a y ltac:(lia) ltac:(lia)).
    assert (a / y <= a).
    { eapply Z.div_le_upper_bound; try lia. nia. }
    lia.
  Qed.

  Lemma expr_runp_load_1 :
    forall z s f sp pc rs pr' m' s' m_ asr asa r0 v,
      check_address_parameter_signed z = true ->
      match_states (GibleSubPar.State s f (Values.Vptr sp (Ptrofs.repr 0)) pc rs pr' m') (DHTL.State s' m_ pc asr asa) ->
      Mem.loadv Mint32 m' (Values.Val.add rs !! r0 (Values.Vint (Int.repr z))) = Some v ->
      Ple r0 (max_reg_function f) ->
      exists v' : value,
      expr_runp tt asr asa (Vvari (DHTL.mod_stk m_) (Vbinop Vdivu (boplitz Vadd r0 z) (Vlit (ZToValue 4)))) v' /\
      val_value_lessdef v v'.
  Proof.
    intros * HCHECK HMATCH HLOAD HPLE.
    exploit load_exists_pointer_offset. 2: { eauto. } 2: { eauto. } inv HMATCH. inv SP. eapply val_add_stack_based; eauto. now cbn.
    intros (ptr & HSIZE & HVAL).
    inv HMATCH. inv MARR; simplify. rename H2 into HPTR1, H4 into HPTR2, H0 into HSTACK, H into HLEN1, H1 into HLEN2, H3 into HEQ.
    rewrite HVAL in HLOAD. specialize (HEQ ptr ltac:(lia)).
    unfold Mem.loadv in HLOAD. rewrite HLOAD in HEQ.
    inv HEQ. exists (get_mem (Z.to_nat ptr) stack); split; auto.
    repeat (econstructor; eauto).
    unfold arr_assocmap_lookup, get_mem. setoid_rewrite HSTACK.
    do 4 f_equal.
    destruct (rs !! r0) eqn:HRS; try discriminate.
    cbn in *. replace Archi.ptr64 with false in HVAL by auto.
    rewrite Ptrofs.add_zero_l in HVAL.
    assert (Ptrofs.unsigned (Ptrofs.repr (4 * ptr)) = Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr z)))).
    { inv HVAL; eauto. }
    assert (HR: forall a b, a < b -> a * 4 < b * 4) by lia. eapply HR in HPTR2.
    exploit stack_correct_transl; eauto; intros (HSTK1 & HSTK2 & HSTK3).
    replace (fn_stacksize f / 4 * 4) with (4 * (fn_stacksize f / 4)) in HPTR2 by lia.
    rewrite <- Z_div_exact_2 with (b := 4) in HPTR2 by lia.
    assert (0 <= 4 * ptr < fn_stacksize f) by lia.
    exploit stack_correct_transl; eauto; intros (STK1 & STK2 & STK3).
    assert (0 <= fn_stacksize f <= Ptrofs.max_unsigned) by crush.
    rewrite Ptrofs.unsigned_repr in H by lia.
    assert (forall a b c, a = b -> a / c = b / c) by (intros; subst; auto).
    apply H3 with (c := 4) in H.
    replace (4 * ptr / 4) with (ptr) in H. 2: { replace (4 * ptr) with (ptr * 4) by lia. now rewrite Z_div_mult. } subst.
    rewrite <- offset_expr_ok. f_equal.
    replace 4 with (Ptrofs.unsigned (Ptrofs.repr 4)) at 2 by eauto.
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr z))) / Ptrofs.unsigned (Ptrofs.repr 4)) with 
      (Ptrofs.unsigned (Ptrofs.divu (Ptrofs.add i (Ptrofs.of_int (Int.repr z))) (Ptrofs.repr 4))).
    2: { unfold Ptrofs.divu. rewrite Ptrofs.unsigned_repr. auto.
         assert (0 <= Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr z))) <= Ptrofs.max_unsigned) by auto using Ptrofs.unsigned_range_2.
         assert (0 <= Ptrofs.unsigned (Ptrofs.repr 4) <= Ptrofs.max_unsigned) by auto using Ptrofs.unsigned_range_2.
         eapply div_ineq; eauto. crush.
       }
   repeat f_equal. unfold uvalueToZ. inv MASSOC. eapply H in HPLE.  rewrite HRS in HPLE. inv HPLE; auto.
  Qed.

  Lemma expr_runp_load_2 :
    forall z s f sp pc rs pr' m' s' m_ asr asa r0 v r1 z0,
      check_address_parameter_signed z = true ->
      match_states (GibleSubPar.State s f (Values.Vptr sp (Ptrofs.repr 0)) pc rs pr' m') (DHTL.State s' m_ pc asr asa) ->
      Mem.loadv Mint32 m' (Values.Val.add rs !! r0 (Values.Val.add (Values.Val.mul rs !! r1 (Values.Vint (Int.repr z))) (Values.Vint (Int.repr z0)))) = Some v ->
      Ple r0 (max_reg_function f) ->
      Ple r1 (max_reg_function f) ->
      exists v' : value,
      expr_runp tt asr asa (Vvari m_.(DHTL.mod_stk)
               (Vbinop Vdivu (Vbinop Vadd (boplitz Vadd r0 z0) (boplitz Vmul r1 z)) (Vlit (ZToValue 4)))) v' /\
      val_value_lessdef v v'.
  Proof.
    intros * HCHECK HMATCH HLOAD HPLE1 HPLE2.
    exploit load_exists_pointer_offset. 2: { eauto. } 2: { eauto. } inv HMATCH. inv SP. eapply val_add_stack_based; eauto.
    eapply val_add_stack_based; cbn; eauto. eapply val_mul_stack_based; cbn; eauto.
    intros (ptr & HSIZE & HVAL).
    inv HMATCH. inv MARR; simplify. rename H2 into HPTR1, H4 into HPTR2, H0 into HSTACK, H into HLEN1, H1 into HLEN2, H3 into HEQ.
    rewrite HVAL in HLOAD. specialize (HEQ ptr ltac:(lia)).
    unfold Mem.loadv in HLOAD. rewrite HLOAD in HEQ.
    inv HEQ. exists (get_mem (Z.to_nat ptr) stack); split; auto.
    repeat (econstructor; eauto).
    unfold arr_assocmap_lookup, get_mem. setoid_rewrite HSTACK.
    repeat f_equal.
    destruct (rs !! r0) eqn:HRS1; destruct (rs !! r1) eqn:HRS2; try discriminate.
    cbn in *. replace Archi.ptr64 with false in HVAL by auto.
    rewrite Ptrofs.add_zero_l in HVAL.
    assert (Ptrofs.unsigned (Ptrofs.repr (4 * ptr)) = Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.add (Int.mul i0 (Int.repr z)) (Int.repr z0))))).
    { inv HVAL; eauto. }
    assert (HR: forall a b, a < b -> a * 4 < b * 4) by lia. eapply HR in HPTR2.
    exploit stack_correct_transl; eauto; intros (HSTK1 & HSTK2 & HSTK3).
    replace (fn_stacksize f / 4 * 4) with (4 * (fn_stacksize f / 4)) in HPTR2 by lia.
    rewrite <- Z_div_exact_2 with (b := 4) in HPTR2 by lia.
    assert (0 <= 4 * ptr < fn_stacksize f) by lia.
    exploit stack_correct_transl; eauto; intros (STK1 & STK2 & STK3).
    assert (0 <= fn_stacksize f <= Ptrofs.max_unsigned) by crush.
    rewrite Ptrofs.unsigned_repr in H by lia.
    assert (forall a b c, a = b -> a / c = b / c) by (intros; subst; auto).
    apply H3 with (c := 4) in H.
    replace (4 * ptr / 4) with (ptr) in H. 2: { replace (4 * ptr) with (ptr * 4) by lia. now rewrite Z_div_mult. } subst.
    rewrite <- offset_expr_ok_2. f_equal.
    replace 4 with (Ptrofs.unsigned (Ptrofs.repr 4)) at 2 by eauto.
    match goal with |- _ = Ptrofs.unsigned ?a / Ptrofs.unsigned ?b => replace (Ptrofs.unsigned a / Ptrofs.unsigned b) with (Ptrofs.unsigned (Ptrofs.divu a b)) end.
    2: { unfold Ptrofs.divu. rewrite Ptrofs.unsigned_repr. auto.
         match goal with |- _ <= Ptrofs.unsigned ?a / Ptrofs.unsigned ?b <= _ => 
           assert (0 <= Ptrofs.unsigned a <= Ptrofs.max_unsigned) by auto using Ptrofs.unsigned_range_2;
           assert (0 <= Ptrofs.unsigned b <= Ptrofs.max_unsigned) by auto using Ptrofs.unsigned_range_2
         end.
         eapply div_ineq; eauto. crush.
       }
   repeat f_equal. 
   - unfold uvalueToZ. inv MASSOC. eapply H in HPLE1. rewrite HRS1 in HPLE1. inv HPLE1; auto.
   - unfold uvalueToZ. inv MASSOC. eapply H in HPLE2. rewrite HRS2 in HPLE2. inv HPLE2; auto.
  Qed.

  Lemma expr_runp_load_3 :
    forall s f sp pc rs pr' m' s' m_ asr asa v i,
      match_states (GibleSubPar.State s f (Values.Vptr sp (Ptrofs.repr 0)) pc rs pr' m') (DHTL.State s' m_ pc asr asa) ->
      Mem.loadv Mint32 m' (Values.Val.offset_ptr (Values.Vptr sp (Ptrofs.repr 0)) i) = Some v ->
      exists v' : value,
      expr_runp tt asr asa (Vvari m_.(DHTL.mod_stk) (Vlit (ZToValue (Ptrofs.unsigned i / 4)))) v' /\
      val_value_lessdef v v'.
  Proof.
    intros * HMATCH HLOAD.
    exploit load_exists_pointer_offset. 2: { eauto. } 2: { eauto. } inv HMATCH. inv SP. unfold Values.Val.offset_ptr; cbn; auto.
    intros (ptr & HSIZE & HVAL).
    inv HMATCH. inv MARR; simplify. rename H2 into HPTR1, H4 into HPTR2, H0 into HSTACK, H into HLEN1, H1 into HLEN2, H3 into HEQ.
    specialize (HEQ ptr ltac:(lia)). rewrite ! Ptrofs.add_zero_l in *.
    assert (HUNSG: Ptrofs.unsigned i = (Ptrofs.unsigned (Ptrofs.repr (4 * ptr)))) by (inv HVAL; eauto). rewrite <- HUNSG in HEQ.
    unfold Mem.loadv in HLOAD. rewrite HLOAD in HEQ.
    inv HEQ. exists (get_mem (Z.to_nat ptr) stack); split; auto.
    repeat (econstructor; eauto).
    unfold arr_assocmap_lookup, get_mem. setoid_rewrite HSTACK.
    repeat f_equal.
    unfold valueToNat, ZToValue. f_equal. rewrite Int.unsigned_repr.
    2: { eapply div_ineq; eauto using ptrofs_unsigned_lt_int_max; crush. }
    rewrite Ptrofs.unsigned_repr in HUNSG. rewrite HUNSG. replace (4 * ptr) with (ptr * 4) by lia.
    now rewrite Z_div_mult by lia.
    exploit stack_correct_transl; eauto; simplify. lia.
    assert (HR: forall a b, a < b -> a * 4 < b * 4) by lia. eapply HR in HPTR2.
    replace (fn_stacksize f / 4 * 4) with (4 * (fn_stacksize f / 4)) in HPTR2 by lia.
    rewrite <- Z_div_exact_2 with (b := 4) in HPTR2 by lia. lia.
  Qed.

  Lemma reset_transl_module :
    forall f m_,
      transl_module f = OK m_ ->
      m_.(DHTL.mod_reset) = Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (max_resource_function f)))))).
  Proof.
    unfold transl_module, Errors.bind, ret. intros. repeat destr; inv H; auto.
  Qed.

  Opaque translate_predicate.
  Lemma transl_load_correct :
    forall m0 a0 l f e m_ asa asr asa0 asr0 pr next_p sp rs m rs' pr' m' o r s pc s' a stmnt,
      translate_arr_access m0 a0 l (ctrl_stack (mk_ctrl f)) = OK e ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr next_p = true ->
      truthy pr o ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) (RBload o m0 a0 l r) 
        (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses (RBload o m0 a0 l r)) ->
      Ple (max_predicate next_p) (max_pred_function f) ->
      Ple (max_reg_instr a (RBload o m0 a0 l r)) (max_reg_function f) ->
      exists (asr' : AssocMap.t value) (asa' : AssocMap.t arr),
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)
          (Vseq stmnt (translate_predicate Vblock (Some (Pand next_p (dfltp o))) (Vvar (reg_enc r)) e)) 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') /\
        match_states (GibleSubPar.State s f sp pc rs' pr' m') (DHTL.State s' m_ pc asr' asa') /\ eval_predf pr' next_p = true.
  Proof.
    intros * HTRANSL HSTMNT HEVAL HTRUTHY HSTEP HMATCH HFRL HPLE1 HPLE2.
    unfold translate_arr_access in HTRANSL; repeat destr; destruct_match; try discriminate; repeat destr;
    inv HTRANSL.
    - inv HSTEP. rename H4 into HADDR, H12 into MEMLOAD, H13 into HTRUTHY'. clear HTRUTHY'.
      2: { inv H3. inv HTRUTHY. cbn in *. now rewrite H1 in H0. }
      unfold Op.eval_addressing in *. replace Archi.ptr64 with false in HADDR by auto. cbn in *. inv HADDR.
      assert (HEXPR: exists v', expr_runp tt asr asa (Vvari (Pos.succ (Pos.succ (Pos.succ (Pos.succ (max_resource_function f))))) (Vbinop Vdivu (boplitz Vadd r0 z) (Vlit (ZToValue 4)))) v' /\ val_value_lessdef v v').
      { inv HMATCH; exploit mk_ctrl_correct; eauto. simplify. rewrite H. eapply expr_runp_load_1; eauto. econstructor; eauto. extlia. }
      destruct HEXPR as (v' & HEXPR' & HVAL).
      exists (AssocMap.set (reg_enc r) v' asr), asa; split; [|split].
      econstructor; eauto.
      eapply transl_predicate_correct2_true; try eassumption.
      { cbn. instantiate (1:=max_pred_function f).
        destruct o; cbn; [eapply le_max_pred in HFRL|]; extlia. }
      inv HMATCH; eassumption.
      rewrite eval_predf_Pand. rewrite HEVAL. rewrite truthy_dflt; eauto.
      assert (HREG: Ple r (max_reg_function f)) by extlia.
      inv HMATCH. econstructor; eauto. eapply regs_lessdef_add_match; auto. eauto.
      eapply state_st_wf_write; eauto.
      { symmetry in TF; eapply mk_ctrl_correct in TF. inv TF. rewrite <- H. cbn.
        eapply ple_max_resource_function in HREG. extlia. }
      unfold reg_stack_based_pointers; intros. destruct (peq r r1); subst; [|rewrite PMap.gso by auto; eauto].
      rewrite PMap.gss. unfold arr_stack_based_pointers in ASBP.
      exploit load_exists_pointer_offset. 2: { eauto. } eapply val_add_stack_based; eauto.
      now cbn. econstructor; eauto. intros (ptr & HSIZE & HVAL').
      eapply ASBP in HSIZE. rewrite HVAL' in MEMLOAD. rewrite MEMLOAD in HSIZE. eauto.
      exploit mk_ctrl_correct; eauto. simplify. inv CONST.
      assert (HX: Ple r (max_reg_function f)) by extlia. eapply ple_max_resource_function in HX.
      exploit reset_transl_module; eauto; intros.
      econstructor; rewrite AssocMap.gso by extlia; auto.
      auto.
    - inv HSTEP. rename H4 into HADDR, H12 into MEMLOAD, H13 into HTRUTHY'. clear HTRUTHY'.
      2: { inv H3. inv HTRUTHY. cbn in *. now rewrite H1 in H0. }
      unfold Op.eval_addressing in *. replace Archi.ptr64 with false in HADDR by auto. cbn in *. inv HADDR.
      assert (HEXPR: exists v', expr_runp tt asr asa (Vvari (Pos.succ (Pos.succ (Pos.succ (Pos.succ (max_resource_function f)))))
               (Vbinop Vdivu (Vbinop Vadd (boplitz Vadd r0 z0) (boplitz Vmul r1 z)) (Vlit (ZToValue 4)))) v' /\ val_value_lessdef v v').
      { inv HMATCH; exploit mk_ctrl_correct; eauto. simplify. rewrite H. eapply expr_runp_load_2; eauto. econstructor; eauto. extlia. extlia. }
      destruct HEXPR as (v' & HEXPR' & HVAL).
      exists (AssocMap.set (reg_enc r) v' asr), asa; split; [|split].
      econstructor; eauto.
      eapply transl_predicate_correct2_true; try eassumption.
      { cbn. instantiate (1:=max_pred_function f).
        destruct o; cbn; [eapply le_max_pred in HFRL|]; extlia. }
      inv HMATCH; eassumption.
      rewrite eval_predf_Pand. rewrite HEVAL. rewrite truthy_dflt; eauto.
      assert (HREG: Ple r (max_reg_function f)) by extlia.
      inv HMATCH. econstructor; eauto. eapply regs_lessdef_add_match; auto. eauto.
      eapply state_st_wf_write; eauto.
      { symmetry in TF; eapply mk_ctrl_correct in TF. inv TF. rewrite <- H. cbn.
        eapply ple_max_resource_function in HREG. extlia. }
      unfold reg_stack_based_pointers; intros. destruct (peq r r2); subst; [|rewrite PMap.gso by auto; eauto].
      rewrite PMap.gss. unfold arr_stack_based_pointers in ASBP.
      exploit load_exists_pointer_offset. 2: { eauto. } eapply val_add_stack_based; eauto.
      eapply val_add_stack_based; cbn; eauto. eapply val_mul_stack_based; cbn; eauto.
      econstructor; eauto. intros (ptr & HSIZE & HVAL').
      eapply ASBP in HSIZE. rewrite HVAL' in MEMLOAD. rewrite MEMLOAD in HSIZE. eauto.
      exploit mk_ctrl_correct; eauto. simplify. inv CONST.
      assert (HX: Ple r (max_reg_function f)) by extlia. eapply ple_max_resource_function in HX.
      exploit reset_transl_module; eauto; intros.
      econstructor; rewrite AssocMap.gso by extlia; auto.
      auto.
    - inv HSTEP. rename H4 into HADDR, H12 into MEMLOAD, H13 into HTRUTHY'. clear HTRUTHY'.
      2: { inv H3. inv HTRUTHY. cbn in *. now rewrite H1 in H0. }
      unfold Op.eval_addressing in *. replace Archi.ptr64 with false in HADDR by auto. cbn in *. 
      replace Archi.ptr64 with false in * by auto. inv HADDR.
      assert (HEXPR: exists v', expr_runp tt asr asa (Vvari (Pos.succ (Pos.succ (Pos.succ (Pos.succ (max_resource_function f))))) (Vlit (ZToValue (Ptrofs.unsigned i / 4)))) v' /\ val_value_lessdef v v').
      { inv HMATCH; exploit mk_ctrl_correct; eauto. simplify. rewrite H. eapply expr_runp_load_3; try eassumption. econstructor; eauto. eauto. }
      destruct HEXPR as (v' & HEXPR' & HVAL).
      exists (AssocMap.set (reg_enc r) v' asr), asa; split; [|split].
      econstructor; eauto.
      eapply transl_predicate_correct2_true; try eassumption.
      { cbn. instantiate (1:=max_pred_function f).
        destruct o; cbn; [eapply le_max_pred in HFRL|]; extlia. }
      inv HMATCH; eassumption.
      rewrite eval_predf_Pand. rewrite HEVAL. rewrite truthy_dflt; eauto.
      assert (HREG: Ple r (max_reg_function f)) by extlia.
      inv HMATCH. econstructor; eauto. eapply regs_lessdef_add_match; auto. eauto.
      eapply state_st_wf_write; eauto.
      { symmetry in TF; eapply mk_ctrl_correct in TF. inv TF. rewrite <- H. cbn.
        eapply ple_max_resource_function in HREG. extlia. }
      unfold reg_stack_based_pointers; intros. destruct (peq r r0); subst; [|rewrite PMap.gso by auto; eauto].
      rewrite PMap.gss. unfold arr_stack_based_pointers in ASBP.
      exploit load_exists_pointer_offset. 2: { eauto. } replace Archi.ptr64 with false by auto. 
      unfold Values.Val.offset_ptr. cbn. eauto.
      econstructor; eauto. intros (ptr & HSIZE & HVAL').
      eapply ASBP in HSIZE. rewrite HVAL' in MEMLOAD. rewrite MEMLOAD in HSIZE. eauto.
      exploit mk_ctrl_correct; eauto. simplify. inv CONST.
      assert (HX: Ple r (max_reg_function f)) by extlia. eapply ple_max_resource_function in HX.
      exploit reset_transl_module; eauto; intros.
      econstructor; rewrite AssocMap.gso by extlia; auto.
      auto.
  Qed.

  Lemma exec_expr_store_1 :
    forall f m_ rs' pr' asr r0 z sp v' asa,
      transl_module f = OK m_ ->
      match_assocmaps (max_reg_function f) (max_pred_function f) rs' pr' asr ->
      Values.Val.add rs' !! r0 (Values.Vint (Int.repr z)) = Values.Vptr sp v' ->
      reg_stack_based_pointers sp rs' ->
      Ple r0 (max_reg_function f) ->
      expr_runp tt asr asa (Vbinop Vdivu (boplitz Vadd r0 z) (Vlit (ZToValue 4))) (Int.divu (ptrToValue v') (ZToValue 4)).
  Proof.
    intros. rename H3 into HPLE. repeat econstructor. cbn.
    replace (Int.eq (ZToValue 4) Int.zero) with false.
    2: { unfold Int.eq. destruct_match; auto. exfalso. unfold Int.zero, ZToValue in *. 
         clear Heqs. rewrite ! Int.unsigned_repr in e; [discriminate| |]; crush. }
    unfold ptrToValue.
    destruct (rs' !! r0) eqn:?; crush.
    replace Archi.ptr64 with false in H1 by auto. inv H1.
    f_equal. unfold Ptrofs.to_int.
    symmetry; rewrite <- Int.repr_unsigned at 1. symmetry. f_equal.
    apply Ptrofs.agree32_add; auto; unfold ZToValue.
    2: { apply Ptrofs.agree32_of_int; auto. }
    inv H0. exploit H1; eauto; intros. rewrite Heqv in H0. inv H0. unfold valueToPtr.
    apply Ptrofs.agree32_of_int; auto.
  Qed.


  Lemma exec_expr_store_2 :
    forall f m_ rs' pr' asr r0 r1 z sp v' asa z0,
      transl_module f = OK m_ ->
      match_assocmaps (max_reg_function f) (max_pred_function f) rs' pr' asr ->
      Values.Val.add rs' !! r0 (Values.Val.add (Values.Val.mul rs' !! r1 (Values.Vint (Int.repr z))) (Values.Vint (Int.repr z0))) = Values.Vptr sp v' ->
      reg_stack_based_pointers sp rs' ->
      Ple r0 (max_reg_function f) ->
      Ple r1 (max_reg_function f) ->
      expr_runp tt asr asa (Vbinop Vdivu (Vbinop Vadd (boplitz Vadd r0 z0) (boplitz Vmul r1 z)) (Vlit (ZToValue 4))) (Int.divu (ptrToValue v') (ZToValue 4)).
  Proof.
    intros * ? ? ? ? ? HPLE2. rename H3 into HPLE. repeat econstructor. cbn.
    replace (Int.eq (ZToValue 4) Int.zero) with false.
    2: { unfold Int.eq. destruct_match; auto. exfalso. unfold Int.zero, ZToValue in *. 
         clear Heqs. rewrite ! Int.unsigned_repr in e; [discriminate| |]; crush. }
    unfold ptrToValue.
    destruct (rs' !! r0) eqn:?; crush;
    destruct (rs' !! r1) eqn:?; crush.
    replace Archi.ptr64 with false in H1 by auto. inv H1.
    f_equal. unfold Ptrofs.to_int.
    symmetry; rewrite <- Int.repr_unsigned at 1. symmetry. f_equal.
    setoid_rewrite Int.add_commut at 2.
    rewrite Int.add_permut at 1.
    apply Ptrofs.agree32_add; auto; unfold ZToValue.
    inv H0. exploit H1; try eapply HPLE; intros. rewrite Heqv in H0. inv H0. unfold valueToPtr.
    apply Ptrofs.agree32_of_int; auto.
    assert (forall a b : int, b = a -> Ptrofs.agree32 (Ptrofs.of_int b) a) by (intros; subst; eauto using Ptrofs.agree32_of_int).
    eapply H1. repeat f_equal.
    inv H0. exploit H3; eauto; intros. rewrite Heqv0 in H0. inv H0. unfold valueToPtr. auto.
  Qed.

  Lemma le_in_range :
    forall a b c,
      c >= 0 ->
      a mod c = 0 ->
      0 <= a <= b ->
      0 <= a / c <= b.
  Proof.
    intros * ? HY **.
    split.
    - apply Z_div_nonneg_nonneg; lia.
    - assert (forall a b c, c > 0 -> a * c <= b * c -> a <= b) by nia.
      destruct (Z.eq_dec c 0); subst; try lia. rewrite Zdiv_0_r; lia.
      apply H1 with (c:=c); try lia.
      rewrite ZLib.div_mul_undo by lia. nia.
  Qed.

  Lemma lt_in_range :
    forall a b c,
      c >= 0 ->
      a mod c = 0 ->
      0 <= a < b ->
      0 <= a / c < b.
  Proof.
    intros * ? HY **.
    split.
    - apply Z_div_nonneg_nonneg; lia.
    - assert (forall a b c, c > 0 -> a * c < b * c -> a < b) by nia.
      destruct (Z.eq_dec c 0); subst; try lia. rewrite Zdiv_0_r; lia.
      apply H1 with (c:=c); try lia.
      rewrite ZLib.div_mul_undo by lia. nia.
  Qed.

  Hint Resolve int_unsigned_lt_ptrofs_max : int_ptrofs.
  Hint Resolve ptrofs_unsigned_lt_int_max : int_ptrofs.
  Hint Resolve Ptrofs.unsigned_range_2 : int_ptrofs.
  Hint Resolve Int.unsigned_range_2 : int_ptrofs.

  Lemma ptrofs_mod_4 :
    forall a m b v,
      Mem.load Mint32 m b (Ptrofs.unsigned a) = Some v ->
      Int.unsigned (ptrToValue a) mod 4 = 0.
  Proof. 
    intros. exploit loadv_mod_ok2. unfold Mem.loadv. eassumption. intros.
    rewrite <- H0; symmetry. unfold ptrToValue. f_equal. apply Ptrofs.agree32_to_int; auto.
  Qed.

  Lemma ptrofs_div_4 :
    forall a,
      Int.unsigned (ptrToValue a) mod 4 = 0 ->
      ((Ptrofs.unsigned (Ptrofs.repr (4 * Int.unsigned (Int.divu (ptrToValue a) (ZToValue 4))))) = Ptrofs.unsigned a).
  Proof. 
    intros. unfold Int.divu. rewrite Int.unsigned_repr.
    replace (Int.unsigned (ZToValue 4)) with 4 by auto. rewrite <- Z_div_exact_2.
    rewrite Ptrofs.unsigned_repr. unfold ptrToValue. symmetry. apply Ptrofs.agree32_to_int; auto.
    apply int_unsigned_lt_ptrofs_max. lia. auto.
    unfold ZToValue; rewrite ! Int.unsigned_repr; try now crush. apply le_in_range. lia. auto.
    auto with int_ptrofs.
  Qed.

  Lemma equiv_stack_pointer_reg_stack_based :
    forall rs b,
      reg_stack_based_pointers b rs ->
      forall sp r i,
        rs !! r = Values.Vptr sp i ->
        b = sp.
  Proof.
    intros * RSBP * Heqv1.
    unfold reg_stack_based_pointers, stack_based in RSBP. specialize (RSBP r). now rewrite Heqv1 in RSBP.
  Qed.

  Lemma storev_stack_bounds :
    forall m sp v dst m' hi,
      Mem.storev Mint32 m (Values.Vptr sp v) dst = Some m' ->
      stack_bounds (Values.Vptr sp (Ptrofs.repr 0)) hi m ->
      (Ptrofs.unsigned v) mod 4 = 0 ->
      0 <= Ptrofs.unsigned v < hi.
  Proof.
    intros. unfold stack_bounds in *.
    pose proof (Ptrofs.unsigned_range_2 v).
    assert (Ptrofs.max_unsigned = Int.max_unsigned) by crush.
    destruct (Z.lt_decidable Int.max_unsigned hi).
    - lia.
    - assert (0 <= Ptrofs.unsigned v < hi \/ hi <= Ptrofs.unsigned v <= Int.max_unsigned) by lia.
      inv H5; auto. pose proof (H0 _ dst H6 H1). destruct H5. rewrite Ptrofs.repr_unsigned in *. 
      cbn in H7. rewrite Ptrofs.add_zero_l in *. unfold Mem.storev in *. congruence.
  Qed.

  Lemma loadv_stack_bounds :
    forall m sp v m' hi,
      Mem.loadv Mint32 m (Values.Vptr sp v) = Some m' ->
      stack_bounds (Values.Vptr sp (Ptrofs.repr 0)) hi m ->
      (Ptrofs.unsigned v) mod 4 = 0 ->
      0 <= Ptrofs.unsigned v < hi.
  Proof.
    intros. unfold stack_bounds in *.
    pose proof (Ptrofs.unsigned_range_2 v).
    assert (Ptrofs.max_unsigned = Int.max_unsigned) by crush.
    destruct (Z.lt_decidable Int.max_unsigned hi).
    - lia.
    - assert (0 <= Ptrofs.unsigned v < hi \/ hi <= Ptrofs.unsigned v <= Int.max_unsigned) by lia.
      inv H5; auto. pose proof (H0 _ (Values.Vint (Int.repr 0)) H6 H1). destruct H5. rewrite Ptrofs.repr_unsigned in *. 
      cbn in H5. rewrite Ptrofs.add_zero_l in *. unfold Mem.loadv in *. congruence.
  Qed.

  Lemma agree32_ptrToValue :
    forall p, Ptrofs.agree32 p (ptrToValue p).
  Proof.
    unfold ptrToValue. eapply Ptrofs.agree32_to_int; auto.
  Qed.

  Lemma div_lt_mono :
    forall a b c, c > 0 -> b mod c = 0 -> a < b -> a / c < b / c.
  Proof.
    intros. assert (forall a b c, c > 0 -> a * c < b * c -> a < b) by nia.
    eapply Zdiv_lt_upper_bound; try lia.
    replace (b / c * c) with (c * (b / c) + b mod c) by lia.
    now rewrite <- Z_div_mod_eq_full.
  Qed.

  Lemma div_lt_mono2 :
    forall a b c, c > 0 -> a mod c = 0 -> b mod c = 0 -> a / c < b / c -> a < b.
  Proof.
    intros * ? HY **.
    assert (forall a b, c > 0 -> a < b -> c * a < c * b) by (intros; apply Zmult_lt_compat_l; lia).
    apply H2 in H1; try lia.
    assert (c * (a / c) + a mod c < c * (b / c) + b mod c) by lia.
    now rewrite <- !Z_div_mod_eq_full in H3.
  Qed.

  Lemma int_divu_cast:
    forall a,
      Ptrofs.unsigned a mod 4 = 0 ->
      Int.unsigned (Int.divu (ptrToValue a) (ZToValue 4)) = 
        Ptrofs.unsigned a / 4.
  Proof.
    unfold Int.divu; intros. unfold ZToValue.
    pose proof (agree32_ptrToValue a). unfold Ptrofs.agree32 in *.
    repeat rewrite !Int.unsigned_repr; try now crush.
    eapply le_in_range; try now crush. auto with int_ptrofs.
  Qed.

  Lemma le_div_implies_le: 
    forall a b c, c >= 0 -> a mod c = 0 -> b mod c = 0 -> a / c <= b / c -> a <= b.
  Proof.
    intros * HGT **. rewrite Z_div_mod_eq_full with (a := a) (b := c).
    rewrite Z_div_mod_eq_full with (a := b) (b := c).
    rewrite H. rewrite H0. rewrite !Z.add_0_r.
    nia.
  Qed.

  Lemma not_eq_pointer_to_addr :
    forall ptr a,
      0 <= 4 * ptr <= Ptrofs.max_unsigned ->
      Ptrofs.unsigned a mod 4 = 0 ->
      ptr <> Int.unsigned (Int.divu (ptrToValue a) (ZToValue 4)) ->
      Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr (4 * ptr))) + 4 <= Ptrofs.unsigned a 
      \/ Ptrofs.unsigned a + 4 <= Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr (4 * ptr))).
  Proof.
    intros * HMAX **. rewrite int_divu_cast in *; auto.
    rewrite !Ptrofs.add_zero_l.
    assert (4 * ptr <> Ptrofs.unsigned a).
    { unfold not; intros. apply H0. rewrite <- H1. rewrite Z.mul_comm. now rewrite Z.div_mul. }
    rewrite Ptrofs.unsigned_repr; auto. destruct (Z.lt_decidable ptr (Ptrofs.unsigned a / 4)).
    - left. apply le_div_implies_le with (c := 4); try lia. rewrite ZLib.mod_add_r by lia.
      now rewrite ZLib.Z_mod_mult'.
      rewrite Z.add_comm. rewrite Z.mul_comm. rewrite Z_div_plus by lia. rewrite Z_div_same by lia.
      lia.
    - right. apply le_div_implies_le with (c := 4); try lia. now rewrite ZLib.mod_add_r by lia. 
      now rewrite ZLib.Z_mod_mult'.
      replace 4 with (4 * 1) at 1 by lia. rewrite Z.mul_comm. rewrite Z_div_plus by lia.
      rewrite Z.mul_comm. rewrite Z.div_mul by lia. lia.
  Qed.

  (* Lemma not_eq_pointer_to_addr' : *)
  (*   forall ptr a, *)
  (*     Ptrofs.unsigned a mod 4 = 0 -> *)
  (*     ptr <> Int.unsigned (Int.divu (ptrToValue a) (ZToValue 4)) -> *)
  (*     Ptrofs.unsigned (Ptrofs.repr (4 * ptr)) + 4 <= Ptrofs.unsigned a  *)
  (*     \/ Ptrofs.unsigned a + 4 <= Ptrofs.unsigned (Ptrofs.repr (4 * ptr)). *)
  (* Proof. *)
  (*   intros * HMAX **. rewrite int_divu_cast in *; auto. *)
  (*   rewrite !Ptrofs.add_zero_l. *)
  (*   assert (4 * ptr <> Ptrofs.unsigned a). *)
  (*   { unfold not; intros. apply H0. rewrite <- H1. rewrite Z.mul_comm. now rewrite Z.div_mul. } *)
  (*   rewrite Ptrofs.unsigned_repr; auto. destruct (Z.lt_decidable ptr (Ptrofs.unsigned a / 4)). *)
  (*   - left. apply le_div_implies_le with (c := 4); try lia. rewrite ZLib.mod_add_r by lia. *)
  (*     now rewrite ZLib.Z_mod_mult'. *)
  (*     rewrite Z.add_comm. rewrite Z.mul_comm. rewrite Z_div_plus by lia. rewrite Z_div_same by lia. *)
  (*     lia. *)
  (*   - right. apply le_div_implies_le with (c := 4); try lia. now rewrite ZLib.mod_add_r by lia.  *)
  (*     now rewrite ZLib.Z_mod_mult'. *)
  (*     replace 4 with (4 * 1) at 1 by lia. rewrite Z.mul_comm. rewrite Z_div_plus by lia. *)
  (*     rewrite Z.mul_comm. rewrite Z.div_mul by lia. lia. *)
  (* Qed. *)

  Lemma out_of_range_of_load :
    forall a b c,
      c > 0 ->
      a <> b ->
      a mod c = 0 ->
      b mod c = 0 ->
      a + c <= b \/ b + c <= a.
  Proof.
    intros. 
    assert (a < b \/ b < a) by lia.
    inv H3; [left|right].
    - apply le_div_implies_le with (c:=c); try lia.
      rewrite ZLib.mod_add_r by lia. assumption.
      replace c with (1 * c) at 1 by lia.
      rewrite Z_div_plus by lia.
      apply div_lt_mono with (c:=c) in H4; lia.
    - apply le_div_implies_le with (c:=c); try lia.
      rewrite ZLib.mod_add_r by lia. assumption.
      replace c with (1 * c) at 1 by lia.
      rewrite Z_div_plus by lia.
      apply div_lt_mono with (c:=c) in H4; lia.
  Qed.

  Lemma forall_stack_based :
    forall m v rs r m' sp' sz,
      stack_based v sp' ->
      stack_bounds (Values.Vptr sp' (Ptrofs.repr 0)) sz m ->
      Mem.storev Mint32 m v rs !! r = Some m' ->
      reg_stack_based_pointers sp' rs ->
      arr_stack_based_pointers sp' m sz (Values.Vptr sp' (Ptrofs.repr 0)) ->
      arr_stack_based_pointers sp' m' sz (Values.Vptr sp' (Ptrofs.repr 0)).
  Proof.
    intros * HSTACK HMEM **. unfold arr_stack_based_pointers in *; intros. pose proof H2 as Y.
    eapply H1 in H2. unfold Mem.storev in *. repeat destr. subst. unfold Values.Val.offset_ptr in *; cbn in *.
    subst. unfold stack_bounds in *.
    destruct (Z.eq_dec (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr (4 * ptr)))) (Ptrofs.unsigned i)).
    - rewrite e in *.
      exploit Mem.load_store_same; eauto; intros HY. rewrite HY. cbn. destruct_match; cbn; auto.
      replace Archi.ptr64 with false by auto. unfold reg_stack_based_pointers in H0. specialize (H0 r).
      rewrite Heqv in H0. cbn in H0; subst. cbn; auto.
    - exploit Mem.load_store_other; eauto.
      2: { intros. rewrite H3; auto. }
      right. cbn. eapply out_of_range_of_load; try lia.
      + rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr_eq.
        rewrite <- Zmod_div_mod by crush. now rewrite ZLib.Z_mod_mult'.
      + eauto using storev_mod_ok2.
  Qed.


  Transparent Mem.store.
  Transparent Mem.load. 
  Lemma forall_stack_bounds :
    forall m v m' sp' sz ptr,
      Mem.storev Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) v = Some m' ->
      stack_bounds (Values.Vptr sp' (Ptrofs.repr 0)) sz m ->
      stack_bounds (Values.Vptr sp' (Ptrofs.repr 0)) sz m'.
  Proof.
    unfold stack_bounds; intros. rename H into H0, H0 into H2, H1 into H3, H2 into H4.
    assert (H: True) by auto. assert (H1: True) by auto.
    unfold Mem.storev in H0. repeat destr.
    assert (H2': forall (ptr : Z),
       sz <= ptr <= Ptrofs.max_unsigned ->
       ptr mod 4 = 0 ->
       Mem.loadv Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) = None /\
       (forall v, Mem.storev Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) v = None)).
    { intros. specialize (H2 ptr1); split; intros; [specialize (H2 Values.Vundef)|specialize (H2 v1)]; tauto. }
    specialize (H2' ptr0 H3 H4). inv H2'. split.
    - cbn in *.
      enough ((Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr ptr0))) <> (Ptrofs.unsigned i)).
      unfold Mem.load. destruct_match; auto. exfalso.
      eapply Mem.store_valid_access_2 in H0; eauto.
      unfold Mem.load in H5. destruct_match; try discriminate. eapply n.
      eapply Mem.valid_access_implies; eauto. constructor.
      unfold not; intros. rewrite <- H7 in *. eapply Mem.store_valid_access_3 in H0.
      eapply Mem.valid_access_implies in H0. eapply Mem.valid_access_load in H0. destruct H0.
      congruence. constructor.
    - cbn in *.
      enough ((Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr ptr0))) <> (Ptrofs.unsigned i)).
      unfold Mem.store. destruct_match; auto. exfalso.
      eapply Mem.store_valid_access_2 in H0; eauto. 
      unfold Mem.load in H5. destruct_match; try discriminate. eapply n.
      eapply Mem.valid_access_implies; eauto. constructor.
      unfold not; intros. rewrite <- H7 in *. eapply Mem.store_valid_access_3 in H0.
      eapply Mem.valid_access_implies in H0. eapply Mem.valid_access_load in H0. destruct H0.
      congruence. constructor.
  Qed.
  Transparent Mem.load.
  Transparent Mem.store.

  Lemma transl_store_correct :
    forall m0 a0 l f e asr0 asa0 asr asa next_p sp o m_ rs pr m r rs' pr' m' s pc s' a stmnt,
      translate_arr_access m0 a0 l (ctrl_stack (mk_ctrl f)) = OK e ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr next_p = true ->
      truthy pr o ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) (RBstore o m0 a0 l r) (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses (RBstore o m0 a0 l r)) ->
      Ple (max_predicate next_p) (max_pred_function f) ->
      Ple (max_reg_instr a (RBstore o m0 a0 l r)) (max_reg_function f) ->
      exists (asr' : AssocMap.t value) (asa' : AssocMap.t arr),
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)
          (Vseq stmnt (Vcond (Vbinop Vand (pred_expr next_p) (pred_expr (dfltp o))) (Vblock e (Vvar (reg_enc r))) Vskip)) (e_assoc asr')
          (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') /\
        match_states (GibleSubPar.State s f sp pc rs' pr' m') (DHTL.State s' m_ pc asr' asa') /\ eval_predf pr' next_p = true.
  Proof.
    intros * HTRANSL HSTMNT HEVAL HTRUTHY HSTEP HMATCH HFRL HPLE1 HPLE2.
    unfold translate_arr_access in HTRANSL; repeat destr; destruct_match; try discriminate; repeat destr;
    inv HTRANSL.
    - inv HSTEP. rename H4 into HADDR, H12 into MEMLOAD, H13 into HTRUTHY'. clear HTRUTHY'.
      2: { inv H3; cbn in *. inv HTRUTHY. congruence. }
      unfold Op.eval_addressing in HADDR. replace Archi.ptr64 with false in HADDR by auto; cbn in *. inv HADDR.
      exploit storev_exists_ptr; eauto. intros (sp0 & v' & HADD).
      exists asr, (arr_assocmap_set m_.(DHTL.mod_stk) (valueToNat (Int.divu (ptrToValue v') (ZToValue 4))) (find_assocmap 32 (reg_enc r) asr) asa).
      split; [|split].
      + repeat (econstructor; try eassumption).
        * eapply pred_expr_correct; intros. inv HMATCH. inv MASSOC. eapply H1; eauto. extlia.
        * eapply pred_expr_correct; intros. inv HMATCH. inv MASSOC. eapply H1; eauto. destruct o. cbn in *.
          eapply le_max_pred in HFRL. extlia. cbn in *. extlia.
        * rewrite int_and_boolToValue. rewrite valueToBool_correct. rewrite HEVAL. now rewrite truthy_dflt. 
        * cbn. inv HMATCH. exploit mk_ctrl_correct; eauto; simplify. rewrite H.
          econstructor. eapply exec_expr_store_1; eauto; try extlia.
          destruct (rs' !! r0) eqn:?; crush. replace Archi.ptr64 with false in HADD by auto. inv HADD.
          unfold reg_stack_based_pointers in *. unfold stack_based in *. pose proof (RSBP r0). rewrite Heqv in H2.
          now subst.
      + inv HMATCH; econstructor; eauto.
        * inv MARR. destruct H as (HARR1 & HARR2 & HARR3 & HARR4). econstructor.
          repeat split.
          -- erewrite arr_assocmap_set_gss by eassumption. eauto.
          -- now rewrite <- array_set_len.
          -- now rewrite <- array_set_len.
          -- intros * HBOUND. rewrite <- array_set_len in HBOUND. pose proof HBOUND as HBOUND'. learn HBOUND'. apply HARR4 in HBOUND. 
             unfold Mem.loadv, Mem.storev in *. move MEMLOAD after HBOUND. repeat destr.
             destruct (rs' !! r0) eqn:?; crush. replace Archi.ptr64 with false in Heqv0 by auto.
             inv Heqv0. inv HADD. inv Heqv. 
             exploit stack_correct_transl; eauto; intros (STK1 & STK2 & STK3).
             destruct (Z.eq_dec ptr (Int.unsigned (Int.divu (ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.repr z)))) (ZToValue 4)))); subst.
             ++ exploit Mem.load_store_same; eauto; intros.
                pose proof (ptrofs_mod_4 _ _ _ _ H) as HY.
                pose proof (ptrofs_div_4 _ HY) as HYY.
                assert (b = sp0) by (eapply equiv_stack_pointer_reg_stack_based; eauto); subst.
                rewrite get_mem_set_array_gss; try rewrite Ptrofs.add_zero_l in *.
                ** rewrite HYY.
                   subst. rewrite H. cbn. destruct_match; econstructor; try solve [repeat econstructor].
                   rewrite <- Heqv. inv MASSOC. eapply H2; extlia. replace Archi.ptr64 with false by auto. rewrite <- Heqv. 
                   inv MASSOC. eapply H2; extlia.
                ** unfold valueToNat. unfold Int.divu. unfold stack_bounds in *.
                   enough ((0 <= (Int.unsigned (Int.repr (Int.unsigned (ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.repr z)))) / Int.unsigned (ZToValue 4)))) < Z.of_nat (arr_length stack))); [lia|].
                   repeat rewrite !Int.unsigned_repr; try now crush.
                   2: { eapply le_in_range; eauto; try lia; eauto with int_ptrofs. }
                   exploit storev_stack_bounds; eauto. rewrite <- HY. f_equal. apply agree32_ptrToValue.
                   intros. rewrite HARR2. rewrite Z_to_nat_max.
                   replace (Z.max (fn_stacksize f / 4) 0) with (fn_stacksize f / 4).
                   pose proof (agree32_ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.repr z)))); unfold Ptrofs.agree32 in *.
                   split. eapply Z_div_nonneg_nonneg; lia.
                   eapply div_lt_mono; lia.
                   destruct (Z.max_dec (fn_stacksize f / 4) 0). congruence.
                   rewrite e. pose proof (Z.le_max_l (fn_stacksize f / 4) 0). rewrite e in H3. 
                   pose proof (Z_div_nonneg_nonneg _ 4 STK1 ltac:(lia)). lia.
             ++ exploit Mem.load_store_other; eauto.
                2: { intros HLOAD. rewrite HLOAD. rewrite get_mem_set_array_gso; auto. unfold not; intros. eapply n. unfold valueToNat in H.
                     pose proof (Int.unsigned_range_2 ((Int.divu (ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.repr z)))) (ZToValue 4)))). lia. }
                cbn. right. eapply not_eq_pointer_to_addr; eauto. enough (4 * ptr < fn_stacksize f). crush.
                apply div_lt_mono2 with (c := 4); try lia. apply ZLib.Z_mod_mult'.
                rewrite Z.mul_comm. rewrite Z_div_mult by lia. lia.
                eapply storev_mod_ok2; eauto.
         * eapply forall_stack_based. 3: { eassumption. } all: auto.
           destruct (rs' !! r0) eqn:?; try discriminate. cbn in *. replace Archi.ptr64 with false in * by auto. cbn in *.
           unfold reg_stack_based_pointers in *. specialize (RSBP r0). rewrite Heqv in RSBP. now cbn in RSBP.
         * destruct (rs' !! r0) eqn:?; try discriminate. cbn in *. replace Archi.ptr64 with false in * by auto. unfold Ptrofs.add in MEMLOAD. cbn in *.
           eapply forall_stack_bounds; cbn; try eassumption. rewrite Ptrofs.add_zero_l.
           enough (sp' = b); subst. eassumption. eapply equiv_stack_pointer_reg_stack_based; eauto.
      + auto.
    - inv HSTEP. rename H4 into HADDR, H12 into MEMLOAD, H13 into HTRUTHY'. clear HTRUTHY'.
      2: { inv H3; cbn in *. inv HTRUTHY. congruence. }
      unfold Op.eval_addressing in HADDR. replace Archi.ptr64 with false in HADDR by auto; cbn in *. inv HADDR.
      exploit storev_exists_ptr; eauto. intros (sp0 & v' & HADD).
      exists asr, (arr_assocmap_set m_.(DHTL.mod_stk) (valueToNat (Int.divu (ptrToValue v') (ZToValue 4))) (find_assocmap 32 (reg_enc r) asr) asa).
      split; [|split].
      + repeat (econstructor; try eassumption).
        * eapply pred_expr_correct; intros. inv HMATCH. inv MASSOC. eapply H1; eauto. extlia.
        * eapply pred_expr_correct; intros. inv HMATCH. inv MASSOC. eapply H1; eauto. destruct o. cbn in *.
          eapply le_max_pred in HFRL. extlia. cbn in *. extlia.
        * rewrite int_and_boolToValue. rewrite valueToBool_correct. rewrite HEVAL. now rewrite truthy_dflt. 
        * cbn. inv HMATCH. exploit mk_ctrl_correct; eauto; simplify. rewrite H.
          econstructor. eapply exec_expr_store_2; eauto; try extlia.
          destruct (rs' !! r0) eqn:?; crush. destruct (rs' !! r1) eqn:?; crush. replace Archi.ptr64 with false in HADD by auto. destr. inv HADD.
          unfold reg_stack_based_pointers in *. unfold stack_based in *. pose proof (RSBP r0). rewrite Heqv in H5.
          now subst.
      + inv HMATCH; econstructor; eauto.
        * inv MARR. destruct H as (HARR1 & HARR2 & HARR3 & HARR4). econstructor.
          repeat split.
          -- erewrite arr_assocmap_set_gss by eassumption. eauto.
          -- now rewrite <- array_set_len.
          -- now rewrite <- array_set_len.
          -- intros * HBOUND. rewrite <- array_set_len in HBOUND. pose proof HBOUND as HBOUND'. learn HBOUND'. apply HARR4 in HBOUND. 
             unfold Mem.loadv, Mem.storev in *. move MEMLOAD after HBOUND. repeat destr.
             destruct (rs' !! r0) eqn:?; crush; destruct (rs' !! r1) eqn:HXX; crush. try discriminate. replace Archi.ptr64 with false in Heqv0 by auto.
             inv Heqv0. inv HADD. inv Heqv. 
             exploit stack_correct_transl; eauto; intros (STK1 & STK2 & STK3).
             destruct (Z.eq_dec ptr (Int.unsigned (Int.divu (ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.add (Int.mul i2 (Int.repr z)) (Int.repr z0))))) (ZToValue 4)))); subst.
             ++ exploit Mem.load_store_same; eauto; intros.
                pose proof (ptrofs_mod_4 _ _ _ _ H3) as HY.
                pose proof (ptrofs_div_4 _ HY) as HYY.
                assert (b = sp0) by (eapply equiv_stack_pointer_reg_stack_based; eauto); subst.
                unfold valueToNat. rewrite get_mem_set_array_gss; try rewrite Ptrofs.add_zero_l in *.
                ** rewrite HYY.
                   subst. rewrite H3. cbn. destruct_match; econstructor; try solve [repeat econstructor].
                   rewrite <- Heqv. inv MASSOC. eapply H4; extlia. replace Archi.ptr64 with false by auto. rewrite <- Heqv. 
                   inv MASSOC. eapply H4; extlia.
                ** unfold valueToNat. unfold Int.divu. unfold stack_bounds in *.
                   enough ((0 <= (Int.unsigned (Int.repr (Int.unsigned (ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.add (Int.mul i2 (Int.repr z)) (Int.repr z0))))) / Int.unsigned (ZToValue 4)))) < Z.of_nat (arr_length stack))); [lia|].
                   repeat rewrite !Int.unsigned_repr; try now crush.
                   2: { eapply le_in_range; eauto; try lia; eauto with int_ptrofs. }
                   exploit storev_stack_bounds; eauto. rewrite <- HY. f_equal. apply agree32_ptrToValue.
                   intros. rewrite HARR2. rewrite Z_to_nat_max.
                   replace (Z.max (fn_stacksize f / 4) 0) with (fn_stacksize f / 4).
                   pose proof (agree32_ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.add (Int.mul i2 (Int.repr z)) (Int.repr z0))))); unfold Ptrofs.agree32 in *.
                   split. eapply Z_div_nonneg_nonneg; lia.
                   eapply div_lt_mono; lia.
                   destruct (Z.max_dec (fn_stacksize f / 4) 0). congruence.
                   rewrite e. pose proof (Z.le_max_l (fn_stacksize f / 4) 0). rewrite e in H5. 
                   pose proof (Z_div_nonneg_nonneg _ 4 STK1 ltac:(lia)). lia.
             ++ exploit Mem.load_store_other; eauto.
                2: { intros HLOAD. rewrite HLOAD. rewrite get_mem_set_array_gso; auto. unfold not; intros. eapply n. unfold valueToNat in H.
                     pose proof (Int.unsigned_range_2 (Int.divu (ptrToValue (Ptrofs.add i1 (Ptrofs.of_int (Int.add (Int.mul i2 (Int.repr z)) (Int.repr z0))))) (ZToValue 4))). unfold valueToNat in *. lia. }
                cbn. right. eapply not_eq_pointer_to_addr; eauto. enough (4 * ptr < fn_stacksize f). crush.
                apply div_lt_mono2 with (c := 4); try lia. apply ZLib.Z_mod_mult'.
                rewrite Z.mul_comm. rewrite Z_div_mult by lia. lia.
                eapply storev_mod_ok2; eauto.
         * eapply forall_stack_based. 3: { eassumption. } all: auto.
           destruct (rs' !! r0) eqn:?; try discriminate; destruct (rs' !! r1) eqn:?; try discriminate; cbn in *. replace Archi.ptr64 with false in * by auto. cbn in *.
           unfold reg_stack_based_pointers in *. pose proof RSBP as RSBP1. specialize (RSBP r0). specialize (RSBP1 r1). rewrite Heqv in RSBP. rewrite Heqv0 in RSBP1.  now cbn in RSBP.
         * destruct (rs' !! r0) eqn:?; try discriminate; destruct (rs' !! r1) eqn:?; try discriminate. cbn in *. replace Archi.ptr64 with false in * by auto. unfold Ptrofs.add in MEMLOAD. cbn in *.
           eapply forall_stack_bounds; cbn; try eassumption. rewrite Ptrofs.add_zero_l.
           enough (sp' = b); subst. eassumption. eapply equiv_stack_pointer_reg_stack_based; eauto.
      + auto.
    - inv HSTEP. rename H4 into HADDR, H12 into MEMLOAD, H13 into HTRUTHY'. clear HTRUTHY'.
      2: { inv H3; cbn in *. inv HTRUTHY. congruence. }
      unfold Op.eval_addressing in HADDR. replace Archi.ptr64 with false in HADDR by auto; cbn in *. inv HADDR.
      exploit storev_exists_ptr; eauto. intros (sp0 & v' & HADD).
      exists asr, (arr_assocmap_set m_.(DHTL.mod_stk) (valueToNat (Int.divu (ptrToValue v') (ZToValue 4))) (find_assocmap 32 (reg_enc r) asr) asa).
      split; [|split].
      + repeat (econstructor; try eassumption).
        * eapply pred_expr_correct; intros. inv HMATCH. inv MASSOC. eapply H1; eauto. extlia.
        * eapply pred_expr_correct; intros. inv HMATCH. inv MASSOC. eapply H1; eauto. destruct o. cbn in *.
          eapply le_max_pred in HFRL. extlia. cbn in *. extlia.
        * rewrite int_and_boolToValue. rewrite valueToBool_correct. rewrite HEVAL. now rewrite truthy_dflt. 
        * cbn. inv HMATCH. exploit mk_ctrl_correct; eauto; simplify. rewrite H.
          econstructor. replace Archi.ptr64 with false in * by auto. inv HADD. 
          unfold ZToValue. enough ((Int.divu (ptrToValue (Ptrofs.add (Ptrofs.repr 0) i)) (Int.repr 4)) = (Int.repr (Ptrofs.unsigned i / 4))).
          rewrite H2. econstructor. rewrite Ptrofs.add_zero_l. unfold Int.divu, ptrToValue.
          replace (Int.unsigned (Int.repr 4)) with 4 by auto. repeat f_equal.
          symmetry; apply Ptrofs.agree32_to_int; auto.
      + inv HMATCH; econstructor; eauto.
        * inv MARR. destruct H as (HARR1 & HARR2 & HARR3 & HARR4). econstructor.
          repeat split.
          -- erewrite arr_assocmap_set_gss by eassumption. eauto.
          -- now rewrite <- array_set_len.
          -- now rewrite <- array_set_len.
          -- intros * HBOUND. rewrite <- array_set_len in HBOUND. pose proof HBOUND as HBOUND'. learn HBOUND'. apply HARR4 in HBOUND. 
             unfold Mem.loadv, Mem.storev in *. move MEMLOAD after HBOUND. repeat destr.
             replace Archi.ptr64 with false in Heqv0 by auto.
             inv Heqv0. inv HADD. inv Heqv. 
             exploit stack_correct_transl; eauto; intros (STK1 & STK2 & STK3).
             destruct (Z.eq_dec ptr (Int.unsigned (Int.divu (ptrToValue v') (ZToValue 4)))); subst.
             ++ exploit Mem.load_store_same; eauto; intros.
                pose proof (ptrofs_mod_4 _ _ _ _ H0) as HY.
                pose proof (ptrofs_div_4 _ HY) as HYY.
                inv Heqo0.
                rewrite get_mem_set_array_gss; try rewrite Ptrofs.add_zero_l in *.
                ** rewrite Ptrofs.add_zero_l. rewrite HYY.
                   subst. rewrite H0. cbn. destruct_match; econstructor; try solve [repeat econstructor].
                   rewrite <- Heqv. inv MASSOC. eapply H1; extlia. replace Archi.ptr64 with false by auto. rewrite <- Heqv. 
                   inv MASSOC. eapply H1; extlia.
                ** unfold valueToNat. unfold Int.divu. unfold stack_bounds in *.
                   enough ((0 <= (Int.unsigned (Int.repr (Int.unsigned (ptrToValue i) / Int.unsigned (ZToValue 4)))) < Z.of_nat (arr_length stack))); [lia|].
                   repeat rewrite !Int.unsigned_repr; try now crush.
                   2: { eapply le_in_range; eauto; try lia; eauto with int_ptrofs. }
                   exploit storev_stack_bounds; eauto. rewrite <- HY. f_equal. apply agree32_ptrToValue.
                   intros. rewrite HARR2. rewrite Z_to_nat_max.
                   replace (Z.max (fn_stacksize f / 4) 0) with (fn_stacksize f / 4).
                   pose proof (agree32_ptrToValue i); unfold Ptrofs.agree32 in *.
                   split. eapply Z_div_nonneg_nonneg; lia.
                   eapply div_lt_mono; lia.
                   destruct (Z.max_dec (fn_stacksize f / 4) 0). congruence.
                   rewrite e. pose proof (Z.le_max_l (fn_stacksize f / 4) 0). rewrite e in H2. 
                   pose proof (Z_div_nonneg_nonneg _ 4 STK1 ltac:(lia)). lia.
             ++ exploit Mem.load_store_other; eauto.
                2: { intros HLOAD. rewrite HLOAD. rewrite get_mem_set_array_gso; auto. unfold not; intros. eapply n. unfold valueToNat in H.
                     pose proof (Int.unsigned_range_2 (Int.divu (ptrToValue v') (ZToValue 4))). unfold valueToNat in *. lia. }
                cbn. right. eapply not_eq_pointer_to_addr; eauto. enough (4 * ptr < fn_stacksize f). crush.
                apply div_lt_mono2 with (c := 4); try lia. apply ZLib.Z_mod_mult'.
                rewrite Z.mul_comm. rewrite Z_div_mult by lia. lia.
                eapply storev_mod_ok2; eauto.
         * eapply forall_stack_based. 3: { eassumption. } all: auto.
           replace Archi.ptr64 with false in * by auto. now cbn in *.
         * replace Archi.ptr64 with false in * by auto. unfold Ptrofs.add in MEMLOAD. cbn in *.
           eapply forall_stack_bounds; cbn; try eassumption. rewrite Ptrofs.add_zero_l. eassumption.
      + auto.
  Qed.

  Lemma transl_setpred_correct : 
    forall c l e b m_ asa asr asa0 asr0 next_p s f sp pc rs' pr m' s' o p a stmnt
      (Heqr : translate_condition c l = OK e)
      (HSTMNT : stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa))
      (HEVAL : eval_predf pr next_p = true)
      (HMATCH : match_states (GibleSubPar.State s f sp pc rs' pr m') (DHTL.State s' m_ pc asr asa))
      (HSTEP : step_instr ge sp (Iexec {| is_rs := rs'; is_ps := pr; is_mem := m' |}) (RBsetpred o c l p)
                (Iexec {| is_rs := rs'; is_ps := Registers.Regmap.set p b pr; is_mem := m' |}))
      (HFRL1 : Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses (RBsetpred o c l p)))
      (HPLE : Ple (max_predicate next_p) (max_pred_function f))
      (HREGMAX : Ple (max_reg_instr a (RBsetpred o c l p)) (max_reg_function f))
      (H2 : Op.eval_condition c (List.map (fun r : positive => rs' !! r) l) m' = Some b)
      (H11 : truthy pr o)
      (HPREDIN: ~ PredIn p next_p),
      exists (asr' : AssocMap.t value) (asa' : AssocMap.t arr),
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)
          (Vseq stmnt (translate_predicate Vblock (Some (Pand next_p (dfltp o))) (Vvar (pred_enc p)) e)) (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') /\
        match_states (GibleSubPar.State s f sp pc rs' (Registers.Regmap.set p b pr) m') (DHTL.State s' m_ pc asr' asa') /\ eval_predf (Registers.Regmap.set p b pr) next_p = true.
  Proof.
    intros. exploit eval_cond_correct; eauto. intros. cbn in *. pose proof (fold_left_max l v a ltac:(tauto)).
    extlia. intros. do 2 eexists.
    split; [|split].
    - econstructor; eauto. inv HMATCH. eapply transl_predicate_correct2_true; eauto. cbn. 
      destruct o; cbn in *. inv HFRL1. eapply le_max_pred in H4. extlia. extlia.
      rewrite eval_predf_Pand. rewrite truthy_dflt. rewrite HEVAL. auto. auto.
    - inv HMATCH; econstructor; eauto. inv MASSOC; econstructor; eauto. 
      intros. rewrite assocmap_gso by eauto using pred_enc_reg_enc_ne. eauto.
      intros. destruct (peq r p); subst. rewrite PMap.gss. now rewrite assocmap_gss.
      rewrite PMap.gso by auto. rewrite assocmap_gso; eauto. eauto using pred_enc_inj.
      unfold state_st_wf. rewrite AssocMap.gso; eauto. exploit mk_ctrl_correct; eauto; simplify. 
      destruct o; inv HFRL1; eapply ple_pred_max_resource_function in H7; extlia.
      exploit mk_ctrl_correct; eauto; simplify. pose proof (mod_ordering_wf m_). unfold module_ordering in H4. 
      inv CONST. econstructor; rewrite AssocMap.gso; auto;
      destruct o; inv HFRL1; eapply ple_pred_max_resource_function in H10; extlia.
    - rewrite eval_predf_not_PredIn; auto.
  Qed.

  Opaque deep_simplify.

  Lemma stmnt_run_store_patch :
    forall m_ asr0 p r e asa0 stmnt asa' asr' s f sp pc rs' pr' m s' asr asa,
    stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)
          (Vseq stmnt (Vcond (pred_expr p) (Vblock e (Vvar (reg_enc r))) Vskip))
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') ->
    match_states (GibleSubPar.State s f sp pc rs' pr' m) (DHTL.State s' m_ pc asr asa) ->
    stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
             (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
    Ple (max_predicate p) (max_pred_function f) ->
    stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)
      (Vseq stmnt (translate_predicate_cond' (Some p) (Vblock e (Vvar (reg_enc r)))))
      (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa').
  Proof.
    intros. inv H. exploit stmnt_runp_determinate. eapply H1. eapply H8. simplify.
    inv H11; cbn in *.
    - inv H0. inv MASSOC. exploit pred_expr_correct. intros. eapply H0. instantiate (1 := p) in H3.
      extlia. intros.
      exploit expr_runp_determinate. eapply H9. eapply H3. intros.
      rewrite <- H4 in H13. rewrite valueToBool_correct in H13.
      econstructor; eauto. destruct_match. unfold sat_pred_simple in Heqo.
      repeat (destruct_match; try discriminate; []). inv Heqo.
      econstructor; eauto. rewrite valueToBool_correct. auto.
      unfold sat_pred_simple in *. repeat (destruct_match; try discriminate).
      eauto.
    - inv H0. inv MASSOC. exploit pred_expr_correct. intros. eapply H0. instantiate (1 := p) in H3.
      extlia. intros.
      exploit expr_runp_determinate. eapply H9. eapply H3. intros.
      rewrite <- H4 in H13. rewrite valueToBool_correct in H13.
      econstructor; eauto. destruct_match. unfold sat_pred_simple in Heqo.
      repeat (destruct_match; try discriminate; []). inv Heqo.
      eapply stmnt_runp_Vcond_false; eauto.
      rewrite valueToBool_correct. eauto.
      unfold sat_pred_simple in Heqo. 
      repeat (destruct_match; try discriminate).
      unfold eval_predf in *.
      clear Heqs0. specialize (e0 (fun x : Sat.var => pr' !! x)).
      rewrite negate_correct in e0.
      rewrite deep_simplify_correct in e0. rewrite H13 in e0. cbn in *. discriminate.
  Qed.

  Opaque translate_predicate_cond'.
  Lemma transl_step_state_correct_single_instr :
    forall s f sp pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n i a,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) i = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) i
             (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses i) ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      Ple (max_reg_instr a i) (max_reg_function f) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc rs' pr' m') (DHTL.State s' m_ pc asr' asa')
        /\ eval_predf pr' next_p = true
        /\ Ple (max_predicate next_p) (max_pred_function f).
  Proof.
    intros * HTRANSF HSTMNT HEVAL HSTEP HMATCH HFRL1 HPLE HREGMAX.
    unfold transf_instr, Errors.bind in HTRANSF. 
    destruct_match; repeat destr; subst; inv HTRANSF.
    - (* RBnop *) inv HSTEP. exists asr, asa; auto. inv H3.
    - (* RBop  *) inversion HSTEP; subst. 
      + exploit transl_iop_correct; eauto. cbn. rewrite Heqr0. cbn. eauto.
        cbn in *. eapply Forall_forall; intros.
        assert (Ple x (fold_left Pos.max l (Pos.max r a))) by (eapply fold_left_max; tauto); extlia.
        assert (Ple r (fold_left Pos.max l (Pos.max r a))) by (eapply fold_left_max; extlia).
        intros (asr'' & HSTMNT' & HMATCH'). cbn in *. extlia.
        exists asr'', asa. split; eauto.
      + inv H3; cbn in *. 
        assert (eval_predf pr' (Pand next_p p) = false).
        { rewrite eval_predf_Pand. rewrite H0; auto with bool. }
        assert (Ple (max_predicate (Pand next_p p)) (max_pred_function f)).
        { cbn. eapply le_max_pred in HFRL1. extlia. }
        inv HMATCH. exploit transl_predicate_correct2; eauto.
        intros (asr'' & HSTMNT' & HASR1 & HASR2).
        exists asr'', asa. split; [|split]; auto. econstructor; eauto.
        eapply unchanged_implies_match.
        split; [|split]; eauto. econstructor; eauto.
    - (* RBload *) inversion HSTEP; subst.
      + exploit transl_load_correct; eauto. intros (asr' & asa' & HS1 & HS2 & HS3). 
        exists asr', asa'. eauto.
      + inv H3; cbn in *. 
        assert (eval_predf pr' (Pand next_p p) = false).
        { rewrite eval_predf_Pand. rewrite H0; auto with bool. }
        assert (Ple (max_predicate (Pand next_p p)) (max_pred_function f)).
        { cbn. eapply le_max_pred in HFRL1. extlia. }
        inv HMATCH. exploit transl_predicate_correct2; eauto.
        intros (asr'' & HSTMNT' & HASR1 & HASR2).
        exists asr'', asa. split; [|split]; auto. econstructor; eauto.
        eapply unchanged_implies_match.
        split; [|split]; eauto. econstructor; eauto.
    - (* RBstore *) inversion HSTEP; subst.
      + exploit transl_store_correct; eauto. intros (asr' & asa' & HS1 & HS2 & HS3).
        exists asr', asa'. split. eapply stmnt_run_store_patch. 3: { eapply HSTMNT. } eauto. eauto. 
        cbn in *. destruct o; cbn. eapply le_max_pred in HFRL1. extlia. extlia. eauto.
      + inv H3; cbn in *. 
        assert (eval_predf pr' (Pand next_p p) = false).
        { rewrite eval_predf_Pand. rewrite H0; auto with bool. }
        assert (Ple (max_predicate (Pand next_p p)) (max_pred_function f)).
        { cbn. eapply le_max_pred in HFRL1. extlia. }
        inv HMATCH. exploit transl_predicate_cond_correct_arr2'; eauto.
        intros.
        exists asr, asa. split; [|split]; auto. econstructor; eauto.
        eapply unchanged_implies_match.
        split; [|split]; eauto. econstructor; eauto.
    - (* RBsetpred *)
      inversion HSTEP; subst.
      + exploit transl_setpred_correct; eauto. unfold assert_ in *. destr.
        pose proof (negb_prop_elim (predin peq p next_p)). unfold not in *; intros.
        eapply H. unfold Is_true. now rewrite Heqb0.
        unfold Is_true. eapply predin_PredIn in H0. now rewrite H0.
        intros (asr' & asa' & HS1 & HS2 & HS3). 
        exists asr', asa'. eauto.
      + inv H3; cbn in *.
        assert (eval_predf pr' (Pand next_p p0) = false).
        { rewrite eval_predf_Pand. rewrite H0; auto with bool. }
        assert (Ple (max_predicate (Pand next_p p0)) (max_pred_function f)).
        { cbn. inv HFRL1. eapply le_max_pred in H4. extlia. }
        inv HMATCH. exploit transl_predicate_correct2; eauto.
        intros (asr'' & HSTMNT' & HASR1 & HASR2).
        exists asr'', asa. split; [|split]; auto. econstructor; eauto.
        eapply unchanged_implies_match.
        split; [|split]; eauto. econstructor; eauto.
    - (* RBexit *) inv HSTEP. 
        inv H3; cbn -[eval_predf] in *.
        assert (eval_predf pr' (Pand curr_p p) = false).
        { rewrite eval_predf_Pand. rewrite H0; auto with bool. }
        assert (Ple (max_predicate (Pand curr_p p)) (max_pred_function f)).
        { cbn. eapply le_max_pred in HFRL1. extlia. }
        unfold translate_cfi, Errors.bind in *.
        inv HMATCH. repeat (destin Heqr0; try discriminate); subst.
        + unfold state_cond in *. inv Heqr0.
          exploit transl_predicate_correct2; eauto.
          intros (asr' & HSTMNT' & HEQUIV & HFORALL).
          exists asr', asa. split; [|split].
          econstructor; eauto.
          eapply unchanged_implies_match; eauto.
          unfold unchanged. split; [|split]; eauto. econstructor; eauto.
          rewrite eval_predf_Pand. rewrite HEVAL. rewrite eval_predf_negate. split. now rewrite H0.
          eapply le_max_pred in HFRL1. rewrite max_predicate_negate. extlia.
        + unfold state_cond, state_goto in *. inv Heqr0.
          exploit transl_predicate_correct2; eauto.
          intros (asr' & HSTMNT' & HEQUIV & HFORALL).
          assert (X': unchanged asr asa asr' asa).
          { unfold unchanged; split; [|split]; eauto. }
          pose proof X' as Y1.
          eapply unchanged_implies_match in X'; eauto. 2: { econstructor; eauto. }
          inversion X'; subst.
          exploit transl_predicate_correct2; eauto.
          intros (asr'' & HSTMNT'' & HEQUIV' & HFORALL').
          assert (X'': unchanged asr' asa asr'' asa).
          { unfold unchanged; split; [|split]; eauto. }
          pose proof X'' as Y2.
          eapply unchanged_implies_match in X''; eauto.
          inversion X''; subst.
          exploit transl_predicate_correct2; eauto.
          intros (asr''' & HSTMNT''' & HEQUIV'' & HFORALL'').
          assert (X''': unchanged asr'' asa asr''' asa).
          { unfold unchanged; split; [|split]; eauto. }
          pose proof X''' as Y3.
          eapply unchanged_match_assocmaps in X'''; eauto.
          exists asr''', asa. split; [|split].
          econstructor; eauto.
          econstructor. econstructor. eauto. eauto. eauto. 
          eapply unchanged_implies_match; eauto.
          rewrite eval_predf_Pand. rewrite eval_predf_negate.
          rewrite HEVAL. split. now rewrite H0.
          eapply le_max_pred in HFRL1. rewrite max_predicate_negate. extlia.
        + unfold state_cond, state_goto in *. inv Heqr0.
          exploit transl_predicate_correct2; eauto.
          intros (asr' & HSTMNT' & HEQUIV & HFORALL).
          assert (X': unchanged asr asa asr' asa).
          { unfold unchanged; split; [|split]; eauto. }
          pose proof X' as Y1.
          eapply unchanged_implies_match in X'; eauto. 2: { econstructor; eauto. }
          inversion X'; subst.
          exploit transl_predicate_correct2; eauto.
          intros (asr'' & HSTMNT'' & HEQUIV' & HFORALL').
          assert (X'': unchanged asr' asa asr'' asa).
          { unfold unchanged; split; [|split]; eauto. }
          pose proof X'' as Y2.
          eapply unchanged_implies_match in X''; eauto.
          inversion X''; subst.
          exploit transl_predicate_correct2; eauto.
          intros (asr''' & HSTMNT''' & HEQUIV'' & HFORALL'').
          assert (X''': unchanged asr'' asa asr''' asa).
          { unfold unchanged; split; [|split]; eauto. }
          pose proof X''' as Y3.
          eapply unchanged_match_assocmaps in X'''; eauto.
          exists asr''', asa. split; [|split].
          econstructor; eauto.
          econstructor. econstructor. eauto. eauto. eauto. 
          eapply unchanged_implies_match; eauto.
          rewrite eval_predf_Pand. rewrite eval_predf_negate.
          rewrite HEVAL. split. now rewrite H0.
          eapply le_max_pred in HFRL1. rewrite max_predicate_negate. extlia.
        + unfold state_cond, state_goto in *. inv Heqr0.
          exploit transl_predicate_correct2; eauto.
          intros (asr' & HSTMNT' & HEQUIV & HFORALL).
          exists asr', asa. split; [|split].
          econstructor; eauto.
          eapply unchanged_implies_match; eauto.
          unfold unchanged. split; [|split]; eauto. econstructor; eauto.
          rewrite eval_predf_Pand. rewrite HEVAL. rewrite eval_predf_negate. split. now rewrite H0.
          eapply le_max_pred in HFRL1. rewrite max_predicate_negate. extlia.
          Unshelve. auto.
  Qed.

  Lemma OK_inj : 
    forall A (a b: A), OK a = OK b -> a = b.
  Proof. now inversion 1. Qed.

  Lemma transl_step_state_correct_single_instr_term :
    forall s f sp pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n i cf pc' a,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) i = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) i
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.State s f sp pc' rs' pr' m') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses i) ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      Ple (max_reg_instr a i) (max_reg_function f) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc' rs' pr' m') (DHTL.State s' m_ pc' asr' asa')
        /\ eval_predf pr' next_p = false.
  Proof. 
    intros * HTRANS HSTMNT HEVAL HSTEP HSTEPCF HMATCH HPLE1 HPLE2 HPLE3.
    inv HSTEP. inv HSTEPCF; cbn in *; unfold Errors.bind in *; repeat destruct_match; try discriminate; subst.
    - inv Heqr1. apply OK_inj in Heqr0. apply OK_inj in HTRANS. inv HTRANS. unfold state_cond.
      exploit eval_cond_correct; eauto. intros. pose proof (fold_left_max args v a ltac:(tauto)). extlia.
      intros. 
      eexists. exists asa. split; [|split].
      econstructor; eauto. eapply transl_predicate_correct2_true; eauto.
      4: { econstructor. eauto. econstructor. now rewrite valueToBool_correct. }
      + instantiate (1 := max_pred_function f). cbn. eapply le_max_pred in HPLE1. extlia.
      + inv HMATCH. eauto.
      + rewrite eval_predf_Pand. rewrite HEVAL. now rewrite truthy_dflt.
      + inv HMATCH. econstructor; eauto.
        * inv MASSOC. econstructor; intros. pose proof (ple_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
          pose proof (ple_pred_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
        * unfold state_st_wf in *. exploit mk_ctrl_correct; eauto; intros. destruct H1. rewrite <- H1. cbn. now rewrite AssocMap.gss.
        * inv CONST. exploit mk_ctrl_correct; eauto; intros. destruct H4. pose proof (mod_ordering_wf m_). unfold module_ordering in H6.
          econstructor. cbn in *. now rewrite AssocMap.gso by lia. cbn in *. now rewrite AssocMap.gso by lia.
      + rewrite eval_predf_Pand. rewrite HEVAL. rewrite eval_predf_negate. inv H3. rewrite H2. auto.
    - inv Heqr1. apply OK_inj in Heqr0. apply OK_inj in HTRANS. inv HTRANS. unfold state_cond.
      exploit eval_cond_correct; eauto. intros. pose proof (fold_left_max args v a ltac:(tauto)). extlia.
      intros. 
      eexists. exists asa. split; [|split].
      econstructor; eauto. eapply transl_predicate_correct2_true; eauto.
      4: { econstructor. eauto. econstructor. now rewrite valueToBool_correct. }
      + instantiate (1 := max_pred_function f). cbn. extlia.
      + inv HMATCH. eauto.
      + rewrite eval_predf_Pand. rewrite HEVAL. now rewrite truthy_dflt.
      + inv HMATCH. econstructor; eauto.
        * inv MASSOC. econstructor; intros. pose proof (ple_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
          pose proof (ple_pred_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
        * unfold state_st_wf in *. exploit mk_ctrl_correct; eauto; intros. destruct H1. rewrite <- H1. cbn. now rewrite AssocMap.gss.
        * inv CONST. exploit mk_ctrl_correct; eauto; intros. destruct H4. pose proof (mod_ordering_wf m_). unfold module_ordering in H6.
          econstructor. cbn in *. now rewrite AssocMap.gso by lia. cbn in *. now rewrite AssocMap.gso by lia.
      + rewrite eval_predf_Pand. rewrite HEVAL. cbn. auto.
    - inv Heqr1. apply OK_inj in Heqr0. apply OK_inj in HTRANS. inv HTRANS. unfold state_cond.
      exploit eval_cond_correct; eauto. intros. pose proof (fold_left_max args v a ltac:(tauto)). extlia.
      intros. 
      eexists. exists asa. split; [|split].
      econstructor; eauto. eapply transl_predicate_correct2_true; eauto.
      4: { eapply erun_Vternary_false. eauto. econstructor. now rewrite valueToBool_correct. }
      + instantiate (1 := max_pred_function f). cbn. eapply le_max_pred in HPLE1. extlia.
      + inv HMATCH. eauto.
      + rewrite eval_predf_Pand. rewrite HEVAL. now rewrite truthy_dflt.
      + inv HMATCH. econstructor; eauto.
        * inv MASSOC. econstructor; intros. pose proof (ple_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
          pose proof (ple_pred_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
        * unfold state_st_wf in *. exploit mk_ctrl_correct; eauto; intros. destruct H1. rewrite <- H1. cbn. now rewrite AssocMap.gss.
        * inv CONST. exploit mk_ctrl_correct; eauto; intros. destruct H4. pose proof (mod_ordering_wf m_). unfold module_ordering in H6.
          econstructor. cbn in *. now rewrite AssocMap.gso by lia. cbn in *. now rewrite AssocMap.gso by lia.
      + rewrite eval_predf_Pand. rewrite HEVAL. rewrite eval_predf_negate. inv H3. rewrite H2. auto.
    - inv Heqr1. apply OK_inj in Heqr0. apply OK_inj in HTRANS. inv HTRANS. unfold state_cond.
      exploit eval_cond_correct; eauto. intros. pose proof (fold_left_max args v a ltac:(tauto)). extlia.
      intros. 
      eexists. exists asa. split; [|split].
      econstructor; eauto. eapply transl_predicate_correct2_true; eauto.
      4: { eapply erun_Vternary_false. eauto. econstructor. now rewrite valueToBool_correct. }
      + instantiate (1 := max_pred_function f). cbn. extlia.
      + inv HMATCH. eauto.
      + rewrite eval_predf_Pand. rewrite HEVAL. now rewrite truthy_dflt.
      + inv HMATCH. econstructor; eauto.
        * inv MASSOC. econstructor; intros. pose proof (ple_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
          pose proof (ple_pred_max_resource_function _ _ H4).
          rewrite assocmap_gso by extlia. eauto.
        * unfold state_st_wf in *. exploit mk_ctrl_correct; eauto; intros. destruct H1. rewrite <- H1. cbn. now rewrite AssocMap.gss.
        * inv CONST. exploit mk_ctrl_correct; eauto; intros. destruct H4. pose proof (mod_ordering_wf m_). unfold module_ordering in H6.
          econstructor. cbn in *. now rewrite AssocMap.gso by lia. cbn in *. now rewrite AssocMap.gso by lia.
      + rewrite eval_predf_Pand. rewrite HEVAL. cbn. auto.
    - unfold state_goto in *. inv HTRANS.
      eexists. exists asa. split; [|split].
      econstructor; eauto. eapply transl_predicate_correct2_true; eauto.
      4: { econstructor. }
      + instantiate (1 := max_pred_function f). cbn. eapply le_max_pred in HPLE1. extlia.
      + inv HMATCH. eauto.
      + rewrite eval_predf_Pand. rewrite HEVAL. inv H3. rewrite H0. auto.
      + inv HMATCH. econstructor; eauto.
        * inv MASSOC. econstructor; intros. pose proof (ple_max_resource_function _ _ H1).
          rewrite assocmap_gso by extlia. eauto.
          pose proof (ple_pred_max_resource_function _ _ H1).
          rewrite assocmap_gso by extlia. eauto.
        * unfold state_st_wf in *. exploit mk_ctrl_correct; eauto; intros. destruct H. rewrite <- H. cbn. now rewrite AssocMap.gss.
        * inv CONST. exploit mk_ctrl_correct; eauto; intros. destruct H1. pose proof (mod_ordering_wf m_). unfold module_ordering in H4.
          econstructor. cbn in *. now rewrite AssocMap.gso by lia. cbn in *. now rewrite AssocMap.gso by lia.
      + rewrite eval_predf_Pand. rewrite HEVAL. rewrite eval_predf_negate. inv H3. rewrite H0. auto.
       - unfold state_goto in *. inv HTRANS.
      eexists. exists asa. split; [|split].
      econstructor; eauto. eapply transl_predicate_correct2_true; eauto.
      4: { econstructor. }
      + instantiate (1 := max_pred_function f). cbn. extlia.
      + inv HMATCH. eauto.
      + rewrite eval_predf_Pand. rewrite HEVAL. inv H3. cbn. auto.
      + inv HMATCH. econstructor; eauto.
        * inv MASSOC. econstructor; intros. pose proof (ple_max_resource_function _ _ H1).
          rewrite assocmap_gso by extlia. eauto.
          pose proof (ple_pred_max_resource_function _ _ H1).
          rewrite assocmap_gso by extlia. eauto.
        * unfold state_st_wf in *. exploit mk_ctrl_correct; eauto; intros. destruct H. rewrite <- H. cbn. now rewrite AssocMap.gss.
        * inv CONST. exploit mk_ctrl_correct; eauto; intros. destruct H1. pose proof (mod_ordering_wf m_). unfold module_ordering in H4.
          econstructor. cbn in *. now rewrite AssocMap.gso by lia. cbn in *. now rewrite AssocMap.gso by lia.
      + rewrite eval_predf_Pand. rewrite HEVAL. cbn. auto.
  Qed.

  Lemma transl_step_state_correct_single_instr_term_return :
    forall s f sp pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n i cf v m'' a,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) i = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) i
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.Returnstate s v m'') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses i) ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      Ple (max_reg_instr a i) (max_reg_function f) ->
      exists retval,
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc (AssocMap.set m_.(DHTL.mod_st) (posToValue n) 
            (AssocMap.set (m_.(DHTL.mod_return)) retval (AssocMap.set (m_.(DHTL.mod_finish)) (ZToValue 1) asr)))) 
          (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa)
        /\ val_value_lessdef v retval
        /\ eval_predf pr' next_p = false.
  Proof. 
    intros * HTRANS HSTMNT HEVAL HSTEP HSTEPCF HMATCH HPLE1 HPLE2 HPLE3.
    inv HSTEP. inv HSTEPCF; cbn in *; unfold Errors.bind in *; repeat destruct_match; try discriminate; subst.
    - assert (Hple4: Ple (max_predicate (Pand curr_p p0)) (max_pred_function f)).
      { cbn. eapply le_max_pred in HPLE1. extlia. }
      assert (HEVAL2: eval_predf pr' (Pand curr_p p0) = true).
      { rewrite eval_predf_Pand. inv H3. rewrite H0. rewrite HEVAL. auto. }
      inv HMATCH. 
      unfold state_goto in *. inv HTRANS. eexists; split; [|split].
      econstructor; eauto. repeat (econstructor; eauto).
      eapply transl_predicate_correct2_true; eauto.
      econstructor.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. eauto.
      unfold transl_module, Errors.bind, ret in *; repeat destr. inv TF; cbn.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. cbn.
      assert (HPLE5: Ple r (max_reg_function f)) by extlia.
      eapply ple_max_resource_function in HPLE5. rewrite assocmap_gso by extlia.
      inv MASSOC. eapply H; try extlia.
      rewrite eval_predf_Pand. rewrite eval_predf_negate. rewrite HEVAL. inv H3.
      now rewrite H0.
    - assert (Hple4: Ple (max_predicate (Pand curr_p Ptrue)) (max_pred_function f)).
      { cbn. extlia. }
      assert (HEVAL2: eval_predf pr' (Pand curr_p Ptrue) = true).
      { rewrite eval_predf_Pand. rewrite HEVAL. auto. }
      inv HMATCH. 
      unfold state_goto in *. inv HTRANS. eexists; split; [|split].
      econstructor; eauto. repeat (econstructor; eauto).
      eapply transl_predicate_correct2_true; eauto.
      econstructor.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. eauto.
      unfold transl_module, Errors.bind, ret in *; repeat destr. inv TF; cbn.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. cbn.
      assert (HPLE5: Ple r (max_reg_function f)) by extlia.
      eapply ple_max_resource_function in HPLE5. rewrite assocmap_gso by extlia.
      inv MASSOC. eapply H; try extlia.
      rewrite eval_predf_Pand. auto with bool.
    - assert (Hple4: Ple (max_predicate (Pand curr_p p0)) (max_pred_function f)).
      { cbn. eapply le_max_pred in HPLE1. extlia. }
      assert (HEVAL2: eval_predf pr' (Pand curr_p p0) = true).
      { rewrite eval_predf_Pand. inv H3. rewrite H0. rewrite HEVAL. auto. }
      inv HMATCH. 
      unfold state_goto in *. inv HTRANS. eexists; split; [|split].
      econstructor; eauto. repeat (econstructor; eauto).
      eapply transl_predicate_correct2_true; eauto.
      econstructor.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. eauto.
      unfold transl_module, Errors.bind, ret in *; repeat destr. inv TF; cbn.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. cbn. constructor.
      rewrite eval_predf_Pand. rewrite eval_predf_negate. rewrite HEVAL. inv H3.
      now rewrite H0.
    - assert (Hple4: Ple (max_predicate (Pand curr_p Ptrue)) (max_pred_function f)).
      { cbn. extlia. }
      assert (HEVAL2: eval_predf pr' (Pand curr_p Ptrue) = true).
      { rewrite eval_predf_Pand. rewrite HEVAL. auto. }
      inv HMATCH. 
      unfold state_goto in *. inv HTRANS. eexists; split; [|split].
      econstructor; eauto. repeat (econstructor; eauto).
      eapply transl_predicate_correct2_true; eauto.
      econstructor.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. eauto.
      unfold transl_module, Errors.bind, ret in *; repeat destr. inv TF; cbn.
      eapply transl_predicate_correct2_true; eauto.
      eapply regs_lessdef_add_greater; eauto. extlia.
      eapply regs_lessdef_add_greater; eauto. extlia.
      econstructor. cbn.
      constructor.
      rewrite eval_predf_Pand. auto with bool.
  Qed.

  Transparent translate_predicate.
  Transparent translate_predicate_cond.

  Lemma transl_step_state_correct_single_false_standard :
    forall ctrl bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n max_reg max_pred rs ps,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n ctrl (curr_p, stmnt) bb = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun x => Ple x max_pred) (pred_uses bb) ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      (forall a b c d e, bb <> RBstore a b c d e) ->
      (forall a b, bb <> RBexit a b) ->
      exists asr', stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
        (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) 
        /\ unchanged asr asa asr' asa
        /\ Ple (max_predicate next_p) max_pred 
        /\ eval_predf ps next_p = false.
  Proof.
    destruct bb; intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH HNO_RBSTORE HNO_EXIT.
    - cbn in HTRANSF. inv HTRANSF. exists asr; repeat split; eauto.
    - cbn -[translate_predicate deep_simplify] in HTRANSF; unfold Errors.bind in HTRANSF.
      destruct_match; try discriminate.
      assert (forall A a b, @OK A a = OK b -> a = b) by now inversion 1. apply H in HTRANSF.
      assert (forall A B (a b: A) (c d: B), (a, c) = (b, d) -> a = b /\ c = d) by now inversion 1. 
      apply H0 in HTRANSF. destruct HTRANSF. rewrite H1 in *. rewrite <- H2 in *.
      assert (eval_predf ps (Pand next_p (dfltp o)) = false).
      { rewrite eval_predf_Pand. subst. rewrite HEVAL. auto. }
      assert (Ple (max_predicate (Pand next_p (dfltp o))) max_pred).
      { cbn. cbn in HFRL. destruct o; cbn; [|unfold Ple in *; lia].
        eapply le_max_pred in HFRL. unfold Ple in *; lia. }
      exploit transl_predicate_correct2; eauto. intros (asr' & HSTMNT' & FRL).
      exists asr'. repeat split; eauto.
      econstructor; eauto. simplify.
      crush. crush.
    - cbn -[translate_predicate deep_simplify] in HTRANSF; unfold Errors.bind in HTRANSF.
      destruct_match; try discriminate.
      assert (forall A a b, @OK A a = OK b -> a = b) by now inversion 1. apply H in HTRANSF.
      assert (forall A B (a b: A) (c d: B), (a, c) = (b, d) -> a = b /\ c = d) by now inversion 1. 
      apply H0 in HTRANSF. destruct HTRANSF. rewrite H1 in *. rewrite <- H2 in *.
      assert (eval_predf ps (Pand next_p (dfltp o)) = false).
      { rewrite eval_predf_Pand. subst. rewrite HEVAL. auto. }
      assert (Ple (max_predicate (Pand next_p (dfltp o))) max_pred).
      { cbn. cbn in HFRL. destruct o; cbn; [|unfold Ple in *; lia].
        eapply le_max_pred in HFRL. unfold Ple in *; lia. }
      exploit transl_predicate_correct2; eauto. intros (asr' & HSTMNT' & FRL).
      exists asr'. repeat split; eauto.
      econstructor; eauto. crush. crush.
    - exfalso; eapply HNO_RBSTORE; auto.
    - cbn -[translate_predicate deep_simplify] in HTRANSF; unfold Errors.bind in HTRANSF.
      repeat (destruct_match; try discriminate).
      assert (forall A a b, @OK A a = OK b -> a = b) by now inversion 1. apply H in HTRANSF.
      assert (forall A B (a b: A) (c d: B), (a, c) = (b, d) -> a = b /\ c = d) by now inversion 1. 
      apply H0 in HTRANSF. destruct HTRANSF. rewrite H1 in *. rewrite <- H2 in *.
      assert (eval_predf ps (Pand next_p (dfltp o)) = false).
      { rewrite eval_predf_Pand. subst. rewrite HEVAL. auto. }
      assert (Ple (max_predicate (Pand next_p (dfltp o))) max_pred).
      { cbn. cbn in HFRL. destruct o; cbn; [|unfold Ple in *; lia]. inv HFRL.
        eapply le_max_pred in H7. unfold Ple in *; lia. }
      exploit transl_predicate_correct2; eauto. intros (asr' & HSTMNT' & FRL).
      exists asr'. repeat split; eauto.
      econstructor; eauto. crush. crush.
    - exfalso; eapply HNO_EXIT; auto.
  Qed.

  Lemma transl_arr_access_exists_vari :
    forall chunk addr args stack e,
      translate_arr_access chunk addr args stack = OK e ->
      exists e', e = Vvari stack e'.
  Proof.
    destruct chunk, addr; intros; cbn in *; repeat destr; try discriminate; inv H; eauto.
  Qed.

  Opaque translate_predicate.
  (* Lemma transl_step_state_correct_single_false_standard_top_store : *)
  (*   forall f s s' pc curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps sp m p chunk addr args src, *)
  (*     (* (fn_code f) ! pc = Some bb -> *) *)
  (*     transf_instr n (mk_ctrl f) (curr_p, stmnt) (RBstore p chunk addr args src) = OK (next_p, stmnt') -> *)
  (*     stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)  *)
  (*       stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) -> *)
  (*     Forall (fun x => Ple x (max_pred_function f)) (pred_uses (RBstore p chunk addr args src)) -> *)
  (*     Ple (max_predicate curr_p) (max_pred_function f) -> *)
  (*     eval_predf ps curr_p = false -> *)
  (*     match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr asa) -> *)
  (*     exists asr' asa',  *)
  (*       stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt'  *)
  (*         (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')  *)
  (*       /\ match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr' asa') *)
  (*       /\ Ple (max_predicate next_p) (max_pred_function f) *)
  (*       /\ eval_predf ps next_p = false. *)
  (* Proof. *)
  (*   intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH.  *)
  (*   cbn -[translate_predicate_cond] in *; unfold Errors.bind in *. *)
  (*   destruct (translate_arr_access chunk addr args (Pos.succ (Pos.succ (Pos.succ (Pos.succ (max_resource_function f)))))) eqn:HT; try discriminate. *)
  (*   inv HTRANSF. exploit transl_arr_access_exists_vari; eauto. intros (e' & HVARI). *)
  (*   subst. inv HMATCH. exploit mk_ctrl_correct; eauto. intros (HCTRLST' & HCTRLSTACK' & HCTRLFIN' & HCTRLRETURN'). *)
  (*   cbn -[translate_predicate_cond] in *. rewrite HCTRLSTACK' in HT. *)
  (*   assert (X: Ple (max_predicate (Pand next_p (dfltp p))) (max_pred_function f)). *)
  (*   { unfold Ple; cbn. destruct p; cbn. apply le_max_pred in HFRL. unfold Ple in *. lia. unfold Ple in *. lia. } *)
  (*   exploit transl_predicate_cond_correct_arr2; eauto. *)
  (*   rewrite eval_predf_Pand. now rewrite HEVAL. *)
  (*   intros HSTMNT'. exists asr, asa.  *)
  (*   split; [|split; [|split]]. *)
  (*   econstructor; eauto. cbn in *. *)
  (*   econstructor; eauto. auto. auto. *)
  (* Qed. *)

  Lemma transl_step_state_correct_single_false_standard_top_store :
    forall ctrl curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n p chunk addr args src max_reg max_pred rs ps,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n ctrl (curr_p, stmnt) (RBstore p chunk addr args src) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) 
        stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun x => Ple x max_pred) (pred_uses (RBstore p chunk addr args src)) ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      exists asr', 
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) 
        /\ unchanged asr asa asr' asa
        /\ Ple (max_predicate next_p) max_pred
        /\ eval_predf ps next_p = false.
  Proof.
    intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH.
    cbn -[translate_predicate_cond] in *; unfold Errors.bind in *.
    destruct (translate_arr_access chunk addr args (ctrl_stack ctrl)) eqn:HT; try discriminate.
    inv HTRANSF. exploit transl_arr_access_exists_vari; eauto. intros (e' & HVARI).
    subst.
    cbn -[translate_predicate_cond] in *.
    assert (X: Ple (max_predicate (Pand next_p (dfltp p))) max_pred).
    { unfold Ple; cbn. destruct p; cbn. apply le_max_pred in HFRL. unfold Ple in *. lia. unfold Ple in *. lia. }
    exploit transl_predicate_cond_correct_arr2'; eauto.
    rewrite eval_predf_Pand. now rewrite HEVAL.
    intros HSTMNT'. exists asr. 
    split; [|split; [|split]].
    econstructor; eauto. cbn in *.
    econstructor; eauto. auto. auto.
  Qed.

  Lemma transl_step_state_correct_single_false_standard_top_exit :
    forall ctrl curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps p cfi max_pred max_reg,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n ctrl (curr_p, stmnt) (RBexit p cfi) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) 
        stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun x => Ple x max_pred) (pred_uses (RBexit p cfi)) ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      exists asr',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) 
        /\ unchanged asr asa asr' asa
        /\ Ple (max_predicate next_p) max_pred
        /\ eval_predf ps next_p = false.
  Proof.
    intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH. 
    cbn -[translate_predicate_cond translate_predicate] in *; unfold Errors.bind in *. 
    repeat (destin HTRANSF; try discriminate; []). inv HTRANSF.
    assert (X: Ple (max_predicate (Pand curr_p (dfltp p))) max_pred).
    { unfold Ple; cbn. destruct p; cbn. apply le_max_pred in HFRL. unfold Ple in *. lia. unfold Ple in *. lia. }
    unfold translate_cfi, Errors.bind in *.
    repeat (destin DIN0; try discriminate).
    - unfold state_cond in *. inv DIN0.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr' & HSTMNT' & HEQUIV & HFORALL).
      exists asr'. split; [|split; [|split]].
      econstructor; eauto.
      unfold unchanged. split; [|split]; eauto.
      unfold Ple in *; cbn. rewrite max_predicate_negate.
      destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia.
      rewrite eval_predf_Pand. now rewrite HEVAL.
    - unfold state_cond, state_goto in *. inv DIN0.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr' & HSTMNT' & HEQUIV & HFORALL).
      assert (X': unchanged asr asa asr' asa).
      { unfold unchanged; split; [|split]; eauto. }
      pose proof X' as Y1.
      eapply unchanged_match_assocmaps in X'; eauto.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr'' & HSTMNT'' & HEQUIV' & HFORALL').
      assert (X'': unchanged asr' asa asr'' asa).
      { unfold unchanged; split; [|split]; eauto. }
      pose proof X'' as Y2.
      eapply unchanged_match_assocmaps in X''; eauto.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr''' & HSTMNT''' & HEQUIV'' & HFORALL'').
      assert (X''': unchanged asr'' asa asr''' asa).
      { unfold unchanged; split; [|split]; eauto. }
      pose proof X''' as Y3.
      eapply unchanged_match_assocmaps in X'''; eauto.
      exists asr'''. split; [|split; [|split]].
      econstructor; eauto.
      econstructor. econstructor. eauto.
      eauto. eauto. eapply unchanged_trans; eauto. eapply unchanged_trans; eauto.
      unfold Ple in *; cbn. rewrite max_predicate_negate.
      destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia.
      rewrite eval_predf_Pand. now rewrite HEVAL.
    - unfold state_cond, state_goto in *. inv DIN0.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr' & HSTMNT' & HEQUIV & HFORALL).
      assert (X': unchanged asr asa asr' asa).
      { unfold unchanged; split; [|split]; eauto. }
      pose proof X' as Y1.
      eapply unchanged_match_assocmaps in X'; eauto.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr'' & HSTMNT'' & HEQUIV' & HFORALL').
      assert (X'': unchanged asr' asa asr'' asa).
      { unfold unchanged; split; [|split]; eauto. }
      pose proof X'' as Y2.
      eapply unchanged_match_assocmaps in X''; eauto.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr''' & HSTMNT''' & HEQUIV'' & HFORALL'').
      assert (X''': unchanged asr'' asa asr''' asa).
      { unfold unchanged; split; [|split]; eauto. }
      pose proof X''' as Y3.
      eapply unchanged_match_assocmaps in X'''; eauto.
      exists asr'''. split; [|split; [|split]].
      econstructor; eauto.
      econstructor. econstructor. eauto.
      eauto. eauto. eapply unchanged_trans; eauto. eapply unchanged_trans; eauto.
      unfold Ple in *; cbn. rewrite max_predicate_negate.
      destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia.
      rewrite eval_predf_Pand. now rewrite HEVAL.
    - unfold state_cond, state_goto in *. inv DIN0.
      exploit transl_predicate_correct2; eauto.
      rewrite eval_predf_Pand. rewrite HEVAL. eauto.
      intros (asr' & HSTMNT' & HEQUIV & HFORALL).
      exists asr'. split; [|split; [|split]].
      econstructor; eauto.
      econstructor; eauto.
      unfold Ple in *; cbn. rewrite max_predicate_negate.
      destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia.
      rewrite eval_predf_Pand. now rewrite HEVAL.
  Qed.

  (* Lemma transl_step_state_correct_single_false_standard_top_exit' : *)
  (*   forall f s s' pc curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps sp m p cfi, *)
  (*     (* (fn_code f) ! pc = Some bb -> *) *)
  (*     transf_instr n (mk_ctrl f) (curr_p, stmnt) (RBexit p cfi) = OK (next_p, stmnt') -> *)
  (*     stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)  *)
  (*       stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) -> *)
  (*     Forall (fun x => Ple x (max_pred_function f)) (pred_uses (RBexit p cfi)) -> *)
  (*     Ple (max_predicate curr_p) (max_pred_function f) -> *)
  (*     eval_predf ps curr_p = false -> *)
  (*     match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr asa) -> *)
  (*     exists asr' asa',  *)
  (*       stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt'  *)
  (*         (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')  *)
  (*       /\ match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr' asa') *)
  (*       /\ Ple (max_predicate next_p) (max_pred_function f) *)
  (*       /\ eval_predf ps next_p = false. *)
  (* Proof.  *)
  (*   intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH.  *)
  (*   cbn -[translate_predicate_cond translate_predicate] in *; unfold Errors.bind in *.  *)
  (*   repeat (destin HTRANSF; try discriminate; []). inv HTRANSF. *)
  (*   assert (X: Ple (max_predicate (Pand curr_p (dfltp p))) (max_pred_function f)). *)
  (*   { unfold Ple; cbn. destruct p; cbn. apply le_max_pred in HFRL. unfold Ple in *. lia. unfold Ple in *. lia. } *)
  (*   unfold translate_cfi, Errors.bind in *. *)
  (*   repeat (destin DIN0; try discriminate). *)
  (*   - unfold state_cond in *. inv DIN0. *)
  (*     inv HMATCH. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr' & HSTMNT' & HEQUIV & HFORALL). *)
  (*     exists asr', asa. split; [|split; [|split]]. *)
  (*     econstructor; eauto. *)
  (*     eapply unchanged_implies_match; eauto. instantiate (2:=asr). instantiate (1:=asa). *)
  (*     unfold unchanged. split; [|split]; eauto. *)
  (*     econstructor; eauto. *)
  (*     unfold Ple in *; cbn. rewrite max_predicate_negate. *)
  (*     destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia. *)
  (*     rewrite eval_predf_Pand. now rewrite HEVAL. *)
  (*   - unfold state_cond, state_goto in *. inv DIN0. *)
  (*     inv HMATCH. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr' & HSTMNT' & HEQUIV & HFORALL). *)
  (*     assert (X': unchanged asr asa asr' asa). *)
  (*     { unfold unchanged; split; [|split]; eauto. } *)
  (*     pose proof unchanged_implies_match as Y. eapply Y in X'; [|econstructor; eauto]. *)
  (*     inv X'. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr'' & HSTMNT'' & HEQUIV' & HFORALL'). *)
  (*     assert (X': unchanged asr' asa asr'' asa). *)
  (*     { unfold unchanged; split; [|split]; eauto. } *)
  (*     pose proof unchanged_implies_match as Y'. eapply Y' in X'; [|econstructor; eauto]. *)
  (*     inv X'. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr''' & HSTMNT''' & HEQUIV'' & HFORALL''). *)
  (*     assert (X': unchanged asr'' asa asr''' asa). *)
  (*     { unfold unchanged; split; [|split]; eauto. } *)
  (*     pose proof unchanged_implies_match as Y''. eapply Y'' in X'; [|econstructor; eauto]. *)
  (*     inv X'. *)
  (*     exists asr''', asa. split; [|split; [|split]]. *)
  (*     econstructor; eauto. *)
  (*     econstructor. econstructor. eauto. *)
  (*     eauto. eauto. econstructor; eauto. *)
  (*     unfold Ple in *; cbn. rewrite max_predicate_negate. *)
  (*     destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia. *)
  (*     rewrite eval_predf_Pand. now rewrite HEVAL. *)
  (*   - unfold state_cond, state_goto in *. inv DIN0. *)
  (*     inv HMATCH. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr' & HSTMNT' & HEQUIV & HFORALL). *)
  (*     assert (X': unchanged asr asa asr' asa). *)
  (*     { unfold unchanged; split; [|split]; eauto. } *)
  (*     pose proof unchanged_implies_match as Y. eapply Y in X'; [|econstructor; eauto]. *)
  (*     inv X'. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr'' & HSTMNT'' & HEQUIV' & HFORALL'). *)
  (*     assert (X': unchanged asr' asa asr'' asa). *)
  (*     { unfold unchanged; split; [|split]; eauto. } *)
  (*     pose proof unchanged_implies_match as Y'. eapply Y' in X'; [|econstructor; eauto]. *)
  (*     inv X'. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr''' & HSTMNT''' & HEQUIV'' & HFORALL''). *)
  (*     assert (X': unchanged asr'' asa asr''' asa). *)
  (*     { unfold unchanged; split; [|split]; eauto. } *)
  (*     pose proof unchanged_implies_match as Y''. eapply Y'' in X'; [|econstructor; eauto]. *)
  (*     inv X'. *)
  (*     exists asr''', asa. split; [|split; [|split]]. *)
  (*     econstructor; eauto. *)
  (*     econstructor. econstructor. eauto. *)
  (*     eauto. eauto. econstructor; eauto. *)
  (*     unfold Ple in *; cbn. rewrite max_predicate_negate. *)
  (*     destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia. *)
  (*     rewrite eval_predf_Pand. now rewrite HEVAL. *)
  (*   - unfold state_cond, state_goto in *. inv DIN0. *)
  (*     inv HMATCH. exploit transl_predicate_correct2; eauto. *)
  (*     rewrite eval_predf_Pand. rewrite HEVAL. eauto. *)
  (*     intros (asr' & HSTMNT' & HEQUIV & HFORALL). *)
  (*     exists asr', asa. split; [|split; [|split]]. *)
  (*     econstructor; eauto. *)
  (*     eapply unchanged_implies_match; eauto. instantiate (2:=asr). instantiate (1:=asa). *)
  (*     unfold unchanged. split; [|split]; eauto. *)
  (*     econstructor; eauto. *)
  (*     unfold Ple in *; cbn. rewrite max_predicate_negate. *)
  (*     destruct p; cbn; try lia. apply le_max_pred in HFRL. unfold Ple in *; lia. *)
  (*     rewrite eval_predf_Pand. now rewrite HEVAL. *)
  (* Qed. *)

  Transparent translate_predicate.

  Lemma transl_step_state_correct_single_false_standard_top :
    forall ctrl bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps max_reg max_pred,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n ctrl (curr_p, stmnt) bb = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) 
        stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun x => Ple x max_pred) (pred_uses bb) ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      exists asr', 
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) 
        /\ unchanged asr asa asr' asa
        /\ Ple (max_predicate next_p) max_pred
        /\ eval_predf ps next_p = false.
  Proof.
    intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH. destruct bb.
    - eapply transl_step_state_correct_single_false_standard; eauto; try discriminate.
    - eapply transl_step_state_correct_single_false_standard; eauto; try discriminate.
    - eapply transl_step_state_correct_single_false_standard; eauto; try discriminate.
    - eapply transl_step_state_correct_single_false_standard_top_store; eauto.
    - eapply transl_step_state_correct_single_false_standard; eauto; try discriminate.
    - eapply transl_step_state_correct_single_false_standard_top_exit; eauto.
  Qed.

  (* Lemma transl_step_state_correct_single_false_standard_top : *)
  (*   forall f s s' pc bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps sp m, *)
  (*     (* (fn_code f) ! pc = Some bb -> *) *)
  (*     transf_instr n (mk_ctrl f) (curr_p, stmnt) bb = OK (next_p, stmnt') -> *)
  (*     stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0)  *)
  (*       stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) -> *)
  (*     Forall (fun x => Ple x (max_pred_function f)) (pred_uses bb) -> *)
  (*     Ple (max_predicate curr_p) (max_pred_function f) -> *)
  (*     eval_predf ps curr_p = false -> *)
  (*     match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr asa) -> *)
  (*     exists asr' asa',  *)
  (*       stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt'  *)
  (*         (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')  *)
  (*       /\ match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr' asa') *)
  (*       /\ Ple (max_predicate next_p) (max_pred_function f) *)
  (*       /\ eval_predf ps next_p = false. *)
  (* Proof. *)
  (*   intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH. destruct bb. *)
  (*   - inv HMATCH. *)
  (*     exploit transl_step_state_correct_single_false_standard; eauto; try discriminate. *)
  (*     intros (asr' & asa' & HSTMNT' & HUNCHG & HPLE' & HEVAL'). *)
  (*     exists asr', asa'. repeat split; auto. eapply unchanged_implies_match; eauto. *)
  (*     econstructor; eauto. *)
  (*   - inv HMATCH. *)
  (*     exploit transl_step_state_correct_single_false_standard; eauto; try discriminate. *)
  (*     intros (asr' & asa' & HSTMNT' & HUNCHG & HPLE' & HEVAL'). *)
  (*     exists asr', asa'. repeat split; auto. eapply unchanged_implies_match; eauto. *)
  (*     econstructor; eauto. *)
  (*   - inv HMATCH. *)
  (*     exploit transl_step_state_correct_single_false_standard; eauto; try discriminate. *)
  (*     intros (asr' & asa' & HSTMNT' & HUNCHG & HPLE' & HEVAL'). *)
  (*     exists asr', asa'. repeat split; auto. eapply unchanged_implies_match; eauto. *)
  (*     econstructor; eauto. *)
  (*   - eapply transl_step_state_correct_single_false_standard_top_store; eauto. *)
  (*   - inv HMATCH. *)
  (*     exploit transl_step_state_correct_single_false_standard; eauto; try discriminate. *)
  (*     intros (asr' & asa' & HSTMNT' & HUNCHG & HPLE' & HEVAL'). *)
  (*     exists asr', asa'. repeat split; auto. eapply unchanged_implies_match; eauto. *)
  (*     econstructor; eauto. *)
  (*   - eapply transl_step_state_correct_single_false_standard_top_exit; eauto. *)
  (* Qed. *)

  Lemma iterm_intermediate_state :
    forall bb sp rs pr m rs' pr' m' cf,
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
               (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      exists bb' i bb'', 
        SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb'
               (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |})
        /\ step_instr ge sp (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) i 
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf)
        /\ bb = bb' ++ (i :: bb'').
  Proof. 
    induction bb; intros * HSUBPAR. 
    - inv HSUBPAR. 
    - inv HSUBPAR. destruct i1; destruct i.
      + exploit IHbb; eauto. intros (bb' & i & bb'' & HSTEPLIST & HSTEP & HLIST). 
        subst. exists (a :: bb'), i, bb''. split; [|split]; auto.
        econstructor; eauto.
      + exists nil, a, bb. exploit step_instr_finish; eauto; inversion 1; subst; clear H.
        exploit step_list_inter_not_term; eauto; inversion 1. inv H0.
        split; [|split]; auto. constructor.
  Qed.

  Lemma lt_check_step_cf_instr2 :
    forall cf n,
      check_cfi n cf = OK tt ->
      Z.pos n <= Int.max_unsigned.
  Proof.
    intros.
    destruct cf; cbn in *; try discriminate; unfold check_cfi, assert_, Errors.bind in *; 
      repeat (destruct_match; try discriminate); simplify; try destruct_match; try lia.
  Qed.

Lemma max_pred_instr_lt :
  forall y a,
    (y <= max_pred_instr y a)%positive.
Proof.
  unfold max_pred_instr; intros.
  destruct a; try destruct o; lia.
Qed.

Lemma max_pred_instr_fold_lt :
  forall b y,
    (y <= fold_left max_pred_instr b y)%positive.
Proof.
  induction b; crush.
  transitivity (max_pred_instr y a); auto.
  apply max_pred_instr_lt.
Qed.

Lemma max_pred_block_lt :
  forall y a b,
    (y <= max_pred_block y a b)%positive.
Proof.
  unfold max_pred_block, SubParBB.foldl; intros.
  apply max_pred_instr_fold_lt.
Qed.

Lemma max_fold_left_initial :
  forall l y,
    (y <= fold_left (fun (a : positive) (p0 : positive * SubParBB.t) => max_pred_block a (fst p0) (snd p0)) l y)%positive.
Proof.
  induction l; crush.
  transitivity (max_pred_block y (fst a) (snd a)); eauto.
  apply max_pred_block_lt.
Qed.

Lemma max_pred_in_max :
  forall y p i,
    In p (pred_uses i) ->
    (p <= max_pred_instr y i)%positive.
Proof.
  intros. unfold max_pred_instr. destruct i; try destruct o; cbn in *; try easy.
  - eapply predicate_lt in H; lia.
  - eapply predicate_lt in H; lia.
  - eapply predicate_lt in H; lia.
  - inv H; try lia. eapply predicate_lt in H0; lia.
  - inv H; try lia.
  - eapply predicate_lt in H; lia.
Qed.

Lemma fold_left_in_max :
  forall bb p y i,
    In i bb ->
    In p (pred_uses i) ->
    (p <= fold_left max_pred_instr bb y)%positive.
Proof.
  induction bb; crush. inv H; eauto.
  transitivity (max_pred_instr y i); [|eapply max_pred_instr_fold_lt].
  apply max_pred_in_max; auto.
Qed.

Lemma max_reg_cfi_lt :
  forall y c, (y <= max_reg_cfi y c)%positive.
Proof.
  intros. destruct c; cbn; repeat destruct_match; try apply max_fold_lt; try lia.
  now apply max_fold_lt.
Qed.

Lemma max_reg_lt :
  forall y a,
    (y <= max_reg_instr y a)%positive.
Proof.
  intros. destruct a; cbn; try apply max_fold_lt; try lia.
  apply max_reg_cfi_lt.
Qed.

Lemma fold_left_max' :
  forall l a b,
    (a <= b)%positive ->
    (fold_left Pos.max l a <= fold_left Pos.max l b)%positive.
Proof.
  induction l.
  - intros. cbn. lia.
  - intros. cbn. eapply IHl. lia.
Qed.

Lemma max_reg_lt'' :
  forall y x a,
    (x <= y)%positive ->
    (max_reg_cfi x a <= max_reg_cfi y a)%positive.
Proof.
  intros. destruct a; cbn; repeat destruct_match; try apply fold_left_max'; try lia.
  apply fold_left_max'. lia.
Qed.

Lemma max_reg_lt' :
  forall y x a,
    (x <= y)%positive ->
    (max_reg_instr x a <= max_reg_instr y a)%positive.
Proof.
  intros. destruct a; cbn; try apply fold_left_max'; try lia.
  now apply max_reg_lt''.
Qed.

Lemma max_pred_lt :
  forall y x a,
    (x <= y)%positive ->
    (max_pred_instr x a <= max_pred_instr y a)%positive.
Proof.
  intros. destruct a; cbn; repeat destruct_match; try apply fold_left_max'; try lia.
Qed.

Lemma fold_left_in_max_reg' :
  forall bb y,
    (y <= fold_left max_reg_instr bb y)%positive.
Proof.
  induction bb.
  - cbn. lia.
  - cbn in *. intros. 
    pose proof (IHbb (max_reg_instr y a)).
    pose proof (max_reg_lt y a). lia.
Qed.

Lemma fold_left_in_max_reg :
  forall bb y i,
    In i bb ->
    (max_reg_instr 1 i <= fold_left max_reg_instr bb y)%positive.
Proof.
  induction bb; crush. inv H; eauto.
  pose proof (fold_left_in_max_reg' bb (max_reg_instr y i)).
  enough ((max_reg_instr 1 i <= max_reg_instr y i)%positive). lia.
  apply max_reg_lt'; lia.
Qed.

Lemma max_reg_instr_lt_fold :
  forall bb x y,
    (x <= y)%positive -> (fold_left max_reg_instr bb x <= fold_left max_reg_instr bb y)%positive.
Proof.
  induction bb; crush.
  apply IHbb. now apply max_reg_lt'.
Qed.

Lemma fold_left_lt_block :
  forall bb y,
    (y <= fold_left (fun a el => max_reg_block a (fst el) (snd el)) bb y)%positive.
Proof.
  induction bb; crush.
  specialize (IHbb (max_reg_block y (fst a) (snd a))).
  enough (y <= max_reg_block y (fst a) (snd a))%positive; [lia|].
  unfold max_reg_block, SubParBB.foldl. apply fold_left_in_max_reg'.
Qed.

Lemma fold_left_in_max_block :
  forall bb y pc i,
    In (pc, i) bb ->
    (max_reg_block 1 pc i <= fold_left (fun a el => max_reg_block a (fst el) (snd el)) bb y)%positive.
Proof.
  induction bb; crush. inv H; eauto.
  cbn.
  pose proof (fold_left_lt_block bb (fold_left max_reg_instr (concat i) y)).
  unfold max_reg_block, SubParBB.foldl in *.
  enough (fold_left max_reg_instr (concat i) 1 <= fold_left max_reg_instr (concat i) y)%positive; [lia|].
  apply max_reg_instr_lt_fold; lia.
Qed.

Lemma max_pred_instr_lt_fold :
  forall bb x y,
    (x <= y)%positive -> (fold_left max_pred_instr bb x <= fold_left max_pred_instr bb y)%positive.
Proof.
  induction bb; crush.
  apply IHbb. now apply max_pred_lt.
Qed.

Lemma fold_left_lt_block_pred :
  forall bb y,
    (y <= fold_left (fun a el => max_pred_block a (fst el) (snd el)) bb y)%positive.
Proof.
  induction bb; crush.
  specialize (IHbb (max_pred_block y (fst a) (snd a))).
  enough (y <= max_pred_block y (fst a) (snd a))%positive; [lia|].
  apply max_pred_block_lt.
Qed.

Lemma fold_left_in_max_pred_block :
  forall bb y pc i,
    In (pc, i) bb ->
    (max_pred_block 1 pc i <= fold_left (fun a el => max_pred_block a (fst el) (snd el)) bb y)%positive.
Proof.
  induction bb; crush. inv H; eauto.
  cbn.
  pose proof (fold_left_lt_block_pred bb (fold_left max_pred_instr (concat i) y)).
  unfold max_pred_block, SubParBB.foldl in *.
  enough (fold_left max_pred_instr (concat i) 1 <= fold_left max_pred_instr (concat i) y)%positive; [lia|].
  apply max_pred_instr_lt_fold; lia.
Qed.

Lemma max_pred_function_use' :
  forall l pc bb p i y,
    In (pc, bb) l ->
    In i (concat bb) ->
    In p (pred_uses i) ->
    (p <= fold_left (fun (a : positive) (p0 : positive * SubParBB.t) => max_pred_block a (fst p0) (snd p0)) l y)%positive.
Proof.
  induction l; crush. inv H; eauto.
  transitivity (max_pred_block y (fst (pc, bb)) (snd (pc, bb))); eauto;
    [|eapply max_fold_left_initial].
  cbn. unfold SubParBB.foldl.
  eapply fold_left_in_max; eauto.
Qed.

Lemma max_pred_function_use :
  forall f pc bb i p,
    f.(fn_code) ! pc = Some bb ->
    In i (concat bb) ->
    In p (pred_uses i) ->
    (p <= max_pred_function f)%positive.
Proof.
  unfold max_pred_function; intros.
  rewrite PTree.fold_spec.
  eapply max_pred_function_use'; eauto.
  eapply PTree.elements_correct; eauto.
Qed.

  Lemma lt_max_resource_predicate_Forall :
    forall f pc bb,
    f.(GibleSubPar.fn_code) ! pc = Some bb ->
    Forall (fun i0 : instr => Forall (fun x2 : positive => Ple x2 (max_pred_function f)) (pred_uses i0)) (concat bb).
  Proof.
    intros. do 2 (eapply Forall_forall; intros). unfold Ple. eapply max_pred_function_use; eauto.
  Qed.

  Lemma transl_step_state_correct_instr :
    forall s f sp bb pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n a b,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Ple (fold_left max_pred_instr bb a) (max_pred_function f) ->
      Ple (fold_left max_reg_instr bb b) (max_reg_function f) ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc rs' pr' m') (DHTL.State s' m_ pc asr' asa')
        /\ eval_predf pr' next_p = true
        /\ Ple (max_predicate next_p) (max_pred_function f).
  Proof. 
    induction bb; intros * HFOLD HSTMNT HEVAL HSUBPAR HMATCH HPLE1 HPLE2 HPLE3.
    - inv HSUBPAR. exists asr, asa. cbn in *. inv HFOLD. auto.
    - exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANS & HINV). inv HINV. destruct y'. clear HFOLD.
      inv HSUBPAR. destruct i1; [|inv H5]. destruct i.
      cbn in HPLE1, HPLE2 |-.
      pose proof (max_pred_instr_fold_lt bb (max_pred_instr a0 a)).
      exploit transl_step_state_correct_single_instr; eauto.
      + apply Forall_forall; intros. apply max_pred_in_max with (y := a0) in H0. extlia.
      + instantiate (1:=1%positive). 
        pose proof (fold_left_in_max_reg' bb (max_reg_instr b a)).
        pose proof (max_reg_lt' b 1 a ltac:(lia)). extlia.
      + intros (asr' & asa' & HSTMNT' & HMATCH' & HEVAL' & Htrue).
        exploit IHbb; eauto.
  Qed.

  Lemma transl_step_state_correct_instr_false :
    forall ctrl bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps max_reg max_pred,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n ctrl) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun i => Forall (fun x : positive => Ple x max_pred) (pred_uses i)) bb ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      exists asr', 
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa)
        /\ unchanged asr asa asr' asa
        /\ eval_predf ps next_p = false
        /\ Ple (max_predicate next_p) max_pred.
  Proof.
    induction bb; intros * HFOLD HSTMNT HFRL HPLE HEVAL HMATCH.
    - cbn in *. inv HFOLD. exists asr; repeat split; auto. eauto.
    - exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANS & HINV). inv HINV. destruct y'.
      exploit transl_step_state_correct_single_false_standard_top; eauto. inv HFRL; eauto.
      intros (asr' & HSTMNT' & HMATCH' & HPLE' & HEVAL').
      inv HFRL. pose proof HMATCH' as HMATCHB.
      eapply unchanged_match_assocmaps in HMATCH'; eauto. exploit IHbb; eauto.
      intros (asr'' & HSTMNT'' & HMATCH'' & HPLE'' & HEVAL'').
      exists asr''; repeat (split; auto; []).
      eapply unchanged_trans; eauto.
  Qed.

  Lemma transl_step_state_correct_instr_state :
    forall s f sp bb pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa cf pc' n a b,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.State s f sp pc' rs' pr' m') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun i0 : instr => Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses i0)) bb ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      Ple (fold_left max_pred_instr bb a) (max_pred_function f) ->
      Ple (fold_left max_reg_instr bb b) (max_reg_function f) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc' rs' pr' m') (DHTL.State s' m_ pc' asr' asa').
  Proof. 
    intros * HFOLD HSTMNT HEVAL HSTEP HSTEPCF HMATCH HFRL HPLE HPLE1 HPLE2.
    exploit iterm_intermediate_state; eauto.
    intros (bb' & i & bb'' & HSTEP' & HSTEPINSTR & HBB). subst.
    exploit mfold_left_app; eauto. intros (y' & HFOLD1 & HFOLD2).
    exploit mfold_left_cons; eauto. intros (x' & y_other & HFOLDFINAL & HINSTR & HSUBST).
    inv HSUBST.
    destruct x'. destruct y_other.
    exploit transl_step_state_correct_instr; try eapply HFOLD1; eauto.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    (* pose proof (fold_left_in_max_reg' bb'' (max_reg_instr (fold_left max_reg_instr bb' b) i)). *)
    (* pose proof (max_reg_lt (fold_left max_reg_instr bb' b) i). *)
    pose proof (max_pred_instr_fold_lt bb'' (max_pred_instr (fold_left max_pred_instr bb' a) i)).
    pose proof (max_pred_instr_lt (fold_left max_pred_instr bb' a) i). 
    instantiate (1:=a). extlia.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    pose proof (fold_left_in_max_reg' bb'' (max_reg_instr (fold_left max_reg_instr bb' b) i)).
    pose proof (max_reg_lt (fold_left max_reg_instr bb' b) i).
    instantiate (1:=b). extlia.
    intros (asr' & asa' & HSTMNT' & HMATCH' & HNEXT & HPRED).
    exploit transl_step_state_correct_single_instr_term; eauto.
    apply Forall_forall; intros.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    pose proof (max_pred_instr_fold_lt bb'' (max_pred_instr (fold_left max_pred_instr bb' a) i)).
    pose proof (max_pred_instr_lt (fold_left max_pred_instr bb' a) i). 
    eapply max_pred_in_max with (y := (fold_left max_pred_instr bb' a)) in H. extlia.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    pose proof (fold_left_in_max_reg' bb'' (max_reg_instr (fold_left max_reg_instr bb' b) i)).
    instantiate (1:=(fold_left max_reg_instr bb' b)). extlia.
    intros (asr'0 & asa'0 & HSTMNT'' & HMATCH'' & HNEXT'').
    inv HMATCH''.
    exploit transl_step_state_correct_instr_false; eauto.
    { eapply Forall_app in HFRL. inv HFRL. inv H0. eauto. }
    { eapply all_le_max_predicate_instr; eauto. eapply Forall_app in HFRL. inv HFRL. inv H0. eauto. }
    intros (asr'' & HSTMNT''' & HUNCHANGED & HEVAL' & HPLE').
    exists asr'', asa'0. split; auto.
    eapply unchanged_implies_match; eauto. econstructor; eauto.
  Qed.

  Lemma transl_step_state_correct_instr_return :
    forall s f sp bb pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa cf v m'' n a b,
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt 
        (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.Returnstate s v m'') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      Forall (fun i0 : instr => Forall (fun x : positive => Ple x (max_pred_function f)) (pred_uses i0)) bb ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      Ple (fold_left max_pred_instr bb a) (max_pred_function f) ->
      Ple (fold_left max_reg_instr bb b) (max_reg_function f) ->
      exists asr' asa' retval,
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ val_value_lessdef v retval
        /\ asr'!(m_.(DHTL.mod_finish)) = Some (ZToValue 1)
        /\ asr'!(m_.(DHTL.mod_return)) = Some retval
        /\ asr'!(m_.(DHTL.mod_st)) = Some (posToValue n).
  Proof.
    intros * HFOLD HSTMNT HEVAL HSTEP HSTEPCF HMATCH HFRL HPLE HPLE1 HPLE2.
    exploit iterm_intermediate_state; eauto.
    intros (bb' & i & bb'' & HSTEP' & HSTEPINSTR & HBB). subst.
    exploit mfold_left_app; eauto. intros (y' & HFOLD1 & HFOLD2).
    exploit mfold_left_cons; eauto. intros (x' & y_other & HFOLDFINAL & HINSTR & HSUBST).
    inv HSUBST.
    destruct x'. destruct y_other.
    exploit transl_step_state_correct_instr; try eapply HFOLD1; eauto.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    (* pose proof (fold_left_in_max_reg' bb'' (max_reg_instr (fold_left max_reg_instr bb' b) i)). *)
    (* pose proof (max_reg_lt (fold_left max_reg_instr bb' b) i). *)
    pose proof (max_pred_instr_fold_lt bb'' (max_pred_instr (fold_left max_pred_instr bb' a) i)).
    pose proof (max_pred_instr_lt (fold_left max_pred_instr bb' a) i). 
    instantiate (1:=a). extlia.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    pose proof (fold_left_in_max_reg' bb'' (max_reg_instr (fold_left max_reg_instr bb' b) i)).
    pose proof (max_reg_lt (fold_left max_reg_instr bb' b) i).
    instantiate (1:=b). extlia.
    intros (asr' & asa' & HSTMNT' & HMATCH' & HNEXT & HGT).
    exploit transl_step_state_correct_single_instr_term_return; eauto.
    apply Forall_forall; intros.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    pose proof (max_pred_instr_fold_lt bb'' (max_pred_instr (fold_left max_pred_instr bb' a) i)).
    pose proof (max_pred_instr_lt (fold_left max_pred_instr bb' a) i). 
    eapply max_pred_in_max with (y := (fold_left max_pred_instr bb' a)) in H. extlia.
    rewrite fold_left_app in HPLE1, HPLE2 |-. cbn in HPLE1, HPLE2 |-.
    pose proof (fold_left_in_max_reg' bb'' (max_reg_instr (fold_left max_reg_instr bb' b) i)).
    instantiate (1:=(fold_left max_reg_instr bb' b)). extlia.
    intros (v' & HSTMNT'' & HEVAL2 & HEVAL3).
    inv HMATCH'.
    exploit transl_step_state_correct_instr_false; eauto.
    { eapply Forall_app in HFRL. inv HFRL. inv H0. eauto. }
    { eapply all_le_max_predicate_instr; eauto. eapply Forall_app in HFRL. inv HFRL. inv H0. eauto. }
    { unfold transl_module, Errors.bind, ret in TF. repeat (destruct_match; try discriminate; []).
      inv TF. repeat eapply regs_lessdef_add_greater; eauto; cbn; unfold Plt; lia. }
    intros (asr'' & HSTMNT''' & HUNCHANGED & HEVAL' & HPLE').
    exists asr'', asa', v'. repeat (split; auto; []).
    inv HUNCHANGED. inv H0. unfold transl_module, Errors.bind, ret in TF. repeat (destruct_match; try discriminate; []).
    inv TF; cbn in *.
    split; [|split]; eapply H1; repeat rewrite AssocMap.gso by lia; now rewrite AssocMap.gss.
  Qed.

  (* Lemma transl_step_state_correct_chained_state : *)
  (*   forall s f sp bb pc pc' curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa cf n, *)
  (*     (* (fn_code f) ! pc = Some bb -> *) *)
  (*     mfold_left (transf_chained_block n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') -> *)
  (*     stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt  *)
  (*       (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) -> *)
  (*     eval_predf pr curr_p = true -> *)
  (*     SubParBB.step ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb *)
  (*            (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) -> *)
  (*     step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.State s f sp pc' rs' pr' m') -> *)
  (*     match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) -> *)
  (*     exists asr' asa', *)
  (*       stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt'  *)
  (*         (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') *)
  (*       /\ match_states (GibleSubPar.State s f sp pc' rs' pr' m') (DHTL.State s' m_ pc' asr' asa'). *)
  (* Proof. Abort. *)

  Lemma transl_step_through_cfi' :
    forall bb ctrl curr_p stmnt next_p stmnt' p cf n,
      mfold_left (transf_instr n ctrl) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      In (RBexit p cf) bb ->
      exists curr_p' stmnt'', 
        translate_cfi n ctrl (Some (Pand curr_p' (dfltp p))) cf = OK stmnt'' 
        /\ check_cfi n cf = OK tt.
  Proof.
    induction bb.
    - inversion 2.
    - intros * HFOLD HIN.
      exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANSF & HSUBST).
      inversion HSUBST. inv H0. clear HSUBST.
      inv HIN; destruct y'; eauto.
      cbn in HTRANSF. unfold Errors.bind in HTRANSF. repeat (destruct_match; try discriminate; []).
      inv HTRANSF. destruct u. eauto.
  Qed.

  Lemma transl_step_through_cfi :
    forall bb ctrl curr_p stmnt next_p stmnt' l p cf n,
      mfold_left (transf_chained_block n ctrl) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      In l bb ->
      In (RBexit p cf) l ->
      exists curr_p' stmnt'', translate_cfi n ctrl (Some (Pand curr_p' (dfltp p))) cf = OK stmnt''.
  Proof.
    induction bb.
    - inversion 2.
    - intros * HFOLD HIN1 HIN2.
      exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANSF & HSUBST).
      destruct y'. inv HSUBST.
      inv HIN1; eauto.
      exploit transl_step_through_cfi'; eauto.
      simplify. eauto.
  Qed.

  Lemma cf_in_bb_subparbb' :
    forall sp bb a b cf,
      SubParBB.step_instr_list ge sp (Iexec a) bb (Iterm b cf) ->
      exists curr_p, In (RBexit curr_p cf) bb /\ truthy (is_ps b) curr_p.
  Proof.
    induction bb.
    - intros. inv H.
    - intros. inv H.
      destruct i1.
      + exploit IHbb; eauto. intros (curr_p & HIN & HTRY).
        exists curr_p. split; auto. now apply in_cons.
      + inv H4. exists p. inv H6; split; auto; now constructor.
  Qed.

  Lemma cf_in_bb_subparbb :
    forall sp bb a b cf,
      SubParBB.step_instr_seq ge sp (Iexec a) bb (Iterm b cf) ->
      exists l curr_p, In l bb /\ In (RBexit curr_p cf) l /\ truthy (is_ps b) curr_p.
  Proof.
    induction bb.
    - intros. inv H.
    - intros. inv H.
      + exploit IHbb; eauto. intros (l & curr_p & HIN2 & HIN & HTRY).
        exists l, curr_p. split; auto. now apply in_cons.
      + exploit cf_in_bb_subparbb'; eauto. 
        intros (curr_p & HIN & HTR).
        exists a, curr_p. split; auto. now constructor.
  Qed.

  Lemma match_states_cf_events_translate_cfi:
    forall T1 cf T2 p t ctrl stmnt n,
      translate_cfi n ctrl p cf = OK stmnt ->
      step_cf_instr ge T1 cf t T2 ->
      t = Events.E0.
  Proof.
    intros * HGET HSTEP.
    destruct cf; try discriminate; inv HSTEP; eauto.
  Qed.

  Lemma match_states_cf_states_translate_cfi:
    forall T1 cf T2 p t ctrl stmnt n,
      translate_cfi n ctrl p cf = OK stmnt ->
      step_cf_instr ge T1 cf t T2 ->
      exists s f sp pc rs pr m,
        T1 = GibleSubPar.State s f sp pc rs pr m
        /\ ((exists pc', T2 = GibleSubPar.State s f sp pc' rs pr m)
            \/ (exists v m' stk, Mem.free m stk 0 (fn_stacksize f) = Some m' 
                /\ sp = Values.Vptr stk Ptrofs.zero 
                /\ T2 = GibleSubPar.Returnstate s v m')).
  Proof.
    intros * HGET HSTEP.
    destruct cf; try discriminate; inv HSTEP; try (now repeat econstructor).
  Qed.

  Lemma translate_cfi_goto:
    forall pr curr_p pc s ctrl asr asa n,
      (forall r, Ple r (max_predicate curr_p) ->
        find_assocmap 1 (pred_enc r) asr = boolToValue (PMap.get r pr)) ->
      eval_predf pr curr_p = true ->
      translate_cfi n ctrl (Some curr_p) (RBgoto pc) = OK s ->
      stmnt_runp tt (e_assoc asr) asa s
        (e_assoc (AssocMap.set ctrl.(ctrl_st) (posToValue pc) asr)) asa.
  Proof.
    intros * HPLE HEVAL HTRANSL. unfold translate_cfi in *.
    inversion_clear HTRANSL as []. destruct_match.
    - constructor. constructor. econstructor. eapply pred_expr_correct.
      intros. unfold Ple in *. eapply HPLE.
      now apply max_predicate_deep_simplify in H.
      eauto. constructor. rewrite eval_predf_deep_simplify. rewrite HEVAL. auto.
    - repeat constructor.
  Qed.

  Lemma translate_cfi_goto_none:
    forall pc s ctrl asr asa n,
      translate_cfi n ctrl None (RBgoto pc) = OK s ->
      stmnt_runp tt (e_assoc asr) asa s
        (e_assoc (AssocMap.set ctrl.(ctrl_st) (posToValue pc) asr)) asa.
  Proof. intros; inversion_clear H as []; repeat constructor. Qed.

  Lemma transl_module_ram_none :
    forall f m_,
      transl_module f = OK m_ ->
      m_.(mod_ram) = None.
  Proof.
    unfold transl_module, Errors.bind, Errors.bind2, ret; intros.
    repeat (destruct_match; try discriminate). inversion_clear H as []. auto.
  Qed.

  Lemma match_states_ok_transl :
    forall s f sp pc rs pr mem R1,
      match_states (GibleSubPar.State s f sp pc rs pr mem) R1 ->
      exists m asr asa s', transl_module f = OK m /\ R1 = DHTL.State s' m pc asr asa.
  Proof. inversion 1; subst. now repeat eexists. Qed.

  Lemma transl_spec_in_output :
    forall l ctrl d_in d_out pc stmnt,
      mfold_left (transf_seq_block ctrl) l (OK d_in) = OK d_out ->
      d_in ! pc = Some stmnt ->
      d_out ! pc = Some stmnt.
  Proof.
    induction l; intros * HFOLD HIN.
    - cbn in *; now (inversion HFOLD; subst).
    - exploit mfold_left_cons; eauto. 
      intros (x' & y' & HFOLD_EXP & TRANSFSEQ & HINV). inv HINV.
      unfold transf_seq_block in TRANSFSEQ. repeat (destruct_match; try discriminate; []).
      destruct (peq pc n); subst.
      + now rewrite Heqo in HIN.
      + unfold Errors.bind2 in TRANSFSEQ. repeat (destruct_match; try discriminate; []).
        inv TRANSFSEQ. eapply IHl; eauto. now rewrite PTree.gso by auto.
  Qed.

  Lemma transl_spec_correct' :
    forall l ctrl d_in d_out pc bb,
      mfold_left (transf_seq_block ctrl) l (OK d_in) = OK d_out ->
      In (pc, bb) l ->
      exists n pred' stmnt, transf_chained_block n ctrl (Ptrue, Vskip) (concat bb) = OK (pred', stmnt)
        /\ d_out ! pc = Some stmnt.
  Proof.
    induction l; [now inversion 2|].
    cbn -[mfold_left]. intros * HFOLD HIN.
    exploit mfold_left_cons; eauto. 
    intros (x' & y' & HFOLD_EXP & TRANSFSEQ & HINV). inv HINV.
    inversion_clear HIN as [HIN' | HIN']; eauto.
    inversion HIN' as [HIN_CLEAR]; subst. clear HIN_CLEAR.
    unfold transf_seq_block, Errors.bind2 in TRANSFSEQ. 
    repeat (destruct_match; try discriminate; []).
    inversion TRANSFSEQ as []; subst. clear TRANSFSEQ.
    exploit transl_spec_in_output; eauto. now rewrite PTree.gss.
  Qed.

  Lemma transl_spec_correct :
    forall ctrl d_in d_out pc bb c,
      mfold_left (transf_seq_block ctrl) (PTree.elements c) (OK d_in) = OK d_out ->
      c ! pc = Some bb ->
      exists n pred' stmnt, transf_chained_block n ctrl (Ptrue, Vskip) (concat bb) = OK (pred', stmnt)
        /\ d_out ! pc = Some stmnt.
  Proof. intros. eapply transl_spec_correct'; eauto using PTree.elements_correct. Qed.

  Lemma lt_check_step_cf_instr :
    forall s f sp pc rs pr m cf t s' f' sp' x rs' pr' m' ctrl p st n,
      translate_cfi n ctrl p cf = OK st ->
      check_cfi n cf = OK tt ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs pr m) cf t
            (GibleSubPar.State s' f' sp' x rs' pr' m') ->
      Z.pos x <= Int.max_unsigned.
  Proof.
    intros.
    destruct cf; cbn in *; try discriminate; unfold check_cfi, assert_, Errors.bind in *; 
      repeat (destruct_match; try discriminate); simplify; inv H1; try destruct_match; try lia.
    (* This was used for case statement translation *)
    (* apply list_nth_z_in in H19. *)
    (* eapply forallb_forall in Heqb; eauto. lia. *)
  Qed.

  Lemma transl_step_state_correct :
    forall s f sp pc rs rs' m m' bb pr pr' state cf t,
      (fn_code f) ! pc = Some bb ->
      SubParBB.step ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf t state ->
      forall R1 : DHTL.state,
        match_states (GibleSubPar.State s f sp pc rs pr m) R1 ->
        exists R2 : DHTL.state, 
          Smallstep.plus DHTL.step tge R1 t R2 /\ match_states state R2.
  Proof.
    intros * HIN HSTEP HCF * HMATCH.
    exploit match_states_ok_transl; eauto.
    intros (m0 & asr & asa & s' & HTRANSL & ?). subst.
    unfold transl_module, Errors.bind, bind, ret in HTRANSL.
    repeat (destruct_match; try discriminate; []).
    exploit transl_spec_correct; eauto.
    intros (n & pred' & stmnt0 & HTRANSF & HGET).
    exploit step_exec_concat; eauto; intros HCONCAT.
    exploit cf_in_bb_subparbb'; eauto. intros (exit_p & HINEXIT & HTRUTHY).
    exploit transl_step_through_cfi'; eauto. intros (curr_p & _stmnt & HCFI & HCHECK).
    exploit match_states_cf_states_translate_cfi; eauto. 
    intros (s0 & f1 & sp0 & pc0 & rs0 & pr0 & m2 & HPARSTATE & HEXISTS).
    exploit match_states_cf_events_translate_cfi; eauto; intros; subst.
    inv HEXISTS.
    - inv HPARSTATE. inv H. exploit transl_step_state_correct_instr_state; eauto.
      constructor. eapply lt_max_resource_predicate_Forall; eauto.
      cbn; extlia. unfold max_pred_function. rewrite PTree.fold_spec.
      unfold Ple in *. eapply fold_left_in_max_pred_block. apply PTree.elements_correct. eassumption.
      intros.  exploit H.
      unfold Ple in *. unfold max_reg_function. rewrite PTree.fold_spec. pose proof (fold_left_in_max_block (PTree.elements (fn_code f1)) 1 pc0 bb ltac:(apply PTree.elements_correct; eassumption)). unfold max_reg_block, SubParBB.foldl in *. instantiate (1:=1%positive). unfold Gible.node in *. lia. clear H. 
      intros (asr' & asa' & HSTMNTRUN & HMATCH').
      do 2 apply match_states_merge_empty_all in HMATCH'.
      eexists. split; eauto. inv HMATCH. inv CONST.
      apply Smallstep.plus_one. econstructor; eauto.
      inv HTRANSL. auto. erewrite transl_module_ram_none by eauto. constructor.
      inv HMATCH'. unfold state_st_wf in WF0. auto.
      eapply lt_check_step_cf_instr; eauto.
    - inv HPARSTATE; simplify. exploit transl_step_state_correct_instr_return; eauto.
      constructor. eapply lt_max_resource_predicate_Forall; eauto.
      cbn; unfold Ple; lia.
      intros.  exploit H0.
      unfold max_pred_function. rewrite PTree.fold_spec.
      unfold Ple in *. eapply fold_left_in_max_pred_block. apply PTree.elements_correct. eassumption.
      intros.
      unfold Ple in *. unfold max_reg_function. rewrite PTree.fold_spec. pose proof (fold_left_in_max_block (PTree.elements (fn_code f1)) 1 pc0 bb ltac:(apply PTree.elements_correct; eassumption)). unfold max_reg_block, SubParBB.foldl in *. instantiate (1:=1%positive). unfold Gible.node in *. lia. clear H. 
      intros (asr' & asa' & retval & HSTMNT_RUN & HVAL & HASR1 & HASR2 & HASR3).
      inv HMATCH. inv CONST.
      econstructor. split.
      eapply Smallstep.plus_two.
      econstructor.
      + eauto.
      + eauto.
      + eauto.
      + inv HTRANSL. eauto.
      + eauto.
      + erewrite transl_module_ram_none by eauto. constructor.
      + eauto.
      + eauto.
      + unfold merge_regs. rewrite AssocMapExt.merge_base_1. rewrite AssocMapExt.merge_base_1. eauto.
      + eapply lt_check_step_cf_instr2; eauto.
      + eapply DHTL.step_finish.
        * now do 2 rewrite AssocMapExt.merge_base_1.
        * do 2 rewrite AssocMapExt.merge_base_1; eauto.
      + auto.
      + constructor. auto. auto.
  Qed.

  Theorem transl_step_correct:
    forall (S1 : GibleSubPar.state) t S2,
      GibleSubPar.step ge S1 t S2 ->
      forall (R1 : DHTL.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus DHTL.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1.
    - now (eapply transl_step_state_correct; eauto).
    - now apply transl_callstate_correct.
    - inversion 1.
    - now apply transl_returnstate_correct.
  Qed.
  #[local] Hint Resolve transl_step_correct : htlproof.

#[local] Hint Resolve transl_returnstate_correct : htlproof.
#[local] Hint Resolve transl_final_states : htlproof.
#[local] Hint Resolve transl_initial_states : htlproof.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (GibleSubPar.semantics prog) (DHTL.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus; eauto with htlproof.
    apply senv_preserved; eauto.
  Qed.

End CORRECTNESS.
