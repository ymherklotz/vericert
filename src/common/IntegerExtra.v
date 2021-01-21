(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Numbers.Integer.Binary.ZBinary.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import vericert.common.Vericertlib.

Local Open Scope Z_scope.

Module PtrofsExtra.

  Ltac ptrofs_mod_match m :=
    match goal with
    | [ H : ?x = 0 |- context[?x] ] => rewrite H
    | [ _ : _ |- context[_ - 0] ] => rewrite Z.sub_0_r
    | [ _ : _ |- context[0 + _] ] => rewrite Z.add_0_l
    | [ _ : _ |- context[_ + 0] ] => rewrite Z.add_0_r
    | [ _ : _ |- context[0 * _] ] => rewrite Z.mul_0_l
    | [ _ : _ |- context[_ * 0] ] => rewrite Z.mul_0_r
    | [ _ : _ |- context[?m mod ?m] ] =>
      rewrite Z_mod_same_full with (a := m)
    | [ _ : _ |- context[0 mod _] ] =>
      rewrite Z.mod_0_l
    | [ _ : _ |- context[(_ mod ?m) mod ?m] ] =>
      rewrite Zmod_mod
    | [ _ : _ |- context[(_ mod Ptrofs.modulus) mod m ] ] =>
      rewrite <- Zmod_div_mod;
      try (crush; lia || assumption)

    | [ _ : _ |- context[Ptrofs.modulus mod m] ] =>
      rewrite Zdivide_mod with (a := Ptrofs.modulus);
      try (lia || assumption)

    | [ _ : _ |- context[Ptrofs.signed ?a mod Ptrofs.modulus] ] =>
      rewrite Z.mod_small with (a := Ptrofs.signed a) (b := Ptrofs.modulus)

    | [ _ : _ |- context[(?x - ?y) mod ?m] ] =>
      rewrite Zminus_mod with (a := x) (b := y) (n := m)

    | [ _ : _ |- context[((?x + ?y) mod ?m) + _] ] =>
      rewrite Zplus_mod with (a := x) (b := y) (n := m)
    | [ _ : _ |- context[(?x + ?y) mod ?m] ] =>
      rewrite Zplus_mod with (a := x) (b := y) (n := m)

    | [ _ : _ |- context[(?x * ?y) mod ?m] ] =>
      rewrite Zmult_mod with (a := x) (b := y) (n := m)
    end.

  Ltac ptrofs_mod_tac m :=
    repeat (ptrofs_mod_match m); lia.

  Lemma signed_mod_unsigned_mod :
    forall x m,
      0 < m ->
      Ptrofs.modulus mod m = 0 ->
      Ptrofs.signed x mod m = 0 ->
      Ptrofs.unsigned x mod m = 0.
  Proof.
    intros.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Ptrofs.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           | [ _ : _ |- context[Ptrofs.unsigned _] ] => rewrite Ptrofs.unsigned_signed
           end; try crush; ptrofs_mod_tac m.
  Qed.

  Lemma of_int_mod :
    forall x m,
      Int.unsigned x mod m = 0 ->
      Ptrofs.unsigned (Ptrofs.of_int x) mod m = 0.
  Proof.
    intros.
    unfold Ptrofs.of_int.
    rewrite Ptrofs.unsigned_repr; crush;
      apply Int.unsigned_range_2.
  Qed.

  Lemma mul_mod :
    forall x y m,
      0 < m ->
      (m | Ptrofs.modulus) ->
      Ptrofs.unsigned x mod m = 0 ->
      Ptrofs.unsigned y mod m = 0 ->
      (Ptrofs.signed (Ptrofs.mul x y)) mod m = 0.
  Proof.
    intros. unfold Ptrofs.mul.
    rewrite Ptrofs.signed_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Ptrofs.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           end; try(crush; lia); ptrofs_mod_tac m.
  Qed.

  Lemma add_mod :
    forall x y m,
      0 < m ->
      (m | Ptrofs.modulus) ->
      Ptrofs.unsigned x mod m = 0 ->
      Ptrofs.unsigned y mod m = 0 ->
      (Ptrofs.unsigned (Ptrofs.add x y)) mod m = 0.
  Proof.
    intros. unfold Ptrofs.add.
    rewrite Ptrofs.unsigned_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Ptrofs.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           end; try (crush; lia); ptrofs_mod_tac m.
  Qed.

  Lemma mul_divu :
    forall x y,
      0 < Ptrofs.unsigned x ->
      Ptrofs.unsigned y mod Ptrofs.unsigned x = 0 ->
      (Integers.Ptrofs.mul x (Integers.Ptrofs.divu y x)) = y.
  Proof.
    intros.

    assert (x <> Ptrofs.zero).
    { intro.
      rewrite H1 in H.
      replace (Ptrofs.unsigned Ptrofs.zero) with 0 in H by reflexivity.
      lia. }

    exploit (Ptrofs.modu_divu_Euclid y x); auto; intros.
    unfold Ptrofs.modu in H2. rewrite H0 in H2.
    replace (Ptrofs.repr 0) with Ptrofs.zero in H2 by reflexivity.
    rewrite Ptrofs.add_zero in H2.
    rewrite Ptrofs.mul_commut.
    congruence.
  Qed.

  Lemma divu_unsigned :
    forall x y,
      0 < Ptrofs.unsigned y ->
      Ptrofs.unsigned x <= Ptrofs.max_unsigned ->
      Ptrofs.unsigned (Ptrofs.divu x y) = Ptrofs.unsigned x / Ptrofs.unsigned y.
  Proof.
    intros.
    unfold Ptrofs.divu.
    rewrite Ptrofs.unsigned_repr; auto.
    split.
    apply Z.div_pos; auto.
    apply Ptrofs.unsigned_range.
    apply Z.div_le_upper_bound; auto.
    eapply Z.le_trans.
    exact H0.
    rewrite Z.mul_comm.
    apply Z.le_mul_diag_r; crush.
  Qed.

  Lemma mul_unsigned :
    forall x y,
      Ptrofs.mul x y =
      Ptrofs.repr (Ptrofs.unsigned x * Ptrofs.unsigned y).
  Proof.
    intros; unfold Ptrofs.mul.
    apply Ptrofs.eqm_samerepr.
    apply Ptrofs.eqm_mult; exists 0; lia.
  Qed.

  Lemma pos_signed_unsigned :
    forall x,
      0 <= Ptrofs.signed x ->
      Ptrofs.signed x = Ptrofs.unsigned x.
  Proof.
    intros.
    rewrite Ptrofs.unsigned_signed.
    destruct (Ptrofs.lt x Ptrofs.zero) eqn:EQ.
    unfold Ptrofs.lt in EQ.
    destruct (zlt (Ptrofs.signed x) (Ptrofs.signed Ptrofs.zero)); try discriminate.
    replace (Ptrofs.signed (Ptrofs.zero)) with 0 in l by reflexivity. lia.
    reflexivity.
  Qed.
End PtrofsExtra.

Ltac ptrofs :=
  repeat match goal with
         | [ |- context[Ptrofs.add (Ptrofs.zero) _] ] => setoid_rewrite Ptrofs.add_zero_l
         | [ H : context[Ptrofs.add (Ptrofs.zero) _] |- _ ] => setoid_rewrite Ptrofs.add_zero_l in H

         | [ |- context[Ptrofs.repr 0] ] => replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity
         | [ H : context[Ptrofs.repr 0] |- _ ] =>
           replace (Ptrofs.repr 0) with Ptrofs.zero in H by reflexivity

         | [ H: context[Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned _))] |- _ ] =>
           setoid_rewrite Ptrofs.unsigned_repr in H; [>| apply Ptrofs.unsigned_range_2]
         | [ |- context[Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned _))] ] =>
           rewrite Ptrofs.unsigned_repr; [>| apply Ptrofs.unsigned_range_2]

         | [ |- context[0 <= Ptrofs.unsigned _] ] => apply Ptrofs.unsigned_range_2
         end.

Module IntExtra.
  Import Int.
  Ltac int_mod_match m :=
    match goal with
    | [ H : ?x = 0 |- context[?x] ] => rewrite H
    | [ _ : _ |- context[_ - 0] ] => rewrite Z.sub_0_r
    | [ _ : _ |- context[0 + _] ] => rewrite Z.add_0_l
    | [ _ : _ |- context[_ + 0] ] => rewrite Z.add_0_r
    | [ _ : _ |- context[0 * _] ] => rewrite Z.mul_0_l
    | [ _ : _ |- context[_ * 0] ] => rewrite Z.mul_0_r
    | [ _ : _ |- context[?m mod ?m] ] =>
      rewrite Z_mod_same_full with (a := m)
    | [ _ : _ |- context[0 mod _] ] =>
      rewrite Z.mod_0_l
    | [ _ : _ |- context[(_ mod ?m) mod ?m] ] =>
      rewrite Zmod_mod
    | [ _ : _ |- context[(_ mod Int.modulus) mod m ] ] =>
      rewrite <- Zmod_div_mod;
      try (crush; lia || assumption)

    | [ _ : _ |- context[Int.modulus mod m] ] =>
      rewrite Zdivide_mod with (a := Int.modulus);
      try (lia || assumption)

    | [ _ : _ |- context[Int.signed ?a mod Int.modulus] ] =>
      rewrite Z.mod_small with (a := Int.signed a) (b := Int.modulus)

    | [ _ : _ |- context[(?x - ?y) mod ?m] ] =>
      rewrite Zminus_mod with (a := x) (b := y) (n := m)

    | [ _ : _ |- context[((?x + ?y) mod ?m) + _] ] =>
      rewrite Zplus_mod with (a := x) (b := y) (n := m)
    | [ _ : _ |- context[(?x + ?y) mod ?m] ] =>
      rewrite Zplus_mod with (a := x) (b := y) (n := m)

    | [ _ : _ |- context[(?x * ?y) mod ?m] ] =>
      rewrite Zmult_mod with (a := x) (b := y) (n := m)
    end.

  Ltac int_mod_tac m :=
    repeat (int_mod_match m); lia.

  Lemma mul_mod1 :
    forall x y m,
      0 < m ->
      (m | Int.modulus) ->
      Int.unsigned x mod m = 0 ->
      (Int.unsigned (Int.mul x y)) mod m = 0.
  Proof.
    intros. unfold Int.mul.
    rewrite Int.unsigned_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Int.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           end; try (crush; lia); int_mod_tac m.
  Qed.

  Lemma mul_mod2 :
    forall x y m,
      0 < m ->
      (m | Int.modulus) ->
      Int.unsigned y mod m = 0 ->
      (Int.unsigned (Int.mul x y)) mod m = 0.
  Proof.
    intros. unfold Int.mul.
    rewrite Int.unsigned_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Int.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           end; try (crush; lia); int_mod_tac m.
  Qed.

  Lemma add_mod :
    forall x y m,
      0 < m ->
      (m | Int.modulus) ->
      Int.unsigned x mod m = 0 ->
      Int.unsigned y mod m = 0 ->
      (Int.unsigned (Int.add x y)) mod m = 0.
  Proof.
    intros. unfold Int.add.
    rewrite Int.unsigned_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Int.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           end; try (crush; lia); int_mod_tac m.
  Qed.

  Definition ofbytes (a b c d : byte) : int :=
    or (shl (repr (Byte.unsigned a)) (repr (3 * Byte.zwordsize)))
       (or (shl (repr (Byte.unsigned b)) (repr (2 * Byte.zwordsize)))
           (or (shl (repr (Byte.unsigned c)) (repr Byte.zwordsize))
               (repr (Byte.unsigned d)))).

  Definition byte1 (n: int) : byte := Byte.repr (unsigned n).

  Definition byte2 (n: int) : byte := Byte.repr (unsigned (shru n (repr Byte.zwordsize))).

  Definition byte3 (n: int) : byte := Byte.repr (unsigned (shru n (repr (2 * Byte.zwordsize)))).

  Definition byte4 (n: int) : byte := Byte.repr (unsigned (shru n (repr (3 * Byte.zwordsize)))).

  Lemma bits_byte1:
    forall n i, 0 <= i < Byte.zwordsize -> Byte.testbit (byte1 n) i = testbit n i.
  Proof.
    intros. unfold byte1. rewrite Byte.testbit_repr; auto.
  Qed.

  Lemma bits_byte2:
    forall n i, 0 <= i < Byte.zwordsize -> Byte.testbit (byte2 n) i = testbit n (i + Byte.zwordsize).
  Proof.
    intros. unfold byte2. rewrite Byte.testbit_repr; auto.
    assert (zwordsize = 4 * Byte.zwordsize) by reflexivity.
    fold (testbit (shru n (repr Byte.zwordsize)) i). rewrite bits_shru.
    change (unsigned (repr Byte.zwordsize)) with Byte.zwordsize.
    apply zlt_true. lia. lia.
  Qed.

  Lemma bits_byte3:
    forall n i, 0 <= i < Byte.zwordsize -> Byte.testbit (byte3 n) i = testbit n (i + (2 * Byte.zwordsize)).
  Proof.
    intros. unfold byte3. rewrite Byte.testbit_repr; auto.
    assert (zwordsize = 4 * Byte.zwordsize) by reflexivity.
    fold (testbit (shru n (repr (2 * Byte.zwordsize))) i). rewrite bits_shru.
    change (unsigned (repr (2 * Byte.zwordsize))) with (2 * Byte.zwordsize).
    apply zlt_true. lia. lia.
  Qed.

  Lemma bits_byte4:
    forall n i, 0 <= i < Byte.zwordsize -> Byte.testbit (byte4 n) i = testbit n (i + (3 * Byte.zwordsize)).
  Proof.
    intros. unfold byte4. rewrite Byte.testbit_repr; auto.
    assert (zwordsize = 4 * Byte.zwordsize) by reflexivity.
    fold (testbit (shru n (repr (3 * Byte.zwordsize))) i). rewrite bits_shru.
    change (unsigned (repr (3 * Byte.zwordsize))) with (3 * Byte.zwordsize).
    apply zlt_true. lia. lia.
  Qed.

  Lemma bits_ofwords:
    forall b4 b3 b2 b1 i, 0 <= i < zwordsize ->
                          testbit (ofbytes b4 b3 b2 b1) i =
                          if zlt i Byte.zwordsize
                          then Byte.testbit b1 i
                          else (if zlt i (2 * Byte.zwordsize)
                                then Byte.testbit b2 (i - Byte.zwordsize)
                                else (if zlt i (3 * Byte.zwordsize)
                                      then Byte.testbit b2 (i - 2 * Byte.zwordsize)
                                      else Byte.testbit b2 (i - 3 * Byte.zwordsize))).
  Proof.
    intros. unfold ofbytes. repeat (rewrite bits_or; auto). repeat (rewrite bits_shl; auto).
    change (unsigned (repr Byte.zwordsize)) with Byte.zwordsize.
    change (unsigned (repr (2 * Byte.zwordsize))) with (2 * Byte.zwordsize).
    change (unsigned (repr (3 * Byte.zwordsize))) with (3 * Byte.zwordsize).
    assert (zwordsize = 4 * Byte.zwordsize) by reflexivity.
    destruct (zlt i Byte.zwordsize).
    rewrite testbit_repr; auto.
    Abort.

  Lemma div_divs_equiv :
    forall x y,
      signed x >= 0 ->
      signed y >= 0 ->
      divs x y = divu x y.
  Proof.
    unfold divs, divu.
    intros.
    rewrite !signed_eq_unsigned;
    try rewrite Zquot.Zquot_Zdiv_pos; try reflexivity;
    lazymatch goal with
    | |- unsigned _ <= max_signed =>
      solve [rewrite <- signed_positive; assumption]
    | |- 0 <= unsigned _ => solve [apply unsigned_range_2]
    end.
  Qed.

  Lemma neg_signed' :
    forall x : int,
      unsigned x <> 2147483648 ->
      signed (neg x) = - signed x.
  Proof.
    intros x Hhalf.
    Transparent repr.
    unfold signed.
    simpl.
    rewrite Z_mod_modulus_eq.
    replace modulus with 4294967296; auto.
    replace half_modulus with 2147483648; auto.
    repeat match goal with | |- context[if ?x then _ else _] => destruct x end.
    - destruct (Z.eq_dec (unsigned x) 0).
      + rewrite e. auto.
      + pose proof (Z.mod_opp_l_nz (unsigned x) 4294967296).
        assert (4294967296 <> 0) by lia.
        apply H in H0.
        rewrite H0 in l.
        pose proof (Z.mod_small (unsigned x) 4294967296).
        assert (0 <= unsigned x < 4294967296).
        pose proof (unsigned_range_2 x). lia.
        apply H1 in H2. rewrite H2 in l. lia.
        rewrite Z.mod_small. assumption.
        pose proof (unsigned_range_2 x). lia.
    - destruct (Z.eq_dec (unsigned x) 0).
      + lia.
      + rewrite Z.mod_opp_l_nz; try lia.
        rewrite Z.opp_sub_distr.
        rewrite Z.mod_small. lia.
        pose proof (unsigned_range_2 x).
        simplify; lia.
        rewrite Z.mod_small. assumption.
        pose proof (unsigned_range_2 x).
        simplify; lia.
    - destruct (Z.eq_dec (unsigned x) 0).
      + rewrite e in *. rewrite Z.opp_0 in *. rewrite Zmod_0_l in g. lia.
      + rewrite Z.mod_opp_l_nz; try lia.
        rewrite Z.mod_small. lia.
        pose proof (unsigned_range_2 x). lia.
        rewrite Z.mod_small. assumption.
        pose proof (unsigned_range_2 x). lia.
    - destruct (Z.eq_dec (unsigned x) 0).
      + lia.
      + rewrite Z.mod_opp_l_nz in g; try lia.
        rewrite Z.mod_small in g.
        assert (unsigned x < 2147483648) by lia. lia.
        pose proof (unsigned_range_2 x).
        replace max_unsigned with 4294967295 in * by auto. lia.
        rewrite Z.mod_small. assumption.
        pose proof (unsigned_range_2 x).
        replace max_unsigned with 4294967295 in * by auto. lia.
  Qed.

  Lemma neg_divs_distr_l :
    forall x y,
      unsigned x <> 2147483648 ->
      neg (divs x y) = divs (neg x) y.
  Proof.
    intros x y Hhalf. unfold divs, neg.
    set (x' := signed x). set (y' := signed y).
    apply eqm_samerepr.
    apply eqm_trans with (- (Z.quot x' y')).
    auto with ints.
    replace (- (Z.quot x' y')) with (Z.quot (- x') y')
      by (rewrite Zquot.Zquot_opp_l; auto).
    unfold x'.
    rewrite <- neg_signed'.
    auto with ints.
    assumption.
  Qed.

  Lemma neg_signed :
    forall x : int,
      unsigned x <> 2147483648 ->
      signed x < 0 ->
      signed (neg x) >= 0.
  Proof.
    intros.
    rewrite neg_signed'. lia.
    assumption.
  Qed.

  Lemma shl_signed_positive :
    forall y,
      unsigned y <= 30 ->
      signed (shl one y) >= 0.
  Proof.
    intros.
    unfold signed, shl.
    destruct (zlt (unsigned (repr (Z.shiftl (unsigned one) (unsigned y)))) half_modulus).
    - rewrite unsigned_repr.
      + rewrite Z.shiftl_1_l.
        apply Z.le_ge. apply Z.pow_nonneg. lia.
      + rewrite Z.shiftl_1_l. split.
        apply Z.pow_nonneg. lia.
        simplify.
        replace (4294967295) with (2 ^ 32 - 1); try lia.
        transitivity (2 ^ 31); try lia.
        apply Z.pow_le_mono_r; lia.
    - simplify. rewrite Z.shiftl_1_l in g.
      unfold half_modulus, modulus, wordsize,
      Wordsize_32.wordsize in *. unfold two_power_nat in *. simplify.
      unfold Z_mod_modulus in *.
      destruct (2 ^ unsigned y) eqn:?.
      apply Z.ge_le in g. exfalso.
      replace (4294967296 / 2) with (2147483648) in g; auto.
      rewrite Z.shiftl_1_l. rewrite Heqz.
      unfold wordsize in *. unfold Wordsize_32.wordsize in *.
      rewrite Zbits.P_mod_two_p_eq in *.
      replace (4294967296 / 2) with (2147483648) in g; auto.
      rewrite <- Heqz in g.
      rewrite Z.mod_small in g.
      replace (2147483648) with (2 ^ 31) in g.
      pose proof (Z.pow_le_mono_r 2 (unsigned y) 30).
      apply Z.ge_le in g.
      assert (0 < 2) by lia. apply H0 in H1. lia. assumption. lia.
      split. lia. rewrite two_power_nat_equiv.
      apply Z.pow_lt_mono_r; lia.

      pose proof (Zlt_neg_0 p).
      pose proof (Z.pow_nonneg 2 (unsigned y)). rewrite <- Heqz in H0.
      lia.
  Qed.

  Lemma is_power2_shl :
    forall y,
      unsigned y <= 30 ->
      is_power2 (shl one y) = Some y.
  Proof.
    intros.
    unfold is_power2, shl.
    destruct (Zbits.Z_is_power2 (unsigned (repr (Z.shiftl (unsigned one) (unsigned y))))) eqn:?.
    - simplify.
      rewrite Z_mod_modulus_eq in Heqo.
      rewrite Z.mod_small in Heqo. rewrite Z.shiftl_1_l in Heqo.
      rewrite <- two_p_correct in Heqo.
      rewrite Zbits.Z_is_power2_complete in Heqo. inv Heqo.
      rewrite repr_unsigned. auto.
      pose proof (unsigned_range_2 y). lia.
      rewrite Z.shiftl_1_l. unfold modulus, wordsize, Wordsize_32.wordsize.
      rewrite two_power_nat_equiv.
      split. apply Z.pow_nonneg. lia.
      apply Z.pow_lt_mono_r; lia.
    - simplify.
      rewrite Z_mod_modulus_eq in Heqo.
      rewrite Z.mod_small in Heqo. rewrite Z.shiftl_1_l in Heqo.
      rewrite <- two_p_correct in Heqo.
      rewrite Zbits.Z_is_power2_complete in Heqo. discriminate.
      pose proof (unsigned_range_2 y). lia.
      rewrite Z.shiftl_1_l. unfold modulus, wordsize, Wordsize_32.wordsize.
      rewrite two_power_nat_equiv.
      split. apply Z.pow_nonneg. lia.
      apply Z.pow_lt_mono_r; lia.
  Qed.

  Definition shrx_alt (x y : int) : int :=
    if zlt (signed x) 0
    then neg (shru (neg x) y)
    else shru x y.

  Lemma shrx_shrx_alt_equiv_ne :
    forall x y,
      unsigned x <> 2147483648 ->
      unsigned y <= 30 ->
      shrx x y = shrx_alt x y.
  Proof.
    intros x y Hhalf H.
    unfold shrx, shrx_alt, lt.
    destruct (Z_ge_lt_dec (signed x) 0);
      [rewrite zlt_false | rewrite zlt_true];

      repeat lazymatch goal with
             | |- is_power2 _ = Some _ => apply is_power2_shl
             | |- signed (shl one _) >= 0 => apply shl_signed_positive
             | |- signed (neg _) >= 0 => apply neg_signed
             | |- divs _ _ = divu _ _ => apply div_divs_equiv
             | |- divs ?x (shl one ?y) = neg (shru (neg ?x) ?y) =>
               rewrite <- neg_involutive at 1; rewrite neg_divs_distr_l;
                 try assumption; f_equal
             | |- divs ?x (shl one ?y) = shru ?x ?y =>
               let H := fresh "H" in
               pose proof (divu_pow2 x (shl one y) y) as H;
                 rewrite <- H
             end; try assumption.
  Qed.

  Lemma shrx_shrx_alt_equiv_eq :
    forall x y,
      unsigned x = 2147483648 ->
      unsigned y <= 30 ->
      shrx x y = shrx_alt x y.
  Proof.
    intros.
    repeat unfold shrx, shrx_alt, signed, divs, neg.
    replace half_modulus with 2147483648 by auto.
    replace modulus with 4294967296 by auto.
    simplify.
    rewrite !Z_mod_modulus_eq.
    rewrite !H.
    simplify.
    assert (Hshl: Z.shiftl 1 (unsigned y) mod 4294967296 = Z.shiftl 1 (unsigned y)).
    { apply Z.mod_small.
      rewrite Z.shiftl_1_l.
      split.
      apply Z.pow_nonneg. lia.
      replace 4294967296 with (2^32) by auto.
      apply Z.le_lt_trans with (m := 2 ^ 31); try lia.
      apply Z.pow_le_mono_r; lia.
    }
    rewrite !Hshl.
    f_equal.
    assert ((Z.shiftl 1 (unsigned y)) < 2147483648).
    rewrite Z.shiftl_1_l.
    replace 2147483648 with (2^31) by auto.
    apply Z.le_lt_trans with (m := 2 ^ 30); try lia.
    apply Z.pow_le_mono_r; lia.
    destruct (zlt (Z.shiftl 1 (unsigned y)) 2147483648); try lia.
    replace (-2147483648 mod 4294967296) with 2147483648 by auto.
    assert (Hmodeq : Z.shiftr 2147483648 (unsigned y) mod 4294967296
                     = Z.shiftr 2147483648 (unsigned y)).
    { apply Z.mod_small. split.
      apply Z.shiftr_nonneg. lia.
      rewrite Z.shiftr_div_pow2.
      replace 4294967296 with (Z.succ 4294967295); auto.
      apply Zle_lt_succ.
      replace 4294967295 with (4294967295 * (2 ^ unsigned y) / (2 ^ unsigned y)).
      2: {
          apply Z.div_mul.
          pose proof (Z.pow_pos_nonneg 2 (unsigned y)).
          apply not_eq_sym.
          apply Z.le_neq. apply H2; try lia.
          apply unsigned_range_2.
      }

      apply Z.div_le_mono.
      apply Z.pow_pos_nonneg. lia.
      apply unsigned_range_2.
      transitivity 4294967295; try lia.
      apply Z.le_mul_diag_r; try lia.
      replace 1 with (Z.succ 0) by auto.
      apply Z.le_succ_l.
      apply Z.pow_pos_nonneg; try lia.
      apply unsigned_range_2. apply unsigned_range_2.
    }
    rewrite !Hmodeq.
    replace (-2147483648) with (Z.opp 2147483648) by auto.
    rewrite Zquot.Zquot_opp_l.
    f_equal.
    rewrite Zquot.Zquot_Zdiv_pos.
    rewrite Z.shiftr_div_pow2.
    rewrite Z.shiftl_1_l. auto.
    apply unsigned_range_2.
    lia.
    rewrite Z.shiftl_1_l.
    apply Z.lt_le_incl.
    apply Z.pow_pos_nonneg; try lia.
    apply unsigned_range_2.
  Qed.

  Theorem shrx_shrx_alt_equiv :
    forall x y,
      unsigned y <= 30 ->
      shrx x y = shrx_alt x y.
  Proof.
    intros.
    destruct (Z.eq_dec (unsigned x) 2147483648);
    [ apply shrx_shrx_alt_equiv_eq | apply shrx_shrx_alt_equiv_ne]; auto.
  Qed.

End IntExtra.
