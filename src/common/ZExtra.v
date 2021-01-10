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

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module ZLib.

Lemma mod2_cases: forall (n: Z), n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros. pose proof (Z.mod_pos_bound n 2). lia.
Qed.

Lemma div_mul_undo: forall a b,
    b <> 0 ->
    a mod b = 0 ->
    a / b * b = a.
Proof.
  intros.
  pose proof Z.div_mul_cancel_l as A. specialize (A a 1 b).
  replace (b * 1) with b in A by lia.
  rewrite Z.div_1_r in A.
  rewrite Z.mul_comm.
  rewrite <- Z.divide_div_mul_exact; try assumption.
  - apply A; congruence.
  - apply Z.mod_divide; assumption.
Qed.

Lemma mod_0_r: forall (m: Z),
    m mod 0 = 0.
Proof.
  intros. destruct m; reflexivity.
Qed.

Lemma sub_mod_0: forall (a b m: Z),
    a mod m = 0 ->
    b mod m = 0 ->
    (a - b) mod m = 0.
Proof.
  intros *. intros E1 E2.
  rewrite Zminus_mod.
  rewrite E1. rewrite E2.
  reflexivity.
Qed.

Lemma add_mod_0: forall a b m : Z,
    a mod m = 0 ->
    b mod m = 0 ->
    (a + b) mod m = 0.
Proof.
  intros *. intros E1 E2.
  rewrite Zplus_mod.
  rewrite E1. rewrite E2.
  reflexivity.
Qed.

Lemma Z_mod_mult': forall a b : Z,
    (a * b) mod a = 0.
Proof.
  intros. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma mod_add_r: forall a b,
    b <> 0 ->
    (a + b) mod b = a mod b.
Proof.
  intros. rewrite <- Z.add_mod_idemp_r by lia.
  rewrite Z.mod_same by lia.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma mod_pow2_same_cases: forall a n,
    a mod 2 ^ n = a ->
    2 ^ n = 0 /\ a = 0 \/ 0 <= a < 2 ^ n.
Proof.
  intros.
  assert (n < 0 \/ 0 <= n) as C by lia. destruct C as [C | C].
  - left. rewrite (Z.pow_neg_r 2 n C) in *. rewrite mod_0_r in H. auto.
  - right.
    rewrite <- H. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
Qed.

Lemma mod_pow2_same_bounds: forall a n,
    a mod 2 ^ n = a ->
    0 <= n ->
    0 <= a < 2 ^ n.
Proof.
  intros. rewrite <- H. apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma pow2_nonneg: forall n,
    0 <= 2 ^ n.
Proof.
  intros. apply Z.pow_nonneg. lia.
Qed.

Lemma pow2_pos: forall n,
    0 <= n ->
    0 < 2 ^ n.
Proof.
  intros. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma pow2_times2: forall i,
    0 < i ->
    2 ^ i = 2 * 2 ^ (i - 1).
Proof.
  intros.
  rewrite <- Z.pow_succ_r by lia.
  f_equal.
  lia.
Qed.

Lemma pow2_div2: forall i,
    0 <= i ->
    2 ^ (i - 1) = 2 ^ i / 2.
Proof.
  intros.
  assert (i = 0 \/ 0 < i) as C by lia. destruct C as [C | C].
  - subst. reflexivity.
  - rewrite Z.pow_sub_r by lia.
    reflexivity.
Qed.

Lemma div_mul_undo_le: forall a b,
    0 <= a ->
    0 < b ->
    a / b * b <= a.
Proof.
  intros.
  pose proof (Zmod_eq_full a b) as P.
  pose proof (Z.mod_bound_pos a b) as Q.
  lia.
Qed.

Lemma testbit_true_nonneg: forall a i,
    0 <= a ->
    0 <= i ->
    Z.testbit a i = true ->
    2 ^ i <= a.
Proof.
  intros.
  apply Z.testbit_true in H1; [|assumption].
  pose proof (pow2_pos i H0).
  eapply Z.le_trans; [| apply (div_mul_undo_le a (2 ^ i)); lia].
  replace (2 ^ i) with (1 * 2 ^ i) at 1 by lia.
  apply Z.mul_le_mono_nonneg_r; [lia|].
  pose proof (Z.div_pos a (2 ^ i)).
  assert (a / 2 ^ i <> 0); [|lia].
  intro E. rewrite E in H1. cbv in H1. discriminate H1.
Qed.

Lemma range_div_pos: forall a b c d,
    0 < d ->
    a <= b <= c ->
    a / d <= b / d <= c / d.
Proof.
  intuition idtac.
  - apply (Z.div_le_mono _ _ _ H H1).
  - apply (Z.div_le_mono _ _ _ H H2).
Qed.

Lemma testbit_true_nonneg': forall a i,
    0 <= i ->
    2 ^ i <= a < 2 ^ (i + 1) ->
    Z.testbit a i = true.
Proof.
  intros.
  apply Z.testbit_true; [assumption|].
  destruct H0 as [A B].
  pose proof (pow2_pos i H) as Q.
  apply (Z.div_le_mono _ _ _ Q) in A.
  rewrite Z_div_same in A by lia.
  pose proof (Z.div_lt_upper_bound a (2 ^ i) 2 Q) as P.
  rewrite Z.mul_comm in P.
  replace i with (i + 1 - 1) in P by lia.
  rewrite <- pow2_times2 in P by lia.
  specialize (P B).
  replace (i + 1 - 1) with i in P by lia.
  replace (a / 2 ^ i) with 1 by lia.
  reflexivity.
Qed.

Lemma testbit_false_nonneg: forall a i,
    0 <= a < 2 ^ i ->
    0 < i ->
    Z.testbit a (i - 1) = false ->
    a < 2 ^ (i - 1).
Proof.
  intros.
  assert (2 ^ (i - 1) <= a < 2 ^ i \/ a < 2 ^ (i - 1)) as C by lia.
  destruct C as [C | C]; [exfalso|assumption].
  assert (Z.testbit a (i - 1) = true); [|congruence].
  replace i with (i - 1 + 1) in C at 2 by lia.
  apply testbit_true_nonneg'; lia.
Qed.

Lemma signed_bounds_to_sz_pos: forall sz n,
    - 2 ^ (sz - 1) <= n < 2 ^ (sz - 1) ->
    0 < sz.
Proof.
  intros.
  assert (0 < sz \/ sz - 1 < 0) as C by lia.
  destruct C as [C | C]; [assumption|exfalso].
  rewrite Z.pow_neg_r in H by assumption.
  lia.
Qed.

Lemma two_digits_encoding_inj_lo: forall base a b c d: Z,
  0 <= b < base ->
  0 <= d < base ->
  base * a + b = base * c + d ->
  b = d.
Proof.
  intros.
  pose proof Z.mod_unique as P.
  specialize P with (b := base) (q := c) (r := d).
  specialize P with (2 := H1).
  rewrite P by lia.
  rewrite <- Z.add_mod_idemp_l by lia.
  rewrite Z.mul_comm.
  rewrite Z.mod_mul by lia.
  rewrite Z.add_0_l.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma two_digits_encoding_inj_hi: forall base a b c d: Z,
  0 <= b < base ->
  0 <= d < base ->
  base * a + b = base * c + d ->
  a = c.
Proof.
  intros. nia.
Qed.

Lemma Z_to_nat_neg: forall (n: Z),
    n < 0 ->
    Z.to_nat n = 0%nat.
Proof.
  intros. destruct n; (lia||reflexivity).
Qed.

End ZLib.

Module ZExtra.

  Lemma mod_0_bounds :
    forall x y m,
      0 < m ->
      x mod m = 0 ->
      y mod m = 0 ->
      x <> y ->
      x + m > y ->
      y + m <= x.
  Proof.
    intros x y m.
    intros POS XMOD YMOD NEQ H.
    destruct (Z_le_gt_dec (y + m) x); eauto.

    apply Znumtheory.Zmod_divide in YMOD; try lia.
    apply Znumtheory.Zmod_divide in XMOD; try lia.
    inversion XMOD as [x']; subst; clear XMOD.
    inversion YMOD as [y']; subst; clear YMOD.

    assert (x' <> y') as NEQ' by lia; clear NEQ.

    rewrite <- Z.mul_succ_l in H.
    rewrite <- Z.mul_succ_l in g.
    apply Zmult_gt_reg_r in H;
      apply Zmult_gt_reg_r in g; lia.
  Qed.

  Lemma Ple_not_eq :
    forall x y,
    (x < y)%positive -> x <> y.
  Proof. lia. Qed.

  Lemma Pge_not_eq :
    forall x y,
    (y < x)%positive -> x <> y.
  Proof. lia. Qed.

  Lemma Ple_Plt_Succ :
    forall x y n,
    (x <= y)%positive -> (x < y + n)%positive.
  Proof. lia. Qed.

End ZExtra.
