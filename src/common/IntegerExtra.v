Require Import BinInt.
Require Import Lia.
Require Import ZBinary.

From bbv Require Import ZLib.
From compcert Require Import Integers Coqlib.

Require Import Coquplib.

Local Open Scope Z_scope.

Module PtrofsExtra.

  Lemma mul_divs :
    forall x y,
      0 <= Ptrofs.signed y ->
      0 < Ptrofs.signed x ->
      Ptrofs.signed y mod Ptrofs.signed x = 0 ->
      (Integers.Ptrofs.mul x (Integers.Ptrofs.divs y x)) = y.
  Proof.
    intros.

    pose proof (Ptrofs.mods_divs_Euclid y x).
    pose proof (Zquot.Zrem_Zmod_zero (Ptrofs.signed y) (Ptrofs.signed x)).
    apply <- H3 in H1; try lia; clear H3.
    unfold Ptrofs.mods in H2.
    rewrite H1 in H2.
    replace (Ptrofs.repr 0) with (Ptrofs.zero) in H2 by reflexivity.
    rewrite Ptrofs.add_zero in H2.
    rewrite Ptrofs.mul_commut.
    congruence.
  Qed.

  Lemma Z_div_distr_add :
    forall x y z,
      x mod z = 0 ->
      y mod z = 0 ->
      z <> 0 ->
      x / z + y / z = (x + y) / z.
  Proof.
    intros.

    assert ((x + y) mod z = 0).
    { rewrite <- Z.add_mod_idemp_l; try assumption.
      rewrite H. assumption. }

    rewrite <- Z.mul_cancel_r with (p := z); try assumption.
    rewrite Z.mul_add_distr_r.
    repeat rewrite ZLib.div_mul_undo; lia.
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

  Lemma mul_repr :
    forall x y,
      Ptrofs.min_signed <= y <= Ptrofs.max_signed ->
      Ptrofs.min_signed <= x <= Ptrofs.max_signed ->
      Ptrofs.mul (Ptrofs.repr y) (Ptrofs.repr x) = Ptrofs.repr (x * y).
  Proof.
    intros; unfold Ptrofs.mul.
    destruct (Z_ge_lt_dec x 0); destruct (Z_ge_lt_dec y 0).

    - f_equal.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Z.mod_small; simplify; lia.

    - assert (Ptrofs.lt (Ptrofs.repr y) Ptrofs.zero = true).
      {
        unfold Ptrofs.lt.
        rewrite Ptrofs.signed_repr; auto.
        rewrite Ptrofs.signed_zero.
        destruct (zlt y 0); try lia; auto.
      }

      rewrite Ptrofs.unsigned_signed with (n := Ptrofs.repr y).
      rewrite H1.
      rewrite Ptrofs.signed_repr; auto.
      rewrite Ptrofs.unsigned_repr_eq.
      rewrite Z.mod_small; simplify; try lia.
      rewrite Z.mul_add_distr_r.
      apply Ptrofs.eqm_samerepr.
      exists x. simplify. lia.

    - assert (Ptrofs.lt (Ptrofs.repr x) Ptrofs.zero = true).
      {
        unfold Ptrofs.lt.
        rewrite Ptrofs.signed_repr; auto.
        rewrite Ptrofs.signed_zero.
        destruct (zlt x 0); try lia; auto.
      }

      rewrite Ptrofs.unsigned_signed with (n := Ptrofs.repr x).
      rewrite H1.
      rewrite Ptrofs.signed_repr; auto.
      rewrite Ptrofs.unsigned_repr_eq.
      rewrite Z.mod_small; simplify; try lia.
      rewrite Z.mul_add_distr_l.
      apply Ptrofs.eqm_samerepr.
      exists y. simplify. lia.

    - assert (Ptrofs.lt (Ptrofs.repr x) Ptrofs.zero = true).
      {
        unfold Ptrofs.lt.
        rewrite Ptrofs.signed_repr; auto.
        rewrite Ptrofs.signed_zero.
        destruct (zlt x 0); try lia; auto.
      }
      assert (Ptrofs.lt (Ptrofs.repr y) Ptrofs.zero = true).
      {
        unfold Ptrofs.lt.
        rewrite Ptrofs.signed_repr; auto.
        rewrite Ptrofs.signed_zero.
        destruct (zlt y 0); try lia; auto.
      }
      rewrite Ptrofs.unsigned_signed with (n := Ptrofs.repr x).
      rewrite Ptrofs.unsigned_signed with (n := Ptrofs.repr y).
      rewrite H2.
      rewrite H1.
      repeat rewrite Ptrofs.signed_repr; auto.
      replace ((y + Ptrofs.modulus) * (x + Ptrofs.modulus)) with
          (x * y + (x + y + Ptrofs.modulus) * Ptrofs.modulus) by lia.
      apply Ptrofs.eqm_samerepr.
      exists (x + y + Ptrofs.modulus). lia.
  Qed.
End PtrofsExtra.

Module IntExtra.
  Lemma mul_unsigned :
    forall x y,
      Int.mul x y =
      Int.repr (Int.unsigned x * Int.unsigned y).
  Proof.
    intros; unfold Int.mul.
    apply Int.eqm_samerepr.
    apply Int.eqm_mult; exists 0; lia.
  Qed.

  Lemma mul_repr :
    forall x y,
      Int.min_signed <= y <= Int.max_signed ->
      Int.min_signed <= x <= Int.max_signed ->
      Int.mul (Int.repr y) (Int.repr x) = Int.repr (x * y).
  Proof.
    intros; unfold Int.mul.
    destruct (Z_ge_lt_dec x 0); destruct (Z_ge_lt_dec y 0).

    - f_equal.
      repeat rewrite Int.unsigned_repr_eq.
      repeat rewrite Z.mod_small; simplify; lia.

    - assert (Int.lt (Int.repr y) Int.zero = true).
      {
        unfold Int.lt.
        rewrite Int.signed_repr; auto.
        rewrite Int.signed_zero.
        destruct (zlt y 0); try lia; auto.
      }

      rewrite Int.unsigned_signed with (n := Int.repr y).
      rewrite H1.
      rewrite Int.signed_repr; auto.
      rewrite Int.unsigned_repr_eq.
      rewrite Z.mod_small; simplify; try lia.
      rewrite Z.mul_add_distr_r.
      apply Int.eqm_samerepr.
      exists x. simplify. lia.

    - assert (Int.lt (Int.repr x) Int.zero = true).
      {
        unfold Int.lt.
        rewrite Int.signed_repr; auto.
        rewrite Int.signed_zero.
        destruct (zlt x 0); try lia; auto.
      }

      rewrite Int.unsigned_signed with (n := Int.repr x).
      rewrite H1.
      rewrite Int.signed_repr; auto.
      rewrite Int.unsigned_repr_eq.
      rewrite Z.mod_small; simplify; try lia.
      rewrite Z.mul_add_distr_l.
      apply Int.eqm_samerepr.
      exists y. simplify. lia.

    - assert (Int.lt (Int.repr x) Int.zero = true).
      {
        unfold Int.lt.
        rewrite Int.signed_repr; auto.
        rewrite Int.signed_zero.
        destruct (zlt x 0); try lia; auto.
      }
      assert (Int.lt (Int.repr y) Int.zero = true).
      {
        unfold Int.lt.
        rewrite Int.signed_repr; auto.
        rewrite Int.signed_zero.
        destruct (zlt y 0); try lia; auto.
      }
      rewrite Int.unsigned_signed with (n := Int.repr x).
      rewrite Int.unsigned_signed with (n := Int.repr y).
      rewrite H2.
      rewrite H1.
      repeat rewrite Int.signed_repr; auto.
      replace ((y + Int.modulus) * (x + Int.modulus)) with
          (x * y + (x + y + Int.modulus) * Int.modulus) by lia.
      apply Int.eqm_samerepr.
      exists (x + y + Int.modulus). lia.
  Qed.
End IntExtra.

Lemma mul_of_int :
  forall x y,
    0 <= x < Integers.Ptrofs.modulus ->
    Integers.Ptrofs.mul (Integers.Ptrofs.repr x) (Integers.Ptrofs.of_int y) =
    Integers.Ptrofs.of_int (Integers.Int.mul (Integers.Int.repr x) y).
Proof.
  intros.
  pose proof (Integers.Ptrofs.agree32_of_int eq_refl y) as A.
  pose proof (Integers.Ptrofs.agree32_to_int eq_refl (Integers.Ptrofs.repr x)) as B.
  exploit Integers.Ptrofs.agree32_mul; [> reflexivity | exact B | exact A | intro C].
  unfold Integers.Ptrofs.to_int in C.
  unfold Integers.Ptrofs.of_int in C.
  rewrite Integers.Ptrofs.unsigned_repr_eq in C.
  rewrite Z.mod_small in C; auto.
  symmetry.
  apply Integers.Ptrofs.agree32_of_int_eq; auto.
Qed.
