Require Import BinInt.
Require Import Lia.
Require Import ZBinary.

From bbv Require Import ZLib.
From compcert Require Import Integers Coqlib.

Require Import Coquplib.

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
      try (simplify; lia || assumption)

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

  Lemma of_int_mod :
    forall x m,
      Int.signed x mod m = 0 ->
      Ptrofs.signed (Ptrofs.of_int x) mod m = 0.
  Proof.
    intros.
    pose proof (Integers.Ptrofs.agree32_of_int eq_refl x) as A.
    pose proof Ptrofs.agree32_signed.
    apply H0 in A; try reflexivity.
    rewrite A. assumption.
  Qed.

  Lemma mul_mod :
    forall x y m,
      0 < m ->
      (m | Ptrofs.modulus) ->
      Ptrofs.signed x mod m = 0 ->
      Ptrofs.signed y mod m = 0 ->
      (Ptrofs.signed (Ptrofs.mul x y)) mod m = 0.
  Proof.
    intros. unfold Ptrofs.mul.
    rewrite Ptrofs.signed_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Ptrofs.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           | [ _ : _ |- context[Ptrofs.unsigned _] ] => rewrite Ptrofs.unsigned_signed
           end; try (simplify; lia); ptrofs_mod_tac m.
  Qed.

  Lemma add_mod :
    forall x y m,
      0 < m ->
      (m | Ptrofs.modulus) ->
      Ptrofs.signed x mod m = 0 ->
      Ptrofs.signed y mod m = 0 ->
      (Ptrofs.signed (Ptrofs.add x y)) mod m = 0.
  Proof.
    intros. unfold Ptrofs.add.
    rewrite Ptrofs.signed_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Ptrofs.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           | [ _ : _ |- context[Ptrofs.unsigned _] ] => rewrite Ptrofs.unsigned_signed
           end; try (simplify; lia); ptrofs_mod_tac m.
  Qed.

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

  Lemma mul_unsigned :
    forall x y,
      Ptrofs.mul x y =
      Ptrofs.repr (Ptrofs.unsigned x * Ptrofs.unsigned y).
  Proof.
    intros; unfold Ptrofs.mul.
    apply Ptrofs.eqm_samerepr.
    apply Ptrofs.eqm_mult; exists 0; lia.
  Qed.
End PtrofsExtra.

Module IntExtra.

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
      try (simplify; lia || assumption)

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

  Lemma mul_mod :
    forall x y m,
      0 < m ->
      (m | Int.modulus) ->
      Int.signed x mod m = 0 ->
      Int.signed y mod m = 0 ->
      (Int.signed (Int.mul x y)) mod m = 0.
  Proof.
    intros. unfold Int.mul.
    rewrite Int.signed_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Int.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           | [ _ : _ |- context[Int.unsigned _] ] => rewrite Int.unsigned_signed
           end; try (simplify; lia); int_mod_tac m.
  Qed.

  Lemma add_mod :
    forall x y m,
      0 < m ->
      (m | Int.modulus) ->
      Int.signed x mod m = 0 ->
      Int.signed y mod m = 0 ->
      (Int.signed (Int.add x y)) mod m = 0.
  Proof.
    intros. unfold Int.add.
    rewrite Int.signed_repr_eq.

    repeat match goal with
           | [ _ : _ |- context[if ?x then _ else _] ] => destruct x
           | [ _ : _ |- context[_ mod Int.modulus mod m] ] =>
             rewrite <- Zmod_div_mod; try lia; try assumption
           | [ _ : _ |- context[Int.unsigned _] ] => rewrite Int.unsigned_signed
           end; try (simplify; lia); int_mod_tac m.
  Qed.
End IntExtra.
