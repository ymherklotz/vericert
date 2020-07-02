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
End IntExtra.
