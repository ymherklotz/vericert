Require Import ZArith.
Require Import Lia.

Local Open Scope Z_scope.

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
