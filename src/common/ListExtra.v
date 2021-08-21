Require Export Coq.Lists.List.

Require Import Coq.micromega.Lia.
Require Import vericert.common.Vericertlib.

From Hammer Require Import Tactics.

Lemma nth_error_length : forall {A} (l : list A) n x,
    nth_error l n = Some x -> (n < length l)%nat.
Proof.
  induction l; intros; simpl in *.
  - destruct n; crush.
  - destruct n; crush.
    edestruct IHl; eauto with arith.
Qed.

Lemma length_nth_error : forall {A} (l : list A) n,
    (n < length l)%nat -> exists x, nth_error l n = Some x.
Proof.
  induction l; intros; simpl in *.
  - lia.
  - destruct n; crush; eauto with arith.
Qed.

Lemma combine_split : forall {A B} (l : list (A * B)),
    List.combine (fst (List.split l)) (snd (List.split l)) = l.
Proof. hfcrush use: split_combine unfold: fst, snd inv: prod. Qed.
