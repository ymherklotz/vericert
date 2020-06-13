Set Implicit Arguments.

Require Import Lia.
Require Import Coquplib.
From Coq Require Import Lists.List Datatypes.

Import ListNotations.

Local Open Scope nat_scope.

Record Array (A : Type) : Type :=
  mk_array
    { arr_contents : list A
    ; arr_length : nat
    ; arr_wf : length arr_contents = arr_length
    }.

Definition make_array {A : Type} (l : list A) : Array A :=
  @mk_array A l (length l) eq_refl.

Fixpoint list_set {A : Type} (i : nat) (x : A) (l : list A) {struct l} : list A :=
  match i, l with
  | _, nil => nil
  | S n, h :: t => h :: list_set n x t
  | O, h :: t => x :: t
  end.

Lemma list_set_spec1 {A : Type} :
  forall l i (x : A),
    i < length l -> nth_error (list_set i x l) i = Some x.
Proof.
  induction l; intros; destruct i; simplify; try lia; try reflexivity; firstorder.
Qed.
Hint Resolve list_set_spec1 : array.

Lemma list_set_spec2 {A : Type} :
  forall l i (x : A) d,
    i < length l -> nth i (list_set i x l) d = x.
Proof.
  induction l; intros; destruct i; simplify; try lia; try reflexivity; firstorder.
Qed.
Hint Resolve list_set_spec2 : array.

Lemma array_set_wf {A : Type} :
  forall l ln i (x : A),
    length l = ln -> length (list_set i x l) = ln.
Proof.
  induction l; intros; destruct i; auto.

  invert H; simplify; auto.
Qed.

Definition array_set {A : Type} (i : nat) (x : A) (a : Array A) :=
  let l := a.(arr_contents) in
  let ln := a.(arr_length) in
  let WF := a.(arr_wf) in
  @mk_array A (list_set i x l) ln (@array_set_wf A l ln i x WF).

Lemma array_set_spec1 {A : Type} :
  forall a i (x : A),
    i < a.(arr_length) -> nth_error ((array_set i x a).(arr_contents)) i = Some x.
Proof.
  intros.

  rewrite <- a.(arr_wf) in H.
  unfold array_set. simplify.
  eauto with array.
Qed.
Hint Resolve array_set_spec1 : array.

Lemma array_set_spec2 {A : Type} :
  forall a i (x : A) d,
    i < a.(arr_length) -> nth i ((array_set i x a).(arr_contents)) d = x.
Proof.
  intros.

  rewrite <- a.(arr_wf) in H.
  unfold array_set. simplify.
  eauto with array.
Qed.
Hint Resolve array_set_spec2 : array.

Definition array_get_error {A : Type} (i : nat) (a : Array A) : option A :=
  nth_error a.(arr_contents) i.

Lemma array_get_error_bound {A : Type} :
  forall (a : Array A) i,
    i < a.(arr_length) -> exists x, array_get_error i a = Some x.
Proof.
  intros.

  rewrite <- a.(arr_wf) in H.
  assert (~ length (arr_contents a) <= i) by lia.

  pose proof (nth_error_None a.(arr_contents) i).
  apply not_iff_compat in H1.
  apply <- H1 in H0.

  destruct (nth_error (arr_contents a) i ) eqn:EQ; try contradiction; eauto.
Qed.

Lemma array_get_error_set_bound {A : Type} :
  forall (a : Array A) i x,
    i < a.(arr_length) -> array_get_error i (array_set i x a) = Some x.
Proof.
  intros.

  unfold array_get_error.
  eauto with array.
Qed.

Definition array_get {A : Type} (i : nat) (x : A) (a : Array A) : A :=
  nth i a.(arr_contents) x.

Lemma array_get_set_bound {A : Type} :
  forall (a : Array A) i x d,
    i < a.(arr_length) -> array_get i d (array_set i x a) = x.
Proof.
  intros.

  unfold array_get.
  info_eauto with array.
Qed.
