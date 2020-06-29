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

Lemma list_set_spec3 {A : Type} :
  forall l i1 i2 (x : A),
    i1 <> i2 ->
    nth_error (list_set i1 x l) i2 = nth_error l i2.
Proof.
  induction l; intros; destruct i1; destruct i2; simplify; try lia; try reflexivity; firstorder.
Qed.
Hint Resolve list_set_spec3 : array.

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

Lemma array_set_len {A : Type} :
  forall a i (x : A),
    a.(arr_length) = (array_set i x a).(arr_length).
Proof.
  unfold array_set. simplify. reflexivity.
Qed.

Definition array_get_error {A : Type} (i : nat) (a : Array A) : option A :=
  nth_error a.(arr_contents) i.

Lemma array_get_error_equal {A : Type} :
  forall (a b : Array A) i,
    a.(arr_contents) = b.(arr_contents) ->
    array_get_error i a = array_get_error i b.
Proof.
  unfold array_get_error. congruence.
Qed.

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

  destruct (nth_error (arr_contents a) i) eqn:EQ; try contradiction; eauto.
Qed.

Lemma array_get_error_set_bound {A : Type} :
  forall (a : Array A) i x,
    i < a.(arr_length) -> array_get_error i (array_set i x a) = Some x.
Proof.
  intros.

  unfold array_get_error.
  eauto with array.
Qed.

Lemma array_gso {A : Type} :
  forall (a : Array A) i1 i2 x,
    i1 <> i2 ->
    array_get_error i2 (array_set i1 x a) = array_get_error i2 a.
Proof.
  intros.

  unfold array_get_error.
  unfold array_set.
  simplify.
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

Lemma array_get_get_error {A : Type} :
  forall (a : Array A) i x d,
    array_get_error i a = Some x ->
    array_get i d a = x.
Proof.
  intros.
  unfold array_get.
  unfold array_get_error in H.
  auto using nth_error_nth.
Qed.

(** Tail recursive version of standard library function. *)
Fixpoint list_repeat' {A : Type} (acc : list A) (a : A) (n : nat) : list A :=
  match n with
  | O => acc
  | S n => list_repeat' (a::acc) a n
  end.

Lemma list_repeat'_len {A : Type} : forall (a : A) n l,
    length (list_repeat' l a n) = (n + Datatypes.length l)%nat.
Proof.
  induction n; intros; simplify; try reflexivity.

  specialize (IHn (a :: l)).
  rewrite IHn.
  simplify.
  lia.
Qed.

Lemma list_repeat'_app {A : Type} : forall (a : A) n l,
    list_repeat' l a n = list_repeat' [] a n ++ l.
Proof.
  induction n; intros; simplify; try reflexivity.

  pose proof IHn.
  specialize (H (a :: l)).
  rewrite H. clear H.
  specialize (IHn (a :: nil)).
  rewrite IHn. clear IHn.
  remember (list_repeat' [] a n) as l0.

  rewrite <- app_assoc.
  f_equal.
Qed.

Lemma list_repeat'_head_tail {A : Type} : forall n (a : A),
  a :: list_repeat' [] a n = list_repeat' [] a n ++ [a].
Proof.
  induction n; intros; simplify; try reflexivity.
  rewrite list_repeat'_app.

  replace (a :: list_repeat' [] a n ++ [a]) with (list_repeat' [] a n ++ [a] ++ [a]).
  2: { rewrite app_comm_cons. rewrite IHn; auto.
       rewrite app_assoc. reflexivity. }
  rewrite app_assoc. reflexivity.
Qed.

Lemma list_repeat'_cons {A : Type} : forall (a : A) n,
    list_repeat' [a] a n = a :: list_repeat' [] a n.
Proof.
  intros.

  rewrite list_repeat'_head_tail; auto.
  apply list_repeat'_app.
Qed.

Definition list_repeat {A : Type} : A -> nat -> list A := list_repeat' nil.

Lemma list_repeat_len {A : Type} : forall n (a : A), length (list_repeat a n) = n.
Proof.
  intros.
  unfold list_repeat.
  rewrite list_repeat'_len.
  simplify. lia.
Qed.

Lemma dec_list_repeat_spec {A : Type} : forall n (a : A) a',
    (forall x x' : A, {x' = x} + {~ x' = x}) ->
    In a' (list_repeat a n) -> a' = a.
Proof.
  induction n; intros; simplify; try contradiction.

  unfold list_repeat in *.
  simplify.

  rewrite list_repeat'_app in H.
  pose proof (X a a').
  destruct H0; auto.

  (* This is actually a degenerate case, not an unprovable goal. *)
  pose proof (in_app_or (list_repeat' [] a n) ([a])).
  apply H0 in H. invert H.

  - eapply IHn in X; eassumption.
  - invert H1; contradiction.
Qed.

Lemma list_repeat_head_tail {A : Type} : forall n (a : A),
    a :: list_repeat a n = list_repeat a n ++ [a].
Proof.
  unfold list_repeat. apply list_repeat'_head_tail.
Qed.

Lemma list_repeat_cons {A : Type} : forall n (a : A),
    list_repeat a (S n) = a :: list_repeat a n.
Proof.
  intros.

  unfold list_repeat.
  apply list_repeat'_cons.
Qed.

Lemma list_repeat_lookup {A : Type} :
  forall n i (a : A),
    i < n ->
    nth_error (list_repeat a n) i = Some a.
Proof.
  induction n; intros.

  destruct i; simplify; lia.

  rewrite list_repeat_cons.
  destruct i; simplify; firstorder.
Qed.

Definition arr_repeat {A : Type} (a : A) (n : nat) : Array A := make_array (list_repeat a n).

Fixpoint list_combine {A B C : Type} (f : A -> B -> C) (x : list A) (y : list B) : list C :=
  match x, y with
  | a :: t, b :: t' => f a b :: list_combine f t t'
  | _, _ => nil
  end.

Lemma list_combine_length {A B C : Type} (f : A -> B -> C) : forall (x : list A) (y : list B),
    length (list_combine f x y) = min (length x) (length y).
Proof.
  induction x; intros; simplify; try reflexivity.

  destruct y; simplify; auto.
Qed.

Definition combine {A B C : Type} (f : A -> B -> C) (x : Array A) (y : Array B) : Array C :=
  make_array (list_combine f x.(arr_contents) y.(arr_contents)).

Lemma combine_length {A B C: Type} : forall x y (f : A -> B -> C),
    x.(arr_length) = y.(arr_length) -> arr_length (combine f x y) = x.(arr_length).
Proof.
  intros.

  unfold combine.
  unfold make_array.
  simplify.

  rewrite <- (arr_wf x) in *.
  rewrite <- (arr_wf y) in *.

  destruct (arr_contents x); simplify.
  - reflexivity.
  - destruct (arr_contents y); simplify.
    f_equal.
    rewrite list_combine_length.
    destruct (Min.min_dec (length l) (length l0)); congruence.
Qed.
