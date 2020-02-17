From Coq Require Import Lists.List Strings.String.
From Coq Require Import
Structures.OrderedTypeEx
FSets.FMapList
Program.Basics
PeanoNat.
From CoqUp.Common Require Import Helper Tactics Show.

Import ListNotations.

Module Map := FMapList.Make String_as_OT.

Inductive value : Type :=
| VBool (b : bool)
| VArray (l : list value).

Definition cons_value (a b : value) : value :=
  match a, b with
  | VBool _, VArray b' => VArray (a :: b')
  | VArray a', VBool _ => VArray (List.concat [a'; [b]])
  | VArray a', VArray b' => VArray (List.concat [a'; b'])
  | _, _ => VArray [a; b]
  end.

(** * Conversion to and from value *)

Fixpoint nat_to_value' (sz n : nat) : value :=
  match sz with
  | 0 => VArray []
  | S sz' =>
    if Nat.even n then
      cons_value (VBool false) (nat_to_value' sz' (Nat.div n 2))
    else
      cons_value (VBool true) (nat_to_value' sz' (Nat.div n 2))
  end.

Definition nat_to_value (n : nat) : value :=
  nat_to_value' ((Nat.log2 n) + 1) n.

Definition state : Type := Map.t value * Map.t value.

Inductive binop : Type :=
| Plus
| Minus
| Times
| Divide
| LT
| GT
| LE
| GE
| Eq
| And
| Or
| Xor.

Inductive expr : Type :=
| Lit (n : value)
| Var (s : string)
| Neg (a : expr)
| BinOp (op : binop) (a1 a2 : expr)
| Ternary (c t f : expr).

Inductive stmnt : Type :=
| Skip
| Block (s : list stmnt)
| Cond (c : expr) (st sf : stmnt)
| Case (c : expr) (b : list (expr * stmnt))
| Blocking (a b : expr)
| Nonblocking (a b : expr).

Inductive verilog : Type := Verilog (s : list stmnt).

Definition verilog_example := Verilog [Block [Nonblocking (Var "hello") (BinOp Plus (Lit (nat_to_value 40)) (Lit (nat_to_value 20))); Cond (BinOp LE (Lit (nat_to_value 2)) (Lit (nat_to_value 3))) (Blocking (Var "Another") (BinOp Times (Lit (nat_to_value 20)) (Lit (nat_to_value 500)))) Skip]; Block []].

Coercion VBool : bool >-> value.
Coercion Lit : value >-> expr.
Coercion Var : string >-> expr.

Definition value_is_bool (v : value) : bool :=
  match v with
  | VBool _ => true
  | VArray _ => false
  end.

Definition value_is_array : value -> bool := compose negb value_is_bool.

Definition flat_value (v : value) : bool :=
  match v with
  | VBool _ => true
  | VArray l => forallb value_is_bool l
  end.

Inductive value_is_boolP : value -> Prop :=
| ValIsBool : forall b : bool, value_is_boolP (VBool b).

Inductive value_is_arrayP : value -> Prop :=
| ValIsArray : forall v : list value, value_is_arrayP (VArray v).

Inductive flat_valueP : value -> Prop :=
| FLV0 : forall b : bool, flat_valueP (VBool b)
| FLVA : forall l : list value,
    Forall (value_is_boolP) l -> flat_valueP (VArray l).

Lemma value_is_bool_equiv :
  forall v, value_is_boolP v <-> value_is_bool v = true.
Proof.
  split; intros.
  - inversion H. trivial.
  - destruct v. constructor. unfold value_is_bool in H. discriminate.
Qed.

Lemma value_is_array_equiv :
  forall v, value_is_arrayP v <-> value_is_array v = true.
Proof.
  split; intros.
  - inversion H. trivial.
  - destruct v; try constructor. unfold value_is_array in H.
    unfold compose, value_is_bool, negb in H. discriminate.
Qed.

Lemma flat_value_equiv :
  forall v, flat_valueP v <-> flat_value v = true.
Proof.
  split; intros.
  - unfold flat_value. inversion H. subst. trivial.
    + rewrite Forall_forall in H0. rewrite forallb_forall. intros. subst.
      apply value_is_bool_equiv. apply H0. assumption.
  - destruct v. constructor. constructor. unfold flat_value in H.
    rewrite Forall_forall. rewrite forallb_forall in H. intros. apply value_is_bool_equiv.
    apply H. assumption.
Qed.

Fixpoint value_to_nat' (i : nat) (v : value) : option nat :=
  match i, v with
  | _, VBool b => Some (Nat.b2n b)
  | _, VArray [VBool b] => Some (Nat.b2n b)
  | S i', VArray ((VBool b) :: l) =>
    Option.map (compose (Nat.add (Nat.b2n b)) (Mult.tail_mult 2)) (value_to_nat' i' (VArray l))
  | _, _ => None
  end.

Definition value_length (v : value) : nat :=
  match v with
  | VBool _ => 1
  | VArray l => Datatypes.length l
  end.

Definition value_to_nat (v : value) : option nat :=
  value_to_nat' (value_length v) v.

Lemma empty_is_flat : flat_valueP (VArray []).
Proof.
  constructor. apply Forall_forall. intros. inversion H.
Qed.

Lemma check_5_is_101 :
  value_to_nat (VArray [VBool true; VBool false; VBool true]) = Some 5.
Proof. reflexivity. Qed.

Lemma cons_value_flat :
  forall (b : bool) (v : value),
    flat_valueP v -> flat_valueP (cons_value (VBool b) v).
Proof.
  intros. unfold cons_value. destruct v.
  - constructor. apply Forall_forall. intros.
    inversion H0; subst. constructor.
    inversion H1; subst. constructor.
    inversion H2.
  - intros. inversion H. inversion H1; subst; constructor.
    + apply Forall_forall. intros.
      inversion H0; subst. constructor.
      inversion H2.
    + repeat constructor. assumption. assumption.
Qed.

Lemma nat_to_value'_is_flat :
  forall (sz n : nat),
    flat_valueP (nat_to_value' sz n).
Proof.
  induction sz; intros.
  - subst. apply empty_is_flat.
  - unfold_rec nat_to_value'.
    destruct (Nat.even n); apply cons_value_flat; apply IHsz.
Qed.

Lemma nat_to_value_is_flat :
  forall (sz n : nat),
    flat_valueP (nat_to_value n).
Proof.
  intros. unfold nat_to_value. apply nat_to_value'_is_flat.
Qed.

Lemma nat_to_value_idempotent :
  forall (sz n : nat),
    sz > 0 -> (value_to_nat' sz (nat_to_value' sz n)) = Some n.
Proof.
  induction sz; intros.
  - inversion H.
  - unfold_rec value_to_nat'.
    assert (flat_valueP (nat_to_value' (S sz) n)).
    { apply nat_to_value'_is_flat. }
    destruct (nat_to_value' (S sz) n) eqn:?.
Admitted.

Module VerilogEval.

  Definition app (f : nat -> nat -> nat) (a : value) (b : value) : option value :=
    Option.map nat_to_value (Option.liftA2 f (value_to_nat a) (value_to_nat b)).

  Definition state_find (k : string) (s : state) : option value :=
    Map.find k (fst s).

  Definition eval_binop (op : binop) (a1 a2 : value) : option value :=
    match op with
    | Plus => app Nat.add a1 a2
    | Minus => app Nat.sub a1 a2
    | Times => app Mult.tail_mult a1 a2
    | Divide => app Nat.div a1 a2
    | _ => Some a1
    end.

(*    Fixpoint eval_expr (s : state) (e : expr) : option value :=
      match e with
      | Lit n => Some n
      | Var v => state_find v s
      | Neg a => 0 - (eval_expr s a)
      | BinOp op a1 a2 => eval_binop op a1 a2
      | Ternary c t f => if eval_expr s c then eval_expr s t else eval_expr s f
      end.
 *)
End VerilogEval.
