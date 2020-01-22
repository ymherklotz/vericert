From Coq Require Import Lists.List Strings.String.
From Coq Require Import
     Structures.OrderedTypeEx
     FSets.FMapList.

From bbv Require Word.

From CoqUp Require Import Helper.

Module Verilog.

Import ListNotations.

Module Map := FMapList.Make String_as_OT.

Definition state : Type := Map.t nat * Map.t nat.

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
| Lit (n : nat)
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

Coercion Lit : nat >-> expr.
Coercion Var : string >-> expr.

Module VerilogNotation.

Declare Scope verilog_scope.
Bind Scope verilog_scope with expr.
Bind Scope verilog_scope with stmnt.
Bind Scope verilog_scope with verilog.
Delimit Scope verilog_scope with verilog.

Notation "x + y" := (BinOp Plus x y) (at level 50, left associativity) : verilog_scope.
Notation "x - y" := (BinOp Minus x y) (at level 50, left associativity) : verilog_scope.
Notation "x * y" := (BinOp Times x y) (at level 40, left associativity) : verilog_scope.
Notation "x / y" := (BinOp Divide x y) (at level 40, left associativity) : verilog_scope.
Notation "x < y" := (BinOp LT x y) (at level 70, no associativity) : verilog_scope.
Notation "x <= y" := (BinOp LE x y) (at level 70, no associativity) : verilog_scope.
Notation "x > y" := (BinOp GT x y) (at level 70, no associativity) : verilog_scope.
Notation "x >= y" := (BinOp GE x y) (at level 70, no associativity) : verilog_scope.
Notation "x == y" := (BinOp Eq x y) (at level 70, no associativity) : verilog_scope.
Notation "x & y" := (BinOp And x y) (at level 40, left associativity) : verilog_scope.
Notation "x | y" := (BinOp Eq x y) (at level 40, left associativity) : verilog_scope.
Notation "x ^ y" := (BinOp Eq x y) (at level 30, right associativity) : verilog_scope.
Notation "~ y" := (Neg y) (at level 75, right associativity) : verilog_scope.
Notation "c ? t : f" := (Ternary c t f) (at level 20, right associativity) : verilog_scope.

Notation "a '<=!' b" := (Nonblocking a b) (at level 80, no associativity) : verilog_scope.
Notation "a '=!' b" := (Blocking a b) (at level 80, no associativity) : verilog_scope.
Notation "'IF' c 'THEN' a 'ELSE' b 'FI'" := (Cond c a b) (at level 80, right associativity) : verilog_scope.

End VerilogNotation.

Module VerilogEval.

Definition state_find (k : string) (s : state) : nat :=
  opt_default 0 (Map.find k (fst s)).

Definition eval_binop (op : binop) (a1 a2 : nat) : nat :=
  match op with
  | Plus => a1 + a2
  | Minus => a1 - a2
  | Times => a1 * a2
  end.

Fixpoint eval_expr (s : state) (e : expr) : nat :=
  match e with
  | Lit n => n
  | Var v => state_find v s
  | Neg a => 0 - (eval_expr s a)
  | BinOp op a1 a2 => eval_binop op a1 a2
  | Ternary c t f => if eval_expr s c then eval_expr s t else eval_expr s f
  end.

End VerilogEval.

End Verilog.
Export Verilog.
