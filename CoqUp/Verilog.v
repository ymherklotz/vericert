From Coq Require Import Bool List String.

Import ListNotations.

Module Verilog.

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
| Var (n : string)
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
Notation "a '=! b" := (Blocking a b) (at level 80, no associativity) : verilog_scope.
Notation "'IF' c 'THEN' a 'ELSE' b 'FI'" := (Cond c a b) (at level 80, right associativity) : verilog_scope.

End VerilogNotation.

Module VerilogEval.

Import VerilogNotation.

Fixpoint eval_expr (state, expr)

End VerilogEval.

End Verilog.
