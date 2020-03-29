(*
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

From Coq Require Import
  Structures.OrderedTypeEx
  FSets.FMapPositive
  Program.Basics
  PeanoNat
  ZArith.

From bbv Require Word.

From coqup.common Require Import Helper Coquplib Show.

Import ListNotations.

Definition reg : Type := positive.

Record value : Type := mkvalue {
  vsize : nat;
  vword : Word.word vsize
}.

Definition posToValue (p : positive) : value :=
  let size := Z.to_nat (log_sup p) in
  mkvalue size (Word.posToWord size p).

Definition state : Type := PositiveMap.t value * PositiveMap.t value.

Inductive binop : Type :=
| Vconst (v : value)
| Vmove
| Vneg
| Vadd
| Vsub
| Vmul
| Vmulimm (v : value)
| Vdiv
| Vdivimm (v : value)
| Vmod
| Vlt
| Vgt
| Vle
| Vge
| Veq
| Vand
| Vor
| Vxor.

Inductive expr : Type := Op (op : binop) (v : list expr).

Inductive stmnt : Type :=
| Skip
| Block (s : list stmnt)
| Cond (c : expr) (st sf : stmnt)
| Case (c : expr) (b : list (expr * stmnt))
| Blocking (a b : expr)
| Nonblocking (a b : expr)
| Decl (v : reg) (s : nat) (b : expr).

Definition posToLit (p : positive) : expr :=
  Lit (posToValue p).

Definition verilog : Type := list stmnt.

Coercion Lit : value >-> expr.
Coercion Var : reg >-> expr.
