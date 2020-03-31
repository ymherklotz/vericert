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

From coqup.common Require Import Coquplib Show.

From compcert Require Integers.

Import ListNotations.

Definition reg : Type := positive.

Record value : Type := mkvalue {
  vsize : nat;
  vword : Word.word vsize
}.

Definition posToValue (p : positive) : value :=
  let size := Z.to_nat (log_sup p) in
  mkvalue size (Word.posToWord size p).

Definition intToValue (i : Integers.int) : value :=
  mkvalue 32%nat (Word.ZToWord 32%nat (Integers.Int.unsigned i)).

Definition valueToZ (v : value) : Z :=
  Word.uwordToZ v.(vword).

Definition state : Type := PositiveMap.t value * PositiveMap.t value.

Inductive binop : Type :=
| Vadd : binop  (** addition (binary [+]) *)
| Vsub : binop  (** subtraction (binary [-]) *)
| Vmul : binop  (** multiplication (binary [*]) *)
| Vdiv : binop  (** division (binary [/]) *)
| Vdivu : binop  (** division unsigned (binary [/]) *)
| Vmod : binop  (** remainder ([%]) *)
| Vmodu : binop  (** remainder unsigned ([/]) *)
| Vlt : binop   (** less than ([<]) *)
| Vltu : binop   (** less than unsigned ([<]) *)
| Vgt : binop   (** greater than ([>]) *)
| Vgtu : binop   (** greater than unsigned ([>]) *)
| Vle : binop   (** less than or equal ([<=]) *)
| Vleu : binop   (** less than or equal unsigned ([<=]) *)
| Vge : binop   (** greater than or equal ([>=]) *)
| Vgeu : binop   (** greater than or equal unsigned ([>=]) *)
| Veq : binop   (** equal to ([==]) *)
| Vne : binop   (** not equal to ([!=]) *)
| Vand : binop  (** and (binary [&]) *)
| Vor : binop   (** or (binary [|]) *)
| Vxor : binop  (** xor (binary [^|]) *)
| Vshl : binop  (** shift left ([<<]) *)
| Vshr : binop. (** shift left ([<<]) *)

Inductive unop : Type :=
| Vneg  (** negation ([~]) *)
| Vnot. (** not operation [!] *)

Inductive expr : Type :=
| Vlit : value -> expr
| Vvar : reg -> expr
| Vbinop : binop -> expr -> expr -> expr
| Vunop : unop -> expr -> expr
| Vternary : expr -> expr -> expr -> expr.

Definition posToExpr (p : positive) : expr :=
  Vlit (posToValue p).

Inductive stmnt : Type :=
| Vskip : stmnt
| Vseq : list stmnt -> stmnt
| Vcond : expr -> stmnt -> stmnt -> stmnt
| Vcase : expr -> list (expr * stmnt) -> stmnt
| Vblock : expr -> expr -> stmnt
| Vnonblock : expr -> expr -> stmnt
| Vdecl : reg -> nat -> expr -> stmnt.

Definition posToLit (p : positive) : expr :=
  Vlit (posToValue p).

Definition verilog : Type := list stmnt.

Coercion Vlit : value >-> expr.
Coercion Vvar : reg >-> expr.
