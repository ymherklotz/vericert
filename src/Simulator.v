(*
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
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

From Coq Require Import FSets.FMapPositive.

From compcert Require Import Errors.

From coqup Require Compiler Verilog Value.
From coqup Require Import Coquplib.

Local Open Scope error_monad_scope.

Definition simulate (n : nat) (m : Verilog.module) : res (Value.value * list (positive * Value.value)) :=
  do map <- Verilog.module_run n m;
  match PositiveMap.find (fst (Verilog.mod_return m)) map with
  | Some v => OK (v, (PositiveMap.elements map))
  | None => Error (msg "Could not find result.")
  end.

Local Close Scope error_monad_scope.
