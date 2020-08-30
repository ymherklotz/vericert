(*
 * Vericert: Verified high-level synthesis.
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

From compcert Require
     RTL.
From compcert Require Import
     AST
     Maps.
From vericert Require Import
     RTLBlock.

Parameter partition : RTL.code -> code.

Definition transl_function (f : RTL.function) : function :=
  mkfunction f.(RTL.fn_sig)
             f.(RTL.fn_params)
             f.(RTL.fn_stacksize)
             (partition f.(RTL.fn_code))
             f.(RTL.fn_entrypoint).

Definition transl_fundef := transf_fundef transl_function.

Definition transl_program : RTL.program -> program :=
  transform_program transl_fundef.
