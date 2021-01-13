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

From compcert Require Import AST.
From vericert Require Import RTLBlock RTLPar.

Parameter schedule : RTLBlock.function -> Errors.res RTLPar.function.

Definition transl_fundef := transf_partial_fundef schedule.

Definition transl_program (p : RTLBlock.program) : Errors.res RTLPar.program :=
  transform_partial_program transl_fundef p.
