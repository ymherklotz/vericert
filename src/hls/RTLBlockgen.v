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

Require compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.lib.Maps.

Require Import vericert.hls.RTLBlock.

Parameter partition : RTL.function -> Errors.res function.

Definition transl_fundef := transf_partial_fundef partition.

Definition transl_program : RTL.program -> Errors.res program :=
  transform_partial_program transl_fundef.
