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

Require Import compcert.common.AST.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.Scheduleoracle.

Parameter schedule : RTLBlock.function -> RTLPar.function.

Definition transl_function (f : RTLBlock.function) : Errors.res RTLPar.function :=
  let tf := schedule f in
  if beq2 schedule_oracle f.(RTLBlock.fn_code) tf.(fn_code) then
    Errors.OK tf
  else
    Errors.Error (Errors.msg "RTLPargen: Could not prove the blocks equivalent.").

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : RTLBlock.program) : Errors.res RTLPar.program :=
  transform_partial_program transl_fundef p.
