(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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
Require Import compcert.common.Errors.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLPargen.
Require Import vericert.hls.Scheduleoracle.

Inductive match_stackframes: RTLBlock.stackframe -> RTLPar.stackframe -> Prop :=
| match_stackframe:
    forall f tf res sp pc rs,
      transl_function f = OK tf ->
      match_stackframes (RTLBlock.Stackframe res f sp pc rs)
                        (RTLPar.Stackframe res tf sp pc rs).

Inductive match_states: RTLBlock.state -> RTLPar.state -> Prop :=
| match_state:
    forall sf f sp pc rs mem sf' tf
      (TRANSL: transl_function f = OK tf)
      (STACKS: list_forall2 match_stackframes sf sf'),
      match_states (RTLBlock.State sf f sp pc rs mem)
                   (RTLPar.State sf' tf sp pc rs mem)
| match_returnstate:
    forall stack stack' v mem
      (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (RTLBlock.Returnstate stack v mem)
                   (RTLPar.Returnstate stack' v mem)
| match_initial_call:
    forall stack stack' f tf args m
           (TRANSL: transl_fundef f = OK tf)
           (STACKS: list_forall2 match_stackframes stack stack'),
      match_states (RTLBlock.Callstate stack f args m)
      (RTLPar.Callstate stack' tf args m).
