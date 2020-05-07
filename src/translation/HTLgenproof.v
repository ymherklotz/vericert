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

From coqup Require Import HTLgenspec.
From coqup Require HTL Verilog.
From compcert Require RTL.

Parameter match_assocset : RTL.regset -> Verilog.assocset -> Prop.

Inductive match_states : RTL.state -> HTL.state -> Prop :=
| match_state : forall (rs : RTL.regset) assoc sf f sp rs mem m st,
    match_assocset rs assoc ->
    match_states (RTL.State sf f sp st rs mem)
                 (HTL.State m st assoc).
