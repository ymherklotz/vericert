(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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

(* [[file:../../docs/basic-block-generation.org::rtlblockgenproof-imports][rtlblockgenproof-imports]] *)
Require compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.lib.Maps.

Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLBlockgen.
(* rtlblockgenproof-imports ends here *)

(* [[file:../../docs/basic-block-generation.org::rtlblockgenproof-match-states][rtlblockgenproof-match-states]] *)
Inductive match_states : RTL.state -> RTLBlock.state -> Prop :=
| match_state :
  forall stk f tf sp pc rs m
         (TF: transl_function f = OK tf),
  match_states (RTL.State stk f sp pc rs m)
               (RTLBlock.State stk tf sp (find_block max n i) rs m).
(* rtlblockgenproof-match-states ends here *)

(* [[file:../../docs/basic-block-generation.org::rtlblockgenproof-correctness][rtlblockgenproof-correctness]] *)
Section CORRECTNESS.

  Context (prog : RTL.program).
  Context (tprog : RTLBlock.program).

  Context (TRANSL : match_prog prog tprog).

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog) (RTLBlock.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus; eauto with htlproof.
    apply senv_preserved.

End CORRECTNESS.
(* rtlblockgenproof-correctness ends here *)
