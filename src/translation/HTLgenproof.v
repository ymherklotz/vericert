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

From coqup Require Import HTLgenspec Value AssocMap.
From coqup Require HTL Verilog.
From compcert Require RTL Registers Globalenvs AST.

Import AssocMapNotation.

Inductive match_assocmaps : RTL.regset -> assocmap -> Prop :=
| match_assocmap : forall r rs am,
    val_value_lessdef (Registers.Regmap.get r rs) am#r ->
    match_assocmaps rs am.

Inductive match_states : RTL.state -> HTL.state -> Prop :=
| match_state : forall (rs : RTL.regset) assoc sf f sp rs mem m st,
    match_assocmaps rs assoc ->
    tr_module f m ->
    match_states (RTL.State sf f sp st rs mem)
                 (HTL.State m st assoc)
| match_returnstate : forall v v' stack m,
    val_value_lessdef v v' ->
    match_states (RTL.Returnstate stack v m) (HTL.Returnstate v').

Inductive match_program : RTL.program -> HTL.module -> Prop :=
  match_program_intro :
    forall ge p b m f,
    ge = Globalenvs.Genv.globalenv p ->
    Globalenvs.Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
    tr_module f m ->
    match_program p m.

Section CORRECTNESS.

  Variable prog : RTL.program.
  Variable tprog : HTL.module.

  Hypothesis TRANSL : match_program prog tprog.

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : HTL.genv := HTL.genv_empty.

  (** The proof of semantic preservation for the translation of instructions
      is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    code st rs ---------------- State m st assoc
         ||                             |
         ||                             |
         ||                             |
         \/                             v
    code st rs' --------------- State m st assoc'
                    I /\ Q
>>
      where [tr_code c data control fin rtrn st] is assumed to hold.
   *)

  Definition transl_code_prop : Prop :=
    HTL.step tge (HTL.State)

End CORRECTNESS.
