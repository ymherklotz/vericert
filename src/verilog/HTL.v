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
From coqup Require Import Coquplib Value AssocMap.
From coqup Require Verilog.
From compcert Require Events Globalenvs Smallstep Integers.

Import HexNotationValue.

(** The purpose of the hardware transfer language (HTL) is to create a more
hardware-like layout that is still similar to the register transfer language
(RTL) that it came from. The main change is that function calls become module
instantiations and that we now describe a state machine instead of a
control-flow graph. *)

Notation "a ! b" := (PositiveMap.find b a) (at level 1).

Definition reg := positive.
Definition node := positive.

Definition datapath := PositiveMap.t Verilog.stmnt.
Definition controllogic := PositiveMap.t Verilog.stmnt.

Record module: Type :=
  mkmodule {
    mod_params : list reg;
    mod_datapath : datapath;
    mod_controllogic : controllogic;
    mod_entrypoint : node;
    mod_st : reg;
    mod_finish : reg;
    mod_return : reg
  }.

(** * Operational Semantics *)

Definition genv := Globalenvs.Genv.t unit unit.
Definition genv_empty := Globalenvs.Genv.empty_genv unit unit nil.

Inductive state : Type :=
| State :
    forall (m : module)
           (st : node)
           (assoc : assocmap),
  state
| Returnstate : forall v : value, state.

Inductive step : genv -> state -> Events.trace -> state -> Prop :=
| step_module :
    forall g t m st ctrl data assoc0 assoc1 assoc2 assoc3 nbassoc0 nbassoc1 f stval pstval,
      m.(mod_controllogic)!st = Some ctrl ->
      m.(mod_datapath)!st = Some data ->
      Verilog.stmnt_runp f
        (Verilog.mkassociations assoc0 empty_assocmap)
        ctrl
        (Verilog.mkassociations assoc1 nbassoc0) ->
      Verilog.stmnt_runp f
        (Verilog.mkassociations assoc1 nbassoc0)
        data
        (Verilog.mkassociations assoc2 nbassoc1) ->
      assoc3 = merge_assocmap nbassoc1 assoc2 ->
      assoc3!(m.(mod_st)) = Some stval ->
      valueToPos stval = pstval ->
      step g (State m st assoc0) t (State m pstval assoc3)
| step_finish :
    forall g t m st assoc retval,
    assoc!(m.(mod_finish)) = Some (1'h"1") ->
    assoc!(m.(mod_return)) = Some retval ->
    step g (State m st assoc) t (Returnstate retval).
Hint Constructors step : htl.

Inductive initial_state (m : module) : state -> Prop :=
| initial_state_intro : forall st,
    st = m.(mod_entrypoint) ->
    initial_state m (State m st empty_assocmap).

Inductive final_state : state -> Integers.int -> Prop :=
| final_state_intro : forall retval retvali,
    value_int_eqb retval retvali = true ->
    final_state (Returnstate retval) retvali.

Definition semantics (m : module) :=
  Smallstep.Semantics step (initial_state m) final_state genv_empty.
