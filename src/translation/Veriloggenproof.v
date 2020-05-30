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

From compcert Require Import Smallstep.
From compcert Require RTL.
From coqup Require Verilog.

Section CORRECTNESS.

  Variable prog: RTL.program.
  Variable tprog: Verilog.module.

  Inductive match_states: RTL.state -> Verilog.state -> Prop :=
  | match_state:
      forall,
        
        match_states (RTL.State f s k sp e m)
                     (Verilog.State m mi mis assoc nbassoc f cycle pc)
  | match_returnstate:
      forall v tv k m tm cs
             (MS: match_stacks k cs)
             (LD: Val.lessdef v tv)
             (MEXT: Mem.extends m tm),
        match_states (CminorSel.Returnstate v k m)
                     (RTL.Returnstate cs tv tm).

  Theorem transf_program_correct:
    forward_simulation (RTL.semantics prog) (Verilog.semantics tprog).
  Admitted.

End CORRECTNESS.
