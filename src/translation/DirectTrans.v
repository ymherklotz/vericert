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

From compcert.backend Require RTL.

From coqup.verilog Require VerilogAST.

Definition trans_instr (rtl : RTL.instruction) : VerilogAST.stmnt :=
  match rtl with
  | RTL.Inop s =>
    (** Nop instruction should just become a Skip in Verilog, which is just a
        semicolon. *)
    VerilogAST.Skip
  | RTL.Iop op args res s =>
    (** Perform an arithmetic operation over registers.  This will just become
        one binary operation in Verilog.  This will contain a list of registers,
        so these will just become a chain of binary operations in Verilog. *)
    VerilogAST.Skip
  | RTL.Iload chunk addr args dst s =>
    (** Load from memory, which will maybe become a load from RAM, however, I'm
        not sure yet how memory will be implemented or how it will formalised
        be. *)
    VerilogAST.Skip
  | RTL.Istore chunk addr args src s =>
    (** How memory will be laid out will also affect how stores are handled.  For
        now hopefully these can be ignored, and hopefull they are not used that
        often when they are not required in C. *)
    VerilogAST.Skip
  | RTL.Icall sig ros args res s =>
    (** Function call should become a module instantiation with start and end
        signals appropriately wired up. *)
    VerilogAST.Skip
  | RTL.Itailcall sig ros args =>
    (** Should be converted into a reset of the modules state, setting the
        initial variables correctly.  This would simulate a tailcall as it is
        similar to jumping back to the top of the function in assembly. *)
    VerilogAST.Skip
  | RTL.Ibuiltin ef args res s =>
    (** Builtin functions will have to supported manually, by implementing the
        Verilog myself. *)
    VerilogAST.Skip
  | RTL.Icond cond args s1 s2 =>
    (** Will be converted into two separate processes that are combined by a mux
        at the end, with a start flag that propagates in the construct that should
        be chosen. *)
    VerilogAST.Skip
  | RTL.Ijumptable arg tbl =>
    (** A jump to a specific instruction in the list, this will require setting
        the state in the state machine appropriately.  This is trivial to
        implement if no scheduling is involved, but as soon as that isn't the
        case it might be difficult to find that location.  It would help to
        transform the CFG to a few basic blocks first which cannot have any
        branching. *)
    VerilogAST.Skip
  | RTL.Ireturn r =>
    (** The return value of the function, which will just mean that the finished
        signal goes high and the result is stored in the result register. *)
    VerilogAST.Skip
  end.
