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

Definition translation (rtl : RTL.code) : Verilog.verilog :=
  match rtl with
  | RTL.Inop ->
    (** Nop instruction should just become a Skip in Verilog, which is just a semicolon *)
  | RTL.op ->
    (** Perform an arithmetic operation over registers. This will just become one binary operation in
        Verilog. This will contain a list of registers, so these will just become a chain of binary
        operations in Verilog. *)
  | RTL.Iload ->
    (** Load from memory, which will maybe become a load from RAM, however, I'm not sure yet how memory
        will be implemented or how it will be formalised. *)
  | RTL.Istore ->
    (** How memory will be laid out will also affect how stores are handled. For now hopefully these can
        be ignored, and hopefull they are not used that often when they are not required in C. *)
  | RTL.Icall -> 
