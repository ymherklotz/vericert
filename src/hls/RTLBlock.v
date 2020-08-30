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

From compcert Require Import
     Coqlib
     AST
     Maps
     Op
     RTL
     Registers.

Definition node := positive.

Inductive instruction : Type :=
| RBnop : instruction
| RBop : operation -> list reg -> reg -> instruction
| RBload : memory_chunk -> addressing -> list reg -> reg -> instruction
| RBstore : memory_chunk -> addressing -> list reg -> reg -> instruction.

Definition bblock_body : Type := list instruction.

Inductive control_flow_inst : Type :=
| RBcall : signature -> ident -> list reg -> reg -> node -> control_flow_inst
| RBtailcall : signature -> ident -> list reg -> control_flow_inst
| RBbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> control_flow_inst
| RBcond : condition -> list reg -> node -> node -> control_flow_inst
| RBjumptable : reg -> list node -> control_flow_inst
| RBredurn : option reg -> control_flow_inst.

Record bblock : Type := mk_bblock {
    bb_body: bblock_body;
    bb_exit: option control_flow_inst
  }.

Definition code : Type := PTree.t bblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.
