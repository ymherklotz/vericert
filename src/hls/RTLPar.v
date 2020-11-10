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

From compcert Require Import Coqlib Maps.
From compcert Require Import AST Integers Values Events Memory Globalenvs Smallstep.
From compcert Require Import Op Registers.

Definition node := positive.

Inductive instruction : Type :=
| RPnop : instruction
| RPop : operation -> list reg -> reg -> instruction
| RPload : memory_chunk -> addressing -> list reg -> reg -> instruction
| RPstore : memory_chunk -> addressing -> list reg -> reg -> instruction.

Definition bblock_body : Type := list (list instruction).

Inductive control_flow_inst : Type :=
| RPcall : signature -> reg + ident -> list reg -> reg -> node -> control_flow_inst
| RPtailcall : signature -> reg + ident -> list reg -> control_flow_inst
| RPbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> control_flow_inst
| RPcond : condition -> list reg -> node -> node -> control_flow_inst
| RPjumptable : reg -> list node -> control_flow_inst
| RPreturn : option reg -> control_flow_inst
| RPgoto : node -> control_flow_inst.

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

Definition successors_instr (i : control_flow_inst) : list node :=
  match i with
  | RPcall sig ros args res s => s :: nil
  | RPtailcall sig ros args => nil
  | RPbuiltin ef args res s => s :: nil
  | RPcond cond args ifso ifnot => ifso :: ifnot :: nil
  | RPjumptable arg tbl => tbl
  | RPreturn optarg => nil
  | RPgoto n => n :: nil
  end.

(*Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val)         (**r arguments to the call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val)                 (**r return value for the call *)
             (m: mem),                (**r memory state *)
      state.
*)
