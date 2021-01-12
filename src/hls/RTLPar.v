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

Definition max_reg_instr (m: positive) (i: instruction) :=
  match i with
  | RPnop => m
  | RPop op args res => fold_left Pos.max args (Pos.max res m)
  | RPload chunk addr args dst => fold_left Pos.max args (Pos.max dst m)
  | RPstore chunk addr args src => fold_left Pos.max args (Pos.max src m)
  end.

Definition max_reg_cfi (m : positive) (i : control_flow_inst) :=
  match i with
  | RPcall sig (inl r) args res s => fold_left Pos.max args (Pos.max r (Pos.max res m))
  | RPcall sig (inr id) args res s => fold_left Pos.max args (Pos.max res m)
  | RPtailcall sig (inl r) args => fold_left Pos.max args (Pos.max r m)
  | RPtailcall sig (inr id) args => fold_left Pos.max args m
  | RPbuiltin ef args res s =>
      fold_left Pos.max (params_of_builtin_args args)
        (fold_left Pos.max (params_of_builtin_res res) m)
  | RPcond cond args ifso ifnot => fold_left Pos.max args m
  | RPjumptable arg tbl => Pos.max arg m
  | RPreturn None => m
  | RPreturn (Some arg) => Pos.max arg m
  | RPgoto n => m
  end.

Definition max_reg_bblock (m : positive) (pc : node) (bb : bblock) :=
  let max_body := fold_left (fun x l => fold_left max_reg_instr l x) bb.(bb_body) m in
  match bb.(bb_exit) with
  | Some e => max_reg_cfi max_body e
  | None => max_body
  end.

Definition max_reg_function (f: function) :=
  Pos.max
    (PTree.fold max_reg_bblock f.(fn_code) 1%positive)
    (fold_left Pos.max f.(fn_params) 1%positive).

Definition max_pc_function (f: function) : positive :=
  PTree.fold (fun m pc i => (Pos.max m
                                     (pc + match Zlength i.(bb_body)
                                           with Z.pos p => p | _ => 1 end))%positive)
             f.(fn_code) 1%positive.

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
