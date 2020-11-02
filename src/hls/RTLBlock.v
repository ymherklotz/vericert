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

Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.

Definition node := positive.

Inductive instruction : Type :=
| RBnop : instruction
| RBop : operation -> list reg -> reg -> instruction
| RBload : memory_chunk -> addressing -> list reg -> reg -> instruction
| RBstore : memory_chunk -> addressing -> list reg -> reg -> instruction.

Definition bblock_body : Type := list instruction.

Inductive control_flow_inst : Type :=
(*| RBcall : signature -> reg + ident -> list reg -> reg -> node -> control_flow_inst
| RBtailcall : signature -> reg + ident -> list reg -> control_flow_inst
| RBbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> control_flow_inst*)
| RBcond : condition -> list reg -> node -> node -> control_flow_inst
| RBjumptable : reg -> list node -> control_flow_inst
| RBreturn : option reg -> control_flow_inst
| RBgoto : node -> control_flow_inst.

Record bblock : Type := mk_bblock {
    bb_body: bblock_body;
    bb_exit: control_flow_inst
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
(*  | RBcall sig ros args res s => s :: nil
  | RBtailcall sig ros args => nil
  | RBbuiltin ef args res s => s :: nil*)
  | RBcond cond args ifso ifnot => ifso :: ifnot :: nil
  | RBjumptable arg tbl => tbl
  | RBreturn optarg => nil
  | RBgoto n => n :: nil
  end.

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

Inductive cont : Type :=
  | C
  | N.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem)                 (**r memory state *)
             (bblock: bblock)         (**r bblock being executed *)
             (c : cont),
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

Section RELSEM.

Variable ge: genv.

Definition find_function
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Inductive step : state -> trace -> state -> Prop :=
  | exec_RBnop :
      forall s f sp pc rs m ls ci,
      step (State s f sp pc rs m (mk_bblock (RBnop :: ls) ci) C) E0
           (State s f sp (Pos.succ pc) rs m (mk_bblock ls ci) C)
  | exec_RBop :
      forall s f sp pc rs m ls args op res ci v,
      eval_operation ge sp op rs##args m = Some v ->
      step (State s f sp pc rs m (mk_bblock (RBop op args res :: ls) ci) C) E0
           (State s f sp (Pos.succ pc) rs m (mk_bblock ls ci) C)
  | exec_RBload:
      forall s f sp pc rs m chunk addr args dst a v ls ci,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m (mk_bblock (RBload chunk addr args dst :: ls) ci) C)
        E0 (State s f sp (Pos.succ pc) (rs#dst <- v) m (mk_bblock ls ci) C)
  | exec_RBstore:
      forall s f sp pc rs m chunk addr args src a m' ls ci,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs m (mk_bblock (RBstore chunk addr args src :: ls) ci) C)
        E0 (State s f sp (Pos.succ pc) rs m' (mk_bblock ls ci) C)
  | exec_RBcond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State s f sp pc rs m (mk_bblock nil (RBcond cond args ifso ifnot)) C)
        E0 (State s f sp pc' rs m (mk_bblock nil (RBcond cond args ifso ifnot)) N)
.
