(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.verilog.Op.

Require Import vericert.common.Vericertlib.

Local Open Scope rtl.

Definition node := positive.

Inductive instr : Type :=
| RBnop : instr
| RBop : operation -> list reg -> reg -> instr
| RBload : memory_chunk -> addressing -> list reg -> reg -> instr
| RBstore : memory_chunk -> addressing -> list reg -> reg -> instr.

Inductive cf_instr : Type :=
| RBcall : signature -> reg + ident -> list reg -> reg -> node -> cf_instr
| RBtailcall : signature -> reg + ident -> list reg -> cf_instr
| RBbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> cf_instr
| RBcond : condition -> list reg -> node -> node -> cf_instr
| RBjumptable : reg -> list node -> cf_instr
| RBreturn : option reg -> cf_instr
| RBgoto : node -> cf_instr.

Record bblock (bblock_body : Type) : Type := mk_bblock {
    bb_body: bblock_body;
    bb_exit: option cf_instr
  }.
Arguments mk_bblock [bblock_body].
Arguments bb_body [bblock_body].
Arguments bb_exit [bblock_body].

Definition successors_instr (i : cf_instr) : list node :=
  match i with
  | RBcall sig ros args res s => s :: nil
  | RBtailcall sig ros args => nil
  | RBbuiltin ef args res s => s :: nil
  | RBcond cond args ifso ifnot => ifso :: ifnot :: nil
  | RBjumptable arg tbl => tbl
  | RBreturn optarg => nil
  | RBgoto n => n :: nil
  end.

Definition max_reg_instr (m: positive) (i: instr) :=
  match i with
  | RBnop => m
  | RBop op args res => fold_left Pos.max args (Pos.max res m)
  | RBload chunk addr args dst => fold_left Pos.max args (Pos.max dst m)
  | RBstore chunk addr args src => fold_left Pos.max args (Pos.max src m)
  end.

Definition max_reg_cfi (m : positive) (i : cf_instr) :=
  match i with
  | RBcall sig (inl r) args res s => fold_left Pos.max args (Pos.max r (Pos.max res m))
  | RBcall sig (inr id) args res s => fold_left Pos.max args (Pos.max res m)
  | RBtailcall sig (inl r) args => fold_left Pos.max args (Pos.max r m)
  | RBtailcall sig (inr id) args => fold_left Pos.max args m
  | RBbuiltin ef args res s =>
      fold_left Pos.max (params_of_builtin_args args)
        (fold_left Pos.max (params_of_builtin_res res) m)
  | RBcond cond args ifso ifnot => fold_left Pos.max args m
  | RBjumptable arg tbl => Pos.max arg m
  | RBreturn None => m
  | RBreturn (Some arg) => Pos.max arg m
  | RBgoto n => m
  end.

Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

Inductive instr_state : Type :=
| InstrState:
    forall (rs: regset)
           (m: mem),
    instr_state.

Inductive cf_instr_state : Type :=
| CfInstrState:
    forall ()

Section RELSEM.

  Context (fundef: Type).

  Definition genv := Genv.t fundef unit.

  Context (ge: genv) (sp: val).

  Inductive step_instr: instr_state -> instr -> instr_state -> Prop :=
  | exec_RBnop:
      forall rs m,
      step_instr (InstrState rs m) RBnop (InstrState rs m)
  | exec_RBop:
      forall op v res args rs m,
      eval_operation ge sp op rs##args m = Some v ->
      step_instr (InstrState rs m)
                 (RBop op args res)
                 (InstrState (rs#res <- v) m)
  | exec_RBload:
      forall addr rs args a chunk m v dst,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step_instr (InstrState rs m)
                 (RBload chunk addr args dst)
                 (InstrState (rs#dst <- v) m)
  | exec_RBstore:
      forall addr rs args a chunk m src m',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step_instr (InstrState rs m)
                 (RBstore chunk addr args src)
                 (InstrState rs m').

  Inductive step_instr_list: instr_state -> list instr -> instr_state -> Prop :=
    | exec_RBcons:
        forall state i state' state'' instrs,
        step_instr state i state' ->
        step_instr_list state' instrs state'' ->
        step_instr_list state (i :: instrs) state''
    | exec_RBnil:
        forall state,
        step_instr_list state nil state.

  Inductive step_cf_instr:

End RELSEM.
