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
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.

Require Import vericert.common.Vericertlib.

Local Open Scope rtl.

Definition node := positive.
Definition predicate := positive.

Inductive pred_op : Type :=
| Pvar: predicate -> pred_op
| Pnot: pred_op -> pred_op
| Pand: pred_op -> pred_op -> pred_op
| Por: pred_op -> pred_op -> pred_op.

Inductive instr : Type :=
| RBnop : instr
| RBop : option pred_op -> operation -> list reg -> reg -> instr
| RBload : option pred_op -> memory_chunk -> addressing -> list reg -> reg -> instr
| RBstore : option pred_op -> memory_chunk -> addressing -> list reg -> reg -> instr
| RBsetpred : condition -> list reg -> predicate -> instr.

Inductive cf_instr : Type :=
| RBcall : signature -> reg + ident -> list reg -> reg -> node -> cf_instr
| RBtailcall : signature -> reg + ident -> list reg -> cf_instr
| RBbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> cf_instr
| RBcond : condition -> list reg -> node -> node -> cf_instr
| RBjumptable : reg -> list node -> cf_instr
| RBreturn : option reg -> cf_instr
| RBgoto : node -> cf_instr
| RBpred_cf : pred_op -> cf_instr -> cf_instr -> cf_instr.

Fixpoint successors_instr (i : cf_instr) : list node :=
  match i with
  | RBcall sig ros args res s => s :: nil
  | RBtailcall sig ros args => nil
  | RBbuiltin ef args res s => s :: nil
  | RBcond cond args ifso ifnot => ifso :: ifnot :: nil
  | RBjumptable arg tbl => tbl
  | RBreturn optarg => nil
  | RBgoto n => n :: nil
  | RBpred_cf p c1 c2 => concat (successors_instr c1 :: successors_instr c2 :: nil)
  end.

Definition max_reg_instr (m: positive) (i: instr) :=
  match i with
  | RBnop => m
  | RBop p op args res =>
    fold_left Pos.max args (Pos.max res m)
  | RBload p chunk addr args dst =>
    fold_left Pos.max args (Pos.max dst m)
  | RBstore p chunk addr args src =>
    fold_left Pos.max args (Pos.max src m)
  | RBsetpred c args p =>
    fold_left Pos.max args 1%positive
  end.

Fixpoint max_reg_cfi (m : positive) (i : cf_instr) :=
  match i with
  | RBcall sig (inl r) args res s =>
    fold_left Pos.max args (Pos.max r (Pos.max res m))
  | RBcall sig (inr id) args res s =>
    fold_left Pos.max args (Pos.max res m)
  | RBtailcall sig (inl r) args =>
    fold_left Pos.max args (Pos.max r m)
  | RBtailcall sig (inr id) args =>
    fold_left Pos.max args m
  | RBbuiltin ef args res s =>
      fold_left Pos.max (params_of_builtin_args args)
        (fold_left Pos.max (params_of_builtin_res res) m)
  | RBcond cond args ifso ifnot => fold_left Pos.max args m
  | RBjumptable arg tbl => Pos.max arg m
  | RBreturn None => m
  | RBreturn (Some arg) => Pos.max arg m
  | RBgoto n => m
  | RBpred_cf p c1 c2 => Pos.max (max_reg_cfi m c1) (max_reg_cfi m c2)
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

Section DEFINITION.

  Context {bblock_body: Type}.

  Record bblock : Type := mk_bblock {
    bb_body: bblock_body;
    bb_exit: cf_instr
  }.

  Definition code: Type := PTree.t bblock.

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

  Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

  Inductive state : Type :=
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

End DEFINITION.

Section RELSEM.

  Context {bblock_body : Type}.

  Definition genv := Genv.t (@fundef bblock_body) unit.

  Context (ge: genv).

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

  Inductive step_instr: val -> instr_state -> instr -> instr_state -> Prop :=
  | exec_RBnop:
      forall rs m sp,
      step_instr sp (InstrState rs m) RBnop (InstrState rs m)
  | exec_RBop:
      forall op v res args rs m sp p,
      eval_operation ge sp op rs##args m = Some v ->
      step_instr sp (InstrState rs m)
                 (RBop p op args res)
                 (InstrState (rs#res <- v) m)
  | exec_RBload:
      forall addr rs args a chunk m v dst sp p,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step_instr sp (InstrState rs m)
                 (RBload p chunk addr args dst)
                 (InstrState (rs#dst <- v) m)
  | exec_RBstore:
      forall addr rs args a chunk m src m' sp p,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step_instr sp (InstrState rs m)
                 (RBstore p chunk addr args src)
                 (InstrState rs m').

  Inductive step_cf_instr: state -> cf_instr -> trace -> state -> Prop :=
  | exec_RBcall:
    forall s f sp rs m res fd ros sig args pc pc',
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step_cf_instr (State s f sp pc rs m) (RBcall sig ros args res pc')
           E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_RBtailcall:
      forall s f stk rs m sig ros args fd m' pc,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f (Vptr stk Ptrofs.zero) pc rs m) (RBtailcall sig ros args)
        E0 (Callstate s fd rs##args m')
  | exec_RBbuiltin:
      forall s f sp rs m ef args res pc' vargs t vres m' pc,
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step_cf_instr (State s f sp pc rs m) (RBbuiltin ef args res pc')
         t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_RBcond:
      forall s f sp rs m cond args ifso ifnot b pc pc',
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step_cf_instr (State s f sp pc rs m) (RBcond cond args ifso ifnot)
        E0 (State s f sp pc' rs m)
  | exec_RBjumptable:
      forall s f sp rs m arg tbl n pc pc',
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step_cf_instr (State s f sp pc rs m) (RBjumptable arg tbl)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk rs m or pc m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f (Vptr stk Ptrofs.zero) pc rs m) (RBreturn or)
        E0 (Returnstate s (regmap_optget or Vundef rs) m').

End RELSEM.
