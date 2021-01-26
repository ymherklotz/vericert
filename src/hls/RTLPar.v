(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2021 Yann Herklotz <yann@yannherklotz.com>
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
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.

Require Import vericert.hls.RTLBlockInstr.

Definition bblock_body := list (list instr).
Definition bblock := RTLBlockInstr.bblock bblock_body.

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

Definition max_reg_bblock (m : positive) (pc : node) (bb : bblock) :=
  let max_body := fold_left (fun x l => fold_left max_reg_instr l x) bb.(bb_body) m in
  max_reg_cfi max_body bb.(bb_exit).

Definition max_reg_function (f: function) :=
  Pos.max
    (PTree.fold max_reg_bblock f.(fn_code) 1%positive)
    (fold_left Pos.max f.(fn_params) 1%positive).

Definition max_pc_function (f: function) : positive :=
  PTree.fold (fun m pc i => (Pos.max m
                                     (pc + match Zlength i.(bb_body)
                                           with Z.pos p => p | _ => 1 end))%positive)
             f.(fn_code) 1%positive.

Definition genv := Genv.t fundef unit.

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

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Block:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (bb: bblock)             (**r current basic block *)
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

Section RELSEM.

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

  Inductive step: state -> trace -> state -> Prop :=
  | exec_bblock_start:
      forall stack f sp pc rs m bb,
      (fn_code f)!pc = Some bb ->
      step (State stack f sp pc rs m) E0 (Block stack f sp bb rs m)
  | exec_bblock_instr_cons:
      forall sp rs m rs' m' stack f bb bbs cfi,
      step_instr_list _ ge sp (InstrState rs m) bb (InstrState rs' m') ->
      step (Block stack f sp (mk_bblock (bb :: bbs) cfi) rs m) E0
           (Block stack f sp (mk_bblock bbs cfi) rs' m')
  | exec_RBcall:
      forall s f sp rs m res fd ros sig args pc',
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (Block s f sp (mk_bblock nil (RBcall sig ros args res pc')) rs m)
           E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_RBtailcall:
      forall s f stk rs m sig ros args fd m',
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (Block s f (Vptr stk Ptrofs.zero) (mk_bblock nil (RBtailcall sig ros args)) rs m)
        E0 (Callstate s fd rs##args m')
  | exec_RBbuiltin:
      forall s f sp rs m ef args res pc' vargs t vres m',
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step (Block s f sp (mk_bblock nil (RBbuiltin ef args res pc')) rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_RBcond:
      forall s f sp rs m cond args ifso ifnot b pc',
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (Block s f sp (mk_bblock nil (RBcond cond args ifso ifnot)) rs m)
        E0 (State s f sp pc' rs m)
  | exec_RBjumptable:
      forall s f sp rs m arg tbl n pc',
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (Block s f sp (mk_bblock nil (RBjumptable arg tbl)) rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk rs m or m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (Block s f (Vptr stk Ptrofs.zero) (mk_bblock nil (RBreturn or)) rs m)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m')
  | exec_function_external:
      forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate nil f nil m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
