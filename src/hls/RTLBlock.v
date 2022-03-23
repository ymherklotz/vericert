(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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

(* [[file:../../lit/scheduler-languages.org::rtlblock-main][rtlblock-main]] *)
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

Definition bb := list instr.

Definition bblock := @bblock bb.
Definition code := @code bb.
Definition function := @function bb.
Definition fundef := @fundef bb.
Definition program := @program bb.
Definition funsig := @funsig bb.
Definition stackframe := @stackframe bb.

Definition genv := @genv bb.

Inductive state : Type :=
| State:
  forall (stack: list stackframe) (**r call stack *)
         (f: function)            (**r current function *)
         (b: bb)                  (**r current block being executed *)
         (sp: val)                (**r stack pointer *)
         (pc: node)               (**r current program point in [c] *)
         (rs: regset)             (**r register state *)
         (pr: predset)            (**r predicate register state *)
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

  Inductive step_instr_list: val -> instr_state -> list instr -> instr_state -> Prop :=
    | exec_RBcons:
        forall state i state' state'' instrs sp,
        step_instr ge sp state i state' ->
        step_instr_list sp state' instrs state'' ->
        step_instr_list sp state (i :: instrs) state''
    | exec_RBnil:
        forall state sp,
        step_instr_list sp state nil state.

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

  Inductive step_cf_instr: state -> cf_instr -> trace -> state -> Prop :=
  | exec_RBcall:
    forall s f b sp rs m res fd ros sig args pc pc' pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step_cf_instr (State s f b sp pc rs pr m) (RBcall sig ros args res pc')
                    E0 (Callstate (Stackframe res f sp pc' rs pr :: s) fd rs##args m)
  | exec_RBtailcall:
    forall s f b stk rs m sig ros args fd m' pc pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f b (Vptr stk Ptrofs.zero) pc rs pr m) (RBtailcall sig ros args)
                    E0 (Callstate s fd rs##args m')
  | exec_RBbuiltin:
      forall s f b sp rs m ef args res pc' vargs t vres m' pc pr,
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step_cf_instr (State s f b sp pc rs pr m) (RBbuiltin ef args res pc')
         t (State s f b sp pc' (regmap_setres res vres rs) pr m')
  | exec_RBcond:
      forall s f block sp rs m cond args ifso ifnot b pc pc' pr,
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step_cf_instr (State s f block sp pc rs pr m) (RBcond cond args ifso ifnot)
        E0 (State s f block sp pc' rs pr m)
  | exec_RBjumptable:
      forall s f b sp rs m arg tbl n pc pc' pr,
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step_cf_instr (State s f b sp pc rs pr m) (RBjumptable arg tbl)
        E0 (State s f b sp pc' rs pr m)
  | exec_RBreturn:
      forall s f b stk rs m or pc m' pr,
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f b (Vptr stk Ptrofs.zero) pc rs pr m) (RBreturn or)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_RBgoto:
      forall s f b sp pc rs pr m pc',
      step_cf_instr (State s f b sp pc rs pr m) (RBgoto pc') E0 (State s f b sp pc' rs pr m)
  | exec_RBpred_cf:
      forall s f b sp pc rs pr m cf1 cf2 st' p t,
      step_cf_instr (State s f b sp pc rs pr m) (if eval_predf pr p then cf1 else cf2) t st' ->
      step_cf_instr (State s f b sp pc rs pr m) (RBpred_cf p cf1 cf2) t st'.

  Inductive step: state -> trace -> state -> Prop :=
  | exec_function_internal:
    forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  (PMap.init false)
                  m')
  | exec_function_external:
    forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
    forall res f sp pc rs s vres m pr,
      step (Returnstate (Stackframe res f sp pc rs pr :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) pr m).

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
(* rtlblock-main ends here *)
