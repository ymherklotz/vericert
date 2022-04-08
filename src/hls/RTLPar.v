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

Definition bb := list (list instr).

Definition bblock := @bblock bb.
Definition code := @code bb.
Definition function := @function bb.
Definition fundef := @fundef bb.
Definition program := @program bb.
Definition funsig := @funsig bb.
Definition stackframe := @stackframe bb.
Definition state := @state bb.
Definition genv := @genv bb.

Section RELSEM.

  Context (ge: genv).

  Definition step_instr_list := step_list (step_instr ge).
  Definition step_instr_seq := step_list step_instr_list.
  Definition step_instr_block := step_list step_instr_seq.

  Inductive step: state -> trace -> state -> Prop :=
  | exec_bblock:
    forall s f sp pc rs rs' m m' bb pr pr',
      step_instr_block sp (mk_instr_state rs pr m) bb
                          (mk_instr_state rs' pr' m') ->
      step (State s f sp pc bb rs pr m) E0 (JumpState s f sp pc rs' pr' m')
  | exec_jumpstate :
    forall s f sp pc rs pr m block t st,
      f.(fn_code) ! pc = Some block ->
      step_cf_instr ge (JumpState s f sp pc rs pr m) block.(bb_exit) t st ->
      step (JumpState s f sp pc rs pr m) t st
  | exec_function_internal:
    forall s f args m m' stk bb cf,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      f.(fn_code) ! (f.(fn_entrypoint)) = Some (mk_bblock bb cf) ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  bb
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
        E0 (State s f sp pc nil (rs#res <- vres) pr m).

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

Definition max_reg_bblock (m : positive) (pc : node) (bb : bblock) :=
  let max_body :=
    fold_left
      (fun x l => fold_left (fun x' l' => fold_left max_reg_instr l' x') l x)
      bb.(bb_body) m
  in
  max_reg_cfi max_body bb.(bb_exit).

Definition max_reg_function (f: function) :=
  Pos.max
    (PTree.fold max_reg_bblock f.(fn_code) 1%positive)
    (fold_left Pos.max f.(fn_params) 1%positive).

Definition max_pc_function (f: function) : positive :=
  PTree.fold
    (fun m pc i =>
       (Pos.max m
                (pc + match Zlength i.(bb_body)
                      with Z.pos p => p | _ => 1 end))%positive)
    f.(fn_code) 1%positive.
