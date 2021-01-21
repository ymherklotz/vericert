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

Definition bblock := RTLBlockInstr.bblock (list (list instr)).

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

  Context (ge : genv).

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

  Inductive step_instruction : state -> trace -> state -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
        (fn_code f)!pc = Some(RPnop pc') ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' rs m)
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
        (fn_code f)!pc = Some(Iop op args res pc') ->
        eval_operation ge sp op rs##args m = Some v ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
        (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
        eval_addressing ge sp addr rs##args = Some a ->
        Mem.loadv chunk m a = Some v ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
        (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
        eval_addressing ge sp addr rs##args = Some a ->
        Mem.storev chunk m a rs#src = Some m' ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' rs m')
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
        (fn_code f)!pc = Some(Icall sig ros args res pc') ->
        find_function ros rs = Some fd ->
        funsig fd = sig ->
        step (State s f sp pc rs m)
             E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
        (fn_code f)!pc = Some(Itailcall sig ros args) ->
        find_function ros rs = Some fd ->
        funsig fd = sig ->
        Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
        step (State s f (Vptr stk Ptrofs.zero) pc rs m)
             E0 (Callstate s fd rs##args m')
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
        (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
        eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
        external_call ef ge vargs m t vres m' ->
        step (State s f sp pc rs m)
             t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
        (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
        eval_condition cond rs##args m = Some b ->
        pc' = (if b then ifso else ifnot) ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' rs m)
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
        (fn_code f)!pc = Some(Ijumptable arg tbl) ->
        rs#arg = Vint n ->
        list_nth_z tbl (Int.unsigned n) = Some pc' ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk pc rs m or m',
        (fn_code f)!pc = Some(Ireturn or) ->
        Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
        step (State s f (Vptr stk Ptrofs.zero) pc rs m)
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
