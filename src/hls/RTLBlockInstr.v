(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2019-2022 Yann Herklotz <yann@yannherklotz.com>

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

=============
RTLBlockInstr
=============

These instructions are used for ``RTLBlock`` and ``RTLPar``, so that they have
consistent instructions, which greatly simplifies the proofs, as they will by
default have the same instruction syntax and semantics.  The only changes are
therefore at the top-level of the instructions.

.. coq:: none
|*)

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.

Require Import Predicate.
Require Import Vericertlib.

Definition node := positive.

(*|
.. index::
   triple: definition; RTLBlockInstr; instruction

Instruction Definition
======================

First, we define the instructions that can be placed into a basic block, meaning
they won't branch.  The main changes to how instructions are defined in ``RTL``,
is that these instructions don't have a next node, as they will be in a basic
block, and they also have an optional predicate (``pred_op``).
|*)

Inductive instr : Type :=
| RBnop : instr
| RBop :
  option pred_op -> operation -> list reg -> reg -> instr
| RBload :
  option pred_op -> memory_chunk -> addressing -> list reg -> reg -> instr
| RBstore :
  option pred_op -> memory_chunk -> addressing -> list reg -> reg -> instr
| RBsetpred :
  option pred_op -> condition -> list reg -> predicate -> instr.

(*|
.. index::
   triple: definition; RTLBlockInstr; control-flow instruction

Control-Flow Instruction Definition
===================================

These are the instructions that count as control-flow, and will be placed at the
end of the basic blocks.
|*)

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

(*|
Helper Functions
================
|*)

Fixpoint successors_instr (i : cf_instr) : list node :=
  match i with
  | RBcall sig ros args res s => s :: nil
  | RBtailcall sig ros args => nil
  | RBbuiltin ef args res s => s :: nil
  | RBcond cond args ifso ifnot => ifso :: ifnot :: nil
  | RBjumptable arg tbl => tbl
  | RBreturn optarg => nil
  | RBgoto n => n :: nil
  | RBpred_cf p c1 c2 =>
      concat (successors_instr c1 :: successors_instr c2 :: nil)
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
  | RBsetpred p' c args p =>
      fold_left Pos.max args m
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
Definition predset := PMap.t bool.

Definition eval_predf (pr: predset) (p: pred_op) :=
  sat_predicate p (fun x => pr !! (Pos.of_nat x)).

#[global]
 Instance eval_predf_Proper : Proper (eq ==> equiv ==> eq) eval_predf.
Proof.
  unfold Proper. simplify. unfold "==>".
  intros.
  unfold sat_equiv in *. intros. unfold eval_predf. subst. apply H0.
Qed.

#[local] Open Scope pred_op.

Lemma eval_predf_Pand :
  forall ps p p',
    eval_predf ps (p ∧ p') = eval_predf ps p && eval_predf ps p'.
Proof. unfold eval_predf; split; simplify; auto with bool. Qed.

Lemma eval_predf_Por :
  forall ps p p',
    eval_predf ps (p ∨ p') = eval_predf ps p || eval_predf ps p'.
Proof. unfold eval_predf; split; simplify; auto with bool. Qed.

Lemma eval_predf_pr_equiv :
  forall p ps ps',
    (forall x, ps !! x = ps' !! x) ->
    eval_predf ps p = eval_predf ps' p.
Proof.
  induction p; simplify; auto;
    try (unfold eval_predf; simplify;
         repeat (destruct_match; []); inv Heqp0; rewrite <- H; auto);
    [repeat rewrite eval_predf_Pand|repeat rewrite eval_predf_Por];
    erewrite IHp1; try eassumption; erewrite IHp2; eauto.
Qed.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

(*|
Instruction State
-----------------

Definition of the instruction state, which contains the following:

:is_rs: This is the current state of the registers.
:is_ps: This is the current state of the predicate registers, which is in a
  separate namespace and area compared to the standard registers in [is_rs].
:is_mem: The current state of the memory.
|*)

Record instr_state := mk_instr_state {
                         is_rs: regset;
                         is_ps: predset;
                         is_mem: mem;
                       }.

(*|
Top-Level Type Definitions
==========================
|*)

Section DEFINITION.

  Context {bblock_body: Type}.

  Record bblock : Type := mk_bblock {
                             bb_body: list bblock_body;
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
           (rs: regset)          (**r register state in calling function *)
           (pr: predset),        (**r predicate state of the calling
                                        function *)
      stackframe.

(*|
State Definition
----------------

Definition of the ``state`` type, which is used by the ``step`` functions.  This
state definition is a bit strange when compared to other state definitions in
CompCert.  The main reason for that is the inclusion of ``list bblock_body``,
even though theoretically this is not necessary as one can use the program
counter ``pc`` to index the current function and find the whole basic block that
needs to be executed.

However, the state definition needs to be viable for a translation from ``RTL``
into ``RTLBlock``, as well as larger grained optimisations such as scheduling.
The proof of semantic correctness of the first translation requires that the
instructions are executed one after another.  As it is not possible to perform
multiple steps in the input language for one step in the output language,
without showing that the ``state`` is reduced by some measure, the current basic
block needs to be present inside of the state.

The ideal solution to this would be to have two indices, one which finds the
current basic block to execute, and another which keeps track of the offset.
This would make the basic block generation proof much simpler, because there is
a direct correlation between the program counter in ``RTL`` and the program
counter in addition to the offset in ``RTLBlock``.

On the other hand, the best solution for proving scheduling correct would be a
pure big step style semantics for executing the basic block.  This would not
need to include anything relating to the basic block in the state, as it would
execute each basic block at a time.  Referring to each instruction individually
becomes impossible then, because the state transition skips over it directly.

Finally, the way the state is actually implemented is using a mixture of the two
methods above.  Instead of having two indices, the internal index is instead a
list of remaining instructions to executed in the current block.  In case of
transformations that need to reason about each instruction individually, the
list of instructions will be reduced one instruction at a time.  However, in the
case of transformations that only need to reason about basic blocks at a time
will only use the fact that one can transform a list of instructions into a next
state transition (``JumpState``).
|*)

  Variant state : Type :=
    | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (il: list bblock_body)   (**r basic block body that is
                                           currently executing. *)
             (rs: regset)             (**r register state *)
             (pr: predset)            (**r predicate register state *)
             (m: mem),                (**r memory state *)
        state
    | JumpState:
        forall (stack: list stackframe) (**r call stack *)
               (f: function)            (**r current function *)
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

End DEFINITION.

(*|
Semantics
=========
|*)

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

  Inductive eval_pred:
    option pred_op -> instr_state -> instr_state -> instr_state -> Prop :=
  | eval_pred_true:
    forall i i' p,
      eval_predf (is_ps i) p = true ->
      eval_pred (Some p) i i' i'
  | eval_pred_false:
    forall i i' p,
      eval_predf (is_ps i) p = false ->
      eval_pred (Some p) i i' i
  | eval_pred_none:
    forall i i', eval_pred None i i' i.

(*|
.. index::
   triple: semantics; RTLBlockInstr; instruction

Step Instruction
=============================
|*)

  Variant step_instr: val -> instr_state -> instr -> instr_state -> Prop :=
  | exec_RBnop:
    forall sp ist,
      step_instr sp ist RBnop ist
  | exec_RBop:
    forall op v res args rs m sp p ist pr,
      eval_operation ge sp op rs##args m = Some v ->
      eval_pred p (mk_instr_state rs pr m)
                (mk_instr_state (rs#res <- v) pr m) ist ->
      step_instr sp (mk_instr_state rs pr m) (RBop p op args res) ist
  | exec_RBload:
    forall addr rs args a chunk m v dst sp p pr ist,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      eval_pred p (mk_instr_state rs pr m)
                (mk_instr_state (rs#dst <- v) pr m) ist ->
      step_instr sp (mk_instr_state rs pr m)
                 (RBload p chunk addr args dst) ist
  | exec_RBstore:
    forall addr rs args a chunk m src m' sp p pr ist,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      eval_pred p (mk_instr_state rs pr m)
                (mk_instr_state rs pr m') ist ->
      step_instr sp (mk_instr_state rs pr m)
                 (RBstore p chunk addr args src) ist
  | exec_RBsetpred:
    forall sp rs pr m p c b args p' ist,
      Op.eval_condition c rs##args m = Some b ->
      eval_pred p' (mk_instr_state rs pr m)
                (mk_instr_state rs (pr#p <- b) m) ist ->
      step_instr sp (mk_instr_state rs pr m)
                 (RBsetpred p' c args p) ist.

  Inductive step_list {A} (step_i: val -> instr_state -> A -> instr_state -> Prop):
    val -> instr_state -> list A -> instr_state -> Prop :=
  | exec_RBcons:
    forall state i state' state'' instrs sp,
      step_i sp state i state' ->
      step_list step_i sp state' instrs state'' ->
      step_list step_i sp state (i :: instrs) state''
  | exec_RBnil:
    forall state sp,
      step_list step_i sp state nil state.

(*|
.. index::
   triple: semantics; RTLBlockInstr; control-flow instruction

Step Control-Flow Instruction
=============================
|*)

  Inductive step_cf_instr: state -> cf_instr -> trace -> state -> Prop :=
  | exec_RBcall:
    forall s f sp rs m res fd ros sig args pc pc' pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step_cf_instr
        (JumpState s f sp pc rs pr m) (RBcall sig ros args res pc')
        E0 (Callstate (Stackframe res f sp pc' rs pr :: s) fd rs##args m)
  | exec_RBtailcall:
    forall s f stk rs m sig ros args fd m' pc pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr
        (JumpState s f (Vptr stk Ptrofs.zero) pc rs pr m)
        (RBtailcall sig ros args)
        E0 (Callstate s fd rs##args m')
  | exec_RBbuiltin:
    forall s f sp rs m ef args res pc' vargs t vres m' pc pr bb' cf',
      f.(fn_code)!pc' = Some (mk_bblock bb' cf') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step_cf_instr
        (JumpState s f sp pc rs pr m) (RBbuiltin ef args res pc')
        t (State s f sp pc' bb' (regmap_setres res vres rs) pr m')
  | exec_RBcond:
    forall s f sp rs m cond args ifso ifnot b pc pc' pr bb' cf',
      f.(fn_code)!pc' = Some (mk_bblock bb' cf') ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step_cf_instr
        (JumpState s f sp pc rs pr m)
        (RBcond cond args ifso ifnot)
        E0 (State s f sp pc' bb' rs pr m)
  | exec_RBjumptable:
    forall s f sp rs m arg tbl n pc pc' pr bb' cf',
      f.(fn_code)!pc' = Some (mk_bblock bb' cf') ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step_cf_instr
        (JumpState s f sp pc rs pr m)
        (RBjumptable arg tbl)
        E0 (State s f sp pc' bb' rs pr m)
  | exec_RBreturn:
    forall s f stk rs m or pc m' pr,
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr
        (JumpState s f (Vptr stk Ptrofs.zero) pc rs pr m)
        (RBreturn or)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_RBgoto:
    forall s f sp pc rs pr m pc' bb' cf',
      f.(fn_code)!pc' = Some (mk_bblock bb' cf') ->
      step_cf_instr (JumpState s f sp pc rs pr m)
                    (RBgoto pc') E0 (State s f sp pc' bb' rs pr m)
  | exec_RBpred_cf:
    forall s f sp pc rs pr m cf1 cf2 st' p t,
      step_cf_instr
        (JumpState s f sp pc
               rs pr m) (if eval_predf pr p then cf1 else cf2) t st' ->
      step_cf_instr
        (JumpState s f sp pc rs pr m) (RBpred_cf p cf1 cf2)
        t st'.

End RELSEM.
