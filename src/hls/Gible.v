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

=====
Gible
=====

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
Require Import compcert.common.Smallstep.
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

(*|
.. index::
   triple: definition; RTLBlockInstr; control-flow instruction

Control-Flow Instruction Definition
===================================

These are the instructions that count as control-flow, and will be placed at the
end of the basic blocks.
|*)

Variant cf_instr : Type :=
| RBcall : signature -> reg + ident -> list reg -> reg -> node -> cf_instr
| RBtailcall : signature -> reg + ident -> list reg -> cf_instr
| RBbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> cf_instr
| RBcond : condition -> list reg -> node -> node -> cf_instr
| RBjumptable : reg -> list node -> cf_instr
| RBreturn : option reg -> cf_instr
| RBgoto : node -> cf_instr.

Variant instr : Type :=
| RBnop : instr
| RBop :
  option pred_op -> operation -> list reg -> reg -> instr
| RBload :
  option pred_op -> memory_chunk -> addressing -> list reg -> reg -> instr
| RBstore :
  option pred_op -> memory_chunk -> addressing -> list reg -> reg -> instr
| RBsetpred :
  option pred_op -> condition -> list reg -> predicate -> instr
| RBexit : option pred_op -> cf_instr -> instr.

(*|
Helper Functions
================
|*)

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

Definition max_reg_cfi (m : positive) (i : cf_instr) :=
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
  | RBexit _ c => max_reg_cfi m c
  end.

Definition max_pred_instr (m: positive) (i: instr) :=
  match i with
  | RBop (Some p) op args res => Pos.max m (max_predicate p)
  | RBload (Some p) chunk addr args dst => Pos.max m (max_predicate p)
  | RBstore (Some p) chunk addr args src => Pos.max m (max_predicate p)
  | RBsetpred (Some p') c args p => Pos.max m (Pos.max p (max_predicate p'))
  | RBexit (Some p) c => Pos.max m (max_predicate p)
  | _ => m
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

Variant istate : Type :=
  | Iexec : instr_state -> istate
  | Iterm : instr_state -> cf_instr -> istate.

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
  forall i i', eval_pred None i i' i'.

Section RELABSTR.

  Context {A B : Type} (ge : Genv.t A B).

(*|
.. index::
   triple: semantics; RTLBlockInstr; instruction

Step Instruction
=============================
|*)

Definition truthyb (ps: predset) (p: option pred_op) :=
  match p with
  | None => true
  | Some p' => eval_predf ps p'
  end.

Variant truthy (ps: predset): option pred_op -> Prop :=
  | truthy_None: truthy ps None
  | truthy_Some: forall p, eval_predf ps p = true -> truthy ps (Some p).

Variant instr_falsy (ps: predset): instr -> Prop :=
  | RBop_falsy :
    forall p op args res,
      eval_predf ps p = false ->
      instr_falsy ps (RBop (Some p) op args res)
  | RBload_falsy:
    forall p chunk addr args dst,
      eval_predf ps p = false ->
      instr_falsy ps (RBload (Some p) chunk addr args dst)
  | RBstore_falsy:
    forall p chunk addr args src,
      eval_predf ps p = false ->
      instr_falsy ps (RBstore (Some p) chunk addr args src)
  | RBsetpred_falsy:
    forall p c args pred,
      eval_predf ps p = false ->
      instr_falsy ps (RBsetpred (Some p) c args pred)
  | RBexit_falsy:
    forall p cf,
      eval_predf ps p = false ->
      instr_falsy ps (RBexit (Some p) cf)
  .

Variant step_instr: val -> istate -> instr -> istate -> Prop :=
  | exec_RBnop:
    forall sp ist,
      step_instr sp (Iexec ist) RBnop (Iexec ist)
  | exec_RBop:
    forall op v res args rs m sp p pr,
      eval_operation ge sp op rs##args m = Some v ->
      truthy pr p ->
      step_instr sp (Iexec (mk_instr_state rs pr m)) (RBop p op args res)
                 (Iexec (mk_instr_state (rs#res <- v) pr m))
  | exec_RBload:
    forall addr rs args a chunk m v dst sp p pr,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      truthy pr p ->
      step_instr sp (Iexec (mk_instr_state rs pr m))
                 (RBload p chunk addr args dst) (Iexec (mk_instr_state (rs#dst <- v) pr m))
  | exec_RBstore:
    forall addr rs args a chunk m src m' sp p pr,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      truthy pr p ->
      step_instr sp (Iexec (mk_instr_state rs pr m))
                 (RBstore p chunk addr args src) (Iexec (mk_instr_state rs pr m'))
  | exec_RBsetpred:
    forall sp rs pr m p c b args p',
      Op.eval_condition c rs##args m = Some b ->
      truthy pr p' ->
      step_instr sp (Iexec (mk_instr_state rs pr m))
                 (RBsetpred p' c args p) (Iexec (mk_instr_state rs (pr#p <- b) m))
  | exec_RBexit:
    forall p c sp i,
      truthy (is_ps i) p ->
      step_instr sp (Iexec i) (RBexit p c) (Iterm i c)
  | exec_RB_falsy :
    forall sp st i,
      instr_falsy (is_ps st) i ->
      step_instr sp (Iexec st) i (Iexec st)
.

End RELABSTR.

(*|
A big-step semantics describing the execution of a list of instructions.  This
uses a higher-order function ``step_i``, so that this ``Inductive`` can be
nested to describe the execution of nested lists.
|*)

Inductive step_list {A} (step_i: val -> istate -> A -> istate -> Prop):
  val -> istate -> list A -> istate -> Prop :=
| exec_RBcons :
  forall state i state' state'' instrs sp cf,
    step_i sp (Iexec state) i (Iexec state') ->
    step_list step_i sp (Iexec state') instrs (Iterm state'' cf) ->
    step_list step_i sp (Iexec state) (i :: instrs) (Iterm state'' cf)
| exec_RBterm :
  forall state sp i state' cf instrs,
    step_i sp (Iexec state) i (Iterm state' cf) ->
    step_list step_i sp (Iexec state) (i :: instrs) (Iterm state' cf).

Inductive step_list2 {A} (step_i: val -> istate -> A -> istate -> Prop):
  val -> istate -> list A -> istate -> Prop :=
| exec_RBcons2 :
  forall i0 i1 i2 i instrs sp,
    step_i sp i0 i i1 ->
    step_list2 step_i sp i1 instrs i2 ->
    step_list2 step_i sp i0 (i :: instrs) i2
| exec_RBnil2 :
  forall sp i, step_list2 step_i sp i nil i.

Inductive step_list_inter {A} (step_i: val -> istate -> A -> istate -> Prop):
  val -> istate -> list A -> istate -> Prop :=
| exec_term_RBcons :
  forall i0 i1 i2 i instrs sp,
    step_i sp (Iexec i0) i i1 ->
    step_list_inter step_i sp i1 instrs i2 ->
    step_list_inter step_i sp (Iexec i0) (i :: instrs) i2
| exec_term_RBnil :
  forall sp i, step_list_inter step_i sp i nil i
| exec_term_RBcons_term :
  forall i cf l sp,
    step_list_inter step_i sp (Iterm i cf) l (Iterm i cf).

(*|
Top-Level Type Definitions
==========================
|*)

Module Type BlockType.

  Parameter t: Type.
  Parameter foldl : forall A, (A -> instr -> A) -> t -> A -> A.
  Parameter length : t -> nat.
  Parameter step: forall A B, Genv.t A B -> val -> istate -> t -> istate -> Prop.

  Arguments step [A B].
  Arguments foldl [A].

End BlockType.

Module Gible(B : BlockType).

  Definition code: Type := PTree.t B.t.

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

The definition of ``state`` is normal now, and is directly the same as in other
intermediate languages.  The main difference in the execution of the semantics,
though is that executing basic blocks uses big-step semantics.
|*)

  Variant state : Type :=
    | State:
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

(*|
Old version of state
~~~~~~~~~~~~~~~~~~~~

The definition of state used to be a bit strange when compared to other state
definitions in CompCert.  The main reason for that is the inclusion of ``list
bblock_body``, even though theoretically this is not necessary as one can use
the program counter ``pc`` to index the current function and find the whole
basic block that needs to be executed.

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

Semantics
=========
|*)

  Section RELSEM.

    Definition genv := Genv.t fundef unit.

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

(*|
.. index::
   triple: semantics; RTLBlockInstr; control-flow instruction

Step Control-Flow Instruction
=============================

These control-flow instruction semantics are essentially the same as in RTL,
with the addition of a recursive conditional instruction, which is used to
support if-conversion.
|*)

    Inductive step_cf_instr: state -> cf_instr -> trace -> state -> Prop :=
    | exec_RBcall:
      forall s f sp rs m res fd ros sig args pc pc' pr,
        find_function ros rs = Some fd ->
        funsig fd = sig ->
        step_cf_instr
          (State s f sp pc rs pr m) (RBcall sig ros args res pc')
          E0 (Callstate (Stackframe res f sp pc' rs pr :: s) fd rs##args m)
    | exec_RBtailcall:
      forall s f stk rs m sig ros args fd m' pc pr,
        find_function ros rs = Some fd ->
        funsig fd = sig ->
        Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
        step_cf_instr
          (State s f (Vptr stk Ptrofs.zero) pc rs pr m)
          (RBtailcall sig ros args)
          E0 (Callstate s fd rs##args m')
    | exec_RBbuiltin:
      forall s f sp rs m ef args res pc' vargs t vres m' pc pr,
        eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
        external_call ef ge vargs m t vres m' ->
        step_cf_instr
          (State s f sp pc rs pr m) (RBbuiltin ef args res pc')
          t (State s f sp pc' (regmap_setres res vres rs) pr m')
    | exec_RBcond:
      forall s f sp rs m cond args ifso ifnot b pc pc' pr,
        eval_condition cond rs##args m = Some b ->
        pc' = (if b then ifso else ifnot) ->
        step_cf_instr
          (State s f sp pc rs pr m)
          (RBcond cond args ifso ifnot)
          E0 (State s f sp pc' rs pr m)
    | exec_RBjumptable:
      forall s f sp rs m arg tbl n pc pc' pr,
        rs#arg = Vint n ->
        list_nth_z tbl (Int.unsigned n) = Some pc' ->
        step_cf_instr
          (State s f sp pc rs pr m)
          (RBjumptable arg tbl)
          E0 (State s f sp pc' rs pr m)
    | exec_RBreturn:
      forall s f stk rs m or pc m' pr,
        Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
        step_cf_instr
          (State s f (Vptr stk Ptrofs.zero) pc rs pr m)
          (RBreturn or)
          E0 (Returnstate s (regmap_optget or Vundef rs) m')
    | exec_RBgoto:
      forall s f sp pc rs pr m pc',
        step_cf_instr (State s f sp pc rs pr m)
                      (RBgoto pc') E0 (State s f sp pc' rs pr m).

    Lemma step_cf_instr_det :
      forall st cf t st1 st2,
        step_cf_instr st cf t st1 ->
        step_cf_instr st cf t st2 ->
        st1 = st2.
    Proof using.
      inversion 1; subst; simplify; clear H;
        match goal with H: context[step_cf_instr] |- _ => inv H end; crush;
        assert (vargs0 = vargs) by eauto using eval_builtin_args_determ; subst;
        assert (vres = vres0 /\ m' = m'0) by eauto using external_call_deterministic; crush.
    Qed.

(*|
Top-level step
--------------

The step function itself then uses this big step of the list of instructions to
then show a transition from basic block to basic block.  The one particular
aspect of this is that the basic block is also part of the state, which has to
be correctly set during the execution of the function.  Function calls and
function returns then also need to set the basic block properly.  This means
that the basic block of the returning function also needs to be stored in the
stackframe, as that is the only assumption one can make when returning from a
function.
|*)

    Variant step: state -> trace -> state -> Prop :=
      | exec_bblock:
        forall s f sp pc rs rs' m m' bb pr pr' t state cf,
          f.(fn_code) ! pc = Some bb ->
          B.step ge sp (Iexec (mk_instr_state rs pr m)) bb (Iterm (mk_instr_state rs' pr' m') cf) ->
          step_cf_instr (State s f sp pc rs' pr' m') cf t state ->
          step (State s f sp pc rs pr m) t state
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

(*|
Semantics
=========

We first describe the semantics by assuming a global program environment with
type ~genv~ which was declared earlier.
|*)

  Definition semantics (p: program) :=
    Semantics step (initial_state p) final_state (Genv.globalenv p).

  Definition max_reg_block (m: positive) (n: node) (i: B.t) := B.foldl max_reg_instr i m.

  Definition max_pred_block (m: positive) (n: node) (i: B.t) := B.foldl max_pred_instr i m.

  Definition max_reg_function (f: function) :=
    Pos.max
      (PTree.fold max_reg_block f.(fn_code) 1%positive)
      (fold_left Pos.max f.(fn_params) 1%positive).

  Definition max_pred_function (f: function) :=
    PTree.fold max_pred_block f.(fn_code) 1%positive.

  Definition max_pc_function (f: function) : positive :=
    PTree.fold
      (fun m pc i =>
         (Pos.max m
                  (pc + match Z.of_nat (B.length i)
                        with Z.pos p => p | _ => 1 end))%positive)
      f.(fn_code) 1%positive.

  Definition all_successors (b: B.t) : list node :=
    B.foldl (fun ns i =>
               match i with
               | RBexit _ cf => successors_instr cf ++ ns
               | _ => ns
               end
            ) b nil.

    Definition pred_uses i :=
      match i with
      | RBop (Some p) _ _ _
      | RBload (Some p) _ _ _ _
      | RBstore (Some p) _ _ _ _
      | RBexit (Some p) _ => predicate_use p
      | RBsetpred (Some p) _ _ p' => p' :: predicate_use p
      | _ => nil
      end.

End Gible.
