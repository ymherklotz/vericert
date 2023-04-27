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

Require Import vericert.hls.FunctionalUnits.
Require Import Predicate.
Require Import Vericertlib.

Definition node := positive.
Definition predicate := positive.
Definition pred_op := @pred_op predicate.

Inductive instr : Type :=
| FUnop : instr
| FUop : option pred_op -> operation -> list reg -> reg -> instr
| FUread : positive -> positive -> reg -> instr
| FUwrite : positive -> positive -> reg -> instr
| FUsetpred : option pred_op -> condition -> list reg -> predicate -> instr.

Inductive cf_instr : Type :=
| FUcall : signature -> reg + ident -> list reg -> reg -> node -> cf_instr
| FUtailcall : signature -> reg + ident -> list reg -> cf_instr
| FUbuiltin : external_function -> list (builtin_arg reg) ->
              builtin_res reg -> node -> cf_instr
| FUcond : condition -> list reg -> node -> node -> cf_instr
| FUjumptable : reg -> list node -> cf_instr
| FUreturn : option reg -> cf_instr
| FUgoto : node -> cf_instr
| FUpred_cf : pred_op -> cf_instr -> cf_instr -> cf_instr.

Fixpoint successors_instr (i : cf_instr) : list node :=
  match i with
  | FUcall sig ros args res s => s :: nil
  | FUtailcall sig ros args => nil
  | FUbuiltin ef args res s => s :: nil
  | FUcond cond args ifso ifnot => ifso :: ifnot :: nil
  | FUjumptable arg tbl => tbl
  | FUreturn optarg => nil
  | FUgoto n => n :: nil
  | FUpred_cf p c1 c2 => concat (successors_instr c1 :: successors_instr c2 :: nil)
  end.

Definition max_reg_instr (m: positive) (i: instr) :=
  match i with
  | FUnop => m
  | FUop p op args res =>
      fold_left Pos.max args (Pos.max res m)
  | FUread p1 p2 r => Pos.max m r
  | FUwrite p1 p2 r => Pos.max m r
  | FUsetpred p' c args p =>
      fold_left Pos.max args m
  end.

Fixpoint max_reg_cfi (m : positive) (i : cf_instr) :=
  match i with
  | FUcall sig (inl r) args res s =>
      fold_left Pos.max args (Pos.max r (Pos.max res m))
  | FUcall sig (inr id) args res s =>
      fold_left Pos.max args (Pos.max res m)
  | FUtailcall sig (inl r) args =>
      fold_left Pos.max args (Pos.max r m)
  | FUtailcall sig (inr id) args =>
      fold_left Pos.max args m
  | FUbuiltin ef args res s =>
      fold_left Pos.max (params_of_builtin_args args)
                (fold_left Pos.max (params_of_builtin_res res) m)
  | FUcond cond args ifso ifnot => fold_left Pos.max args m
  | FUjumptable arg tbl => Pos.max arg m
  | FUreturn None => m
  | FUreturn (Some arg) => Pos.max arg m
  | FUgoto n => m
  | FUpred_cf p c1 c2 => Pos.max (max_reg_cfi m c1) (max_reg_cfi m c2)
  end.

Definition regset := Regmap.t val.
Definition predset := PMap.t bool.

Definition eval_predf (pr: predset) (p: pred_op) :=
  sat_predicate p (fun x => pr !! x).

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
    try (unfold eval_predf; simplify; repeat (destruct_match; []); inv Heqp0; rewrite <- H; auto);
    [repeat rewrite eval_predf_Pand|repeat rewrite eval_predf_Por];
    erewrite IHp1; try eassumption; erewrite IHp2; eauto.
Qed.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

Definition bblock_body := list (list (list instr)).

Record bblock : Type :=
  mk_bblock {
      bb_body: bblock_body;
      bb_exit: cf_instr
    }.

Definition code: Type := PTree.t bblock.

Record function: Type :=
  mkfunction {
      fn_sig: signature;
      fn_params: list reg;
      fn_stacksize: Z;
      fn_code: code;
      fn_funct_units: resources;
      fn_entrypoint: node;
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
         (pr: predset),        (**r predicate state of the calling function *)
    stackframe.

Inductive state : Type :=
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

Record instr_state := mk_instr_state {
                         is_rs: regset;
                         is_ps: predset;
                         is_mem: mem;
                       }.

Definition genv := Genv.t fundef unit.

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

  Inductive eval_pred: option pred_op -> instr_state -> instr_state -> instr_state -> Prop :=
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

  Inductive step_instr: val -> instr_state -> instr -> instr_state -> Prop :=
  | exec_FUnop:
    forall sp ist,
      step_instr sp ist FUnop ist
  | exec_FUop:
    forall op v res args rs m sp p ist pr,
      eval_operation ge sp op rs##args m = Some v ->
      eval_pred p (mk_instr_state rs pr m) (mk_instr_state (rs#res <- v) pr m) ist ->
      step_instr sp (mk_instr_state rs pr m) (FUop p op args res) ist
  | exec_FUsetpred:
    forall sp rs pr m p c b args p' ist,
      Op.eval_condition c rs##args m = Some b ->
      eval_pred p' (mk_instr_state rs pr m) (mk_instr_state rs (pr#p <- b) m) ist ->
      step_instr sp (mk_instr_state rs pr m) (FUsetpred p' c args p) ist.

  Inductive step_instr_list: val -> instr_state -> list instr -> instr_state -> Prop :=
  | exec_RBcons:
    forall state i state' state'' instrs sp,
      step_instr sp state i state' ->
      step_instr_list sp state' instrs state'' ->
      step_instr_list sp state (i :: instrs) state''
  | exec_RBnil:
    forall state sp,
      step_instr_list sp state nil state.

  Inductive step_instr_seq (sp : val)
    : instr_state -> list (list instr) -> instr_state -> Prop :=
  | exec_instr_seq_cons:
    forall state i state' state'' instrs,
      step_instr_list sp state i state' ->
      step_instr_seq sp state' instrs state'' ->
      step_instr_seq sp state (i :: instrs) state''
  | exec_instr_seq_nil:
    forall state,
      step_instr_seq sp state nil state.

  Inductive step_instr_block (sp : val)
    : instr_state -> bblock_body -> instr_state -> Prop :=
  | exec_instr_block_cons:
    forall state i state' state'' instrs,
      step_instr_seq sp state i state' ->
      step_instr_block sp state' instrs state'' ->
      step_instr_block sp state (i :: instrs) state''
  | exec_instr_block_nil:
    forall state,
      step_instr_block sp state nil state.

  Inductive step_cf_instr: state -> cf_instr -> trace -> state -> Prop :=
  | exec_FUcall:
    forall s f sp rs m res fd ros sig args pc pc' pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step_cf_instr (State s f sp pc rs pr m) (FUcall sig ros args res pc')
                    E0 (Callstate (Stackframe res f sp pc' rs pr :: s) fd rs##args m)
  | exec_FUtailcall:
    forall s f stk rs m sig ros args fd m' pc pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f (Vptr stk Ptrofs.zero) pc rs pr m) (FUtailcall sig ros args)
                    E0 (Callstate s fd rs##args m')
  | exec_FUbuiltin:
    forall s f sp rs m ef args res pc' vargs t vres m' pc pr,
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step_cf_instr (State s f sp pc rs pr m) (FUbuiltin ef args res pc')
                    t (State s f sp pc' (regmap_setres res vres rs) pr m')
  | exec_FUcond:
    forall s f sp rs m cond args ifso ifnot b pc pc' pr,
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step_cf_instr (State s f sp pc rs pr m) (FUcond cond args ifso ifnot)
                    E0 (State s f sp pc' rs pr m)
  | exec_FUjumptable:
    forall s f sp rs m arg tbl n pc pc' pr,
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step_cf_instr (State s f sp pc rs pr m) (FUjumptable arg tbl)
                    E0 (State s f sp pc' rs pr m)
  | exec_FUreturn:
    forall s f stk rs m or pc m' pr,
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f (Vptr stk Ptrofs.zero) pc rs pr m) (FUreturn or)
                    E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_FUgoto:
    forall s f sp pc rs pr m pc',
      step_cf_instr (State s f sp pc rs pr m) (FUgoto pc') E0 (State s f sp pc' rs pr m)
  | exec_FUpred_cf:
    forall s f sp pc rs pr m cf1 cf2 st' p t,
      step_cf_instr (State s f sp pc rs pr m) (if eval_predf pr p then cf1 else cf2) t st' ->
      step_cf_instr (State s f sp pc rs pr m) (FUpred_cf p cf1 cf2) t st'.

  Inductive step: state -> trace -> state -> Prop :=
  | exec_bblock:
    forall s f sp pc rs rs' m m' t s' bb pr pr',
      f.(fn_code)!pc = Some bb ->
      step_instr_block sp (mk_instr_state rs pr m) bb.(bb_body) (mk_instr_state rs' pr' m') ->
      step_cf_instr (State s f sp pc rs' pr' m') bb.(bb_exit) t s' ->
      step (State s f sp pc rs pr m) t s'
  | exec_function_internal:
    forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
           E0 (State s
                     f
                     (Vptr stk Ptrofs.zero)
                     f.(fn_entrypoint)
                         (init_regs args f.(fn_params))
                         (PMap.init false) m')
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

Definition max_reg_bblock (m : positive) (pc : node) (bb : bblock) :=
  let max_body := fold_left (fun x l => fold_left (fun x' l' => fold_left max_reg_instr l' x') l x) bb.(bb_body) m in
  max_reg_cfi max_body bb.(bb_exit).

Definition max_reg_function (f: function) :=
  Pos.max
    (PTree.fold max_reg_bblock f.(fn_code) 1%positive)
    (Pos.max (fold_left Pos.max f.(fn_params) 1%positive)
             (max_reg_resources f.(fn_funct_units))).

Definition max_pc_function (f: function) : positive :=
  PTree.fold (fun m pc i => (Pos.max m
                                     (pc + match Zlength i.(bb_body)
                                           with Z.pos p => p | _ => 1 end))%positive)
             f.(fn_code) 1%positive.
