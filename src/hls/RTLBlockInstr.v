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

Require Import Coq.micromega.Lia.

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
Require Import vericert.hls.Sat.

Local Open Scope rtl.

Definition node := positive.
Definition predicate := positive.

Inductive pred_op : Type :=
| Pvar: predicate -> pred_op
| Pnot: pred_op -> pred_op
| Pand: pred_op -> pred_op -> pred_op
| Por: pred_op -> pred_op -> pred_op.

Fixpoint sat_predicate (p: pred_op) (a: asgn) : bool :=
  match p with
  | Pvar p' => a (Pos.to_nat p')
  | Pnot p' => negb (sat_predicate p' a)
  | Pand p1 p2 => sat_predicate p1 a && sat_predicate p2 a
  | Por p1 p2 => sat_predicate p1 a || sat_predicate p2 a
  end.

Fixpoint mult {A: Type} (a b: list (list A)) : list (list A) :=
  match a with
  | nil => nil
  | l :: ls => mult ls b ++ (List.map (fun x => l ++ x) b)
  end.

Lemma satFormula_concat:
  forall a b agn,
  satFormula a agn ->
  satFormula b agn ->
  satFormula (a ++ b) agn.
Proof. induction a; crush. Qed.

Lemma satFormula_concat2:
  forall a b agn,
  satFormula (a ++ b) agn ->
  satFormula a agn /\ satFormula b agn.
Proof.
  induction a; simplify;
    try apply IHa in H1; crush.
Qed.

Lemma satClause_concat:
  forall a a1 a0,
  satClause a a1 ->
  satClause (a0 ++ a) a1.
Proof. induction a0; crush. Qed.

Lemma satClause_concat2:
  forall a a1 a0,
  satClause a0 a1 ->
  satClause (a0 ++ a) a1.
Proof.
  induction a0; crush.
  inv H; crush.
Qed.

Lemma satClause_concat3:
  forall a b c,
  satClause (a ++ b) c ->
  satClause a c \/ satClause b c.
Proof.
  induction a; crush.
  inv H; crush.
  apply IHa in H0; crush.
  inv H0; crush.
Qed.

Lemma satFormula_mult':
  forall p2 a a0,
  satFormula p2 a0 \/ satClause a a0 ->
  satFormula (map (fun x : list lit => a ++ x) p2) a0.
Proof.
  induction p2; crush.
  - inv H. inv H0. apply satClause_concat. auto.
    apply satClause_concat2; auto.
  - apply IHp2.
    inv H; crush; inv H0; crush.
Qed.

Lemma satFormula_mult2':
  forall p2 a a0,
  satFormula (map (fun x : list lit => a ++ x) p2) a0 ->
  satClause a a0 \/ satFormula p2 a0.
Proof.
  induction p2; crush.
  apply IHp2 in H1. inv H1; crush.
  apply satClause_concat3 in H0.
  inv H0; crush.
Qed.

Lemma satFormula_mult:
  forall p1 p2 a,
  satFormula p1 a \/ satFormula p2 a ->
  satFormula (mult p1 p2) a.
Proof.
  induction p1; crush.
  apply satFormula_concat; crush.
  inv H. inv H0.
  apply IHp1. auto.
  apply IHp1. auto.
  apply satFormula_mult';
  inv H; crush.
Qed.

Lemma satFormula_mult2:
  forall p1 p2 a,
  satFormula (mult p1 p2) a ->
  satFormula p1 a \/ satFormula p2 a.
Proof.
  induction p1; crush.
  apply satFormula_concat2 in H; crush.
  apply IHp1 in H0.
  inv H0; crush.
  apply satFormula_mult2' in H1. inv H1; crush.
Qed.

Fixpoint trans_pred_temp (bound: nat) (p: pred_op) : option formula :=
  match bound with
  | O => None
  | S n =>
    match p with
    | Pvar p' => Some (((true, Pos.to_nat p') :: nil) :: nil)
    | Pand p1 p2 =>
      match trans_pred_temp n p1, trans_pred_temp n p2 with
      | Some p1', Some p2' =>
        Some (p1' ++ p2')
      | _, _ => None
      end
    | Por p1 p2 =>
      match trans_pred_temp n p1, trans_pred_temp n p2 with
      | Some p1', Some p2' =>
        Some (mult p1' p2')
      | _, _ => None
      end
    | Pnot (Pvar p') => Some (((false, Pos.to_nat p') :: nil) :: nil)
    | Pnot (Pnot p) => trans_pred_temp n p
    | Pnot (Pand p1 p2) => trans_pred_temp n (Por (Pnot p1) (Pnot p2))
    | Pnot (Por p1 p2) => trans_pred_temp n (Pand (Pnot p1) (Pnot p2))
    end
  end.

Fixpoint trans_pred (bound: nat) (p: pred_op) :
  option {fm: formula | forall a,
           sat_predicate p a = true <-> satFormula fm a}.
  refine
  (match bound with
   | O => None
   | S n =>
     match p with
     | Pvar p' => Some (exist _ (((true, Pos.to_nat p') :: nil) :: nil) _)
     | Pand p1 p2 =>
      match trans_pred n p1, trans_pred n p2 with
      | Some (exist _ p1' _), Some (exist _ p2' _) =>
        Some (exist _ (p1' ++ p2') _)
      | _, _ => None
      end
     | Por p1 p2 =>
      match trans_pred n p1, trans_pred n p2 with
      | Some (exist _ p1' _), Some (exist _ p2' _) =>
        Some (exist _ (mult p1' p2') _)
      | _, _ => None
      end
     | Pnot (Pvar p') => Some (exist _ (((false, Pos.to_nat p') :: nil) :: nil) _)
     | Pnot (Pnot p') =>
       match trans_pred n p' with
       | Some (exist _ p1' _) => Some (exist _ p1' _)
       | None => None
       end
     | Pnot (Pand p1 p2) =>
       match trans_pred n (Por (Pnot p1) (Pnot p2)) with
       | Some (exist _ p1' _) => Some (exist _ p1' _)
       | None => None
       end
     | Pnot (Por p1 p2) =>
       match trans_pred n (Pand (Pnot p1) (Pnot p2)) with
       | Some (exist _ p1' _) => Some (exist _ p1' _)
       | None => None
       end
     end
   end); split; intros; simpl in *; auto.
  - inv H. inv H0; auto.
  - split; auto. destruct (a (Pos.to_nat p')) eqn:?; crush.
  - inv H. inv H0. unfold satLit in H. simplify. rewrite H. auto.
    crush.
  - rewrite negb_involutive in H. apply i in H. auto.
  - rewrite negb_involutive. apply i; auto.
  - rewrite negb_andb in H. apply i. auto.
  - rewrite negb_andb. apply i. auto.
  - rewrite negb_orb in H. apply i. auto.
  - rewrite negb_orb. apply i. auto.
  - apply satFormula_concat.
    apply andb_prop in H. inv H. apply i in H0. auto.
    apply andb_prop in H. inv H. apply i0 in H1. auto.
  - apply satFormula_concat2 in H. simplify. apply andb_true_intro.
    split. apply i in H0. auto.
    apply i0 in H1. auto.
  - apply orb_prop in H. inv H; apply satFormula_mult. apply i in H0. auto.
    apply i0 in H0. auto.
  - apply orb_true_intro.
    apply satFormula_mult2 in H. inv H. apply i in H0. auto.
    apply i0 in H0. auto.
Defined.

Definition sat_pred (bound: nat) (p: pred_op) :
  option ({al : alist | sat_predicate p (interp_alist al) = true}
          + {forall a : asgn, sat_predicate p a = false}).
  refine
  ( match trans_pred bound p with
    | Some (exist _ fm _) =>
      match boundedSat bound fm with
      | Some (inleft (exist _ a _)) => Some (inleft (exist _ a _))
      | Some (inright _) => Some (inright _)
      | None => None
      end
    | None => None
    end ).
  - apply i in s2. auto.
  - intros. specialize (n a). specialize (i a).
    destruct (sat_predicate p a). exfalso.
    apply n. apply i. auto. auto.
Defined.

Definition sat_pred_simple (bound: nat) (p: pred_op) :=
  match sat_pred bound p with
  | Some (inleft (exist _ al _)) => Some (Some al)
  | Some (inright _) => Some None
  | None => None
  end.

Definition sat_pred_temp (bound: nat) (p: pred_op) :=
  match trans_pred_temp bound p with
  | Some fm => boundedSatSimple bound fm
  | None => None
  end.

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

Fixpoint eval_predf (pr: predset) (p: pred_op) {struct p} :=
  match p with
  | Pvar p' => PMap.get p' pr
  | Pnot p' => negb (eval_predf pr p')
  | Pand p' p'' => (eval_predf pr p') && (eval_predf pr p'')
  | Por p' p'' => (eval_predf pr p') || (eval_predf pr p'')
  end.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

Record instr_state := mk_instr_state {
  is_rs: regset;
  is_ps: predset;
  is_mem: mem;
}.

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

  Inductive eval_pred: option pred_op -> instr_state -> instr_state -> instr_state -> Prop :=
  | eval_pred_true:
      forall (pr: predset) p rs pr m i,
      eval_predf pr p = true ->
      eval_pred (Some p) (mk_instr_state rs pr m) i i
  | eval_pred_false:
      forall (pr: predset) p rs pr m i,
      eval_predf pr p = false ->
      eval_pred (Some p) (mk_instr_state rs pr m) i (mk_instr_state rs pr m)
  | eval_pred_none:
      forall i i',
      eval_pred None i i' i.

  Inductive step_instr: val -> instr_state -> instr -> instr_state -> Prop :=
  | exec_RBnop:
      forall sp ist,
        step_instr sp ist RBnop ist
  | exec_RBop:
      forall op v res args rs m sp p ist pr,
        eval_operation ge sp op rs##args m = Some v ->
        eval_pred p (mk_instr_state rs pr m) (mk_instr_state (rs#res <- v) pr m) ist ->
        step_instr sp (mk_instr_state rs pr m) (RBop p op args res) ist
  | exec_RBload:
      forall addr rs args a chunk m v dst sp p pr ist,
        eval_addressing ge sp addr rs##args = Some a ->
        Mem.loadv chunk m a = Some v ->
        eval_pred p (mk_instr_state rs pr m) (mk_instr_state (rs#dst <- v) pr m) ist ->
        step_instr sp (mk_instr_state rs pr m) (RBload p chunk addr args dst) ist
  | exec_RBstore:
      forall addr rs args a chunk m src m' sp p pr ist,
        eval_addressing ge sp addr rs##args = Some a ->
        Mem.storev chunk m a rs#src = Some m' ->
        eval_pred p (mk_instr_state rs pr m) (mk_instr_state rs pr m') ist ->
        step_instr sp (mk_instr_state rs pr m) (RBstore p chunk addr args src) ist
  | exec_RBsetpred:
      forall sp rs pr m p c b args,
      Op.eval_condition c rs##args m = Some b ->
      step_instr sp (mk_instr_state rs pr m) (RBsetpred c args p)
                 (mk_instr_state rs (PMap.set p b pr) m).

  Inductive step_cf_instr: state -> cf_instr -> trace -> state -> Prop :=
  | exec_RBcall:
    forall s f sp rs m res fd ros sig args pc pc' pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step_cf_instr (State s f sp pc rs pr m) (RBcall sig ros args res pc')
           E0 (Callstate (Stackframe res f sp pc' rs pr :: s) fd rs##args m)
  | exec_RBtailcall:
      forall s f stk rs m sig ros args fd m' pc pr,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f (Vptr stk Ptrofs.zero) pc rs pr m) (RBtailcall sig ros args)
        E0 (Callstate s fd rs##args m')
  | exec_RBbuiltin:
      forall s f sp rs m ef args res pc' vargs t vres m' pc pr,
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step_cf_instr (State s f sp pc rs pr m) (RBbuiltin ef args res pc')
         t (State s f sp pc' (regmap_setres res vres rs) pr m')
  | exec_RBcond:
      forall s f sp rs m cond args ifso ifnot b pc pc' pr,
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step_cf_instr (State s f sp pc rs pr m) (RBcond cond args ifso ifnot)
        E0 (State s f sp pc' rs pr m)
  | exec_RBjumptable:
      forall s f sp rs m arg tbl n pc pc' pr,
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step_cf_instr (State s f sp pc rs pr m) (RBjumptable arg tbl)
        E0 (State s f sp pc' rs pr m)
  | exec_RBreturn:
      forall s f stk rs m or pc m' pr,
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step_cf_instr (State s f (Vptr stk Ptrofs.zero) pc rs pr m) (RBreturn or)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_RBgoto:
      forall s f sp pc rs pr m pc',
      step_cf_instr (State s f sp pc rs pr m) (RBgoto pc') E0 (State s f sp pc' rs pr m)
  | exec_RBpred_cf:
      forall s f sp pc rs pr m cf1 cf2 st' p t,
      step_cf_instr (State s f sp pc rs pr m) (if eval_predf pr p then cf1 else cf2) t st' ->
      step_cf_instr (State s f sp pc rs pr m) (RBpred_cf p cf1 cf2) t st'.

End RELSEM.
