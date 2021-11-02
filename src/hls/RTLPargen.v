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
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

(*Parameter op_le : Op.operation -> Op.operation -> bool.
Parameter chunk_le : AST.memory_chunk -> AST.memory_chunk -> bool.
Parameter addr_le : Op.addressing -> Op.addressing -> bool.
Parameter cond_le : Op.condition -> Op.condition -> bool.

Fixpoint pred_le (p1 p2: pred_op) : bool :=
  match p1, p2 with
  | Pvar i, Pvar j => (i <=? j)%positive
  | Pnot p1, Pnot p2 => pred_le p1 p2
  | Pand p1 p1', Pand p2 p2' => if pred_le p1 p2 then true else pred_le p1' p2'
  | Por p1 p1', Por p2 p2' => if pred_le p1 p2 then true else pred_le p1' p2'
  | Pvar _, _ => true
  | Pnot _, Pvar _ => false
  | Pnot _, _ => true
  | Pand _ _, Pvar _ => false
  | Pand _ _, Pnot _ => false
  | Pand _ _, _ => true
  | Por _ _, _ => false
  end.

Import Lia.

Lemma pred_le_trans :
  forall p1 p2 p3 b, pred_le p1 p2 = b -> pred_le p2 p3 = b -> pred_le p1 p3 = b.
Proof.
  induction p1; destruct p2; destruct p3; crush.
  destruct b. rewrite Pos.leb_le in *. lia. rewrite Pos.leb_gt in *. lia.
  firstorder.
  destruct (pred_le p1_1 p2_1) eqn:?. subst. destruct (pred_le p2_1 p3_1) eqn:?.
  apply IHp1_1 in Heqb. rewrite Heqb. auto. auto.


Fixpoint expr_le (e1 e2: expression) {struct e2}: bool :=
  match e1, e2 with
  | Ebase r1, Ebase r2 => (R_indexed.index r1 <=? R_indexed.index r2)%positive
  | Ebase _, _ => true
  | Eop op1 elist1 m1, Eop op2 elist2 m2 =>
    if op_le op1 op2 then true
    else if elist_le elist1 elist2 then true
         else expr_le m1 m2
  | Eop _ _ _, Ebase _ => false
  | Eop _ _ _, _ => true
  | Eload chunk1 addr1 elist1 expr1, Eload chunk2 addr2 elist2 expr2 =>
    if chunk_le chunk1 chunk2 then true
    else if addr_le addr1 addr2 then true
         else if elist_le elist1 elist2 then true
              else expr_le expr1 expr2
  | Eload _ _ _ _, Ebase _ => false
  | Eload _ _ _ _, Eop _ _ _ => false
  | Eload _ _ _ _, _ => true
  | Estore m1 chunk1 addr1 elist1 expr1, Estore m2 chunk2 addr2 elist2 expr2 =>
    if expr_le m1 m2 then true
    else if chunk_le chunk1 chunk2 then true
         else if addr_le addr1 addr2 then true
              else if elist_le elist1 elist2 then true
                   else expr_le expr1 expr2
  | Estore _ _ _ _ _, Ebase _ => false
  | Estore _ _ _ _ _, Eop _ _ _ => false
  | Estore _ _ _ _ _, Eload _ _ _ _ => false
  | Estore _ _ _ _ _, _ => true
  | Esetpred p1 cond1 elist1 m1, Esetpred p2 cond2 elist2 m2 =>
    if (p1 <=? p2)%positive then true
    else if cond_le cond1 cond2 then true
         else if elist_le elist1 elist2 then true
              else expr_le m1 m2
  | Esetpred _ _ _ _, Econd _ => true
  | Esetpred _ _ _ _, _ => false
  | Econd eplist1, Econd eplist2 => eplist_le eplist1 eplist2
  | Econd eplist1, _ => false
  end
with elist_le (e1 e2: expression_list) : bool :=
  match e1, e2 with
  | Enil, Enil => true
  | Econs a1 b1, Econs a2 b2 => if expr_le a1 a2 then true else elist_le b1 b2
  | Enil, _ => true
  | _, Enil => false
  end
with eplist_le (e1 e2: expr_pred_list) : bool :=
  match e1, e2 with
  | EPnil, EPnil => true
  | EPcons p1 a1 b1, EPcons p2 a2 b2 =>
    if pred_le p1 p2 then true
    else if expr_le a1 a2 then true else eplist_le b1 b2
  | EPnil, _ => true
  | _, EPnil => false
  end
.*)

Definition ge_preserved {A B C D: Type} (ge: Genv.t A B) (tge: Genv.t C D) : Prop :=
  (forall sp op vl m, Op.eval_operation ge sp op vl m =
                      Op.eval_operation tge sp op vl m)
  /\ (forall sp addr vl, Op.eval_addressing ge sp addr vl =
                         Op.eval_addressing tge sp addr vl).

#[local] Hint Resolve ge_preserved_same : rtlpar.

Ltac rtlpar_crush := crush; eauto with rtlpar.

Inductive match_states_ld : instr_state -> instr_state -> Prop :=
| match_states_ld_intro:
  forall ps ps' rs rs' m m',
    regs_lessdef rs rs' ->
    (forall x, ps !! x = ps' !! x) ->
    Mem.extends m m' ->
    match_states_ld (mk_instr_state rs ps m) (mk_instr_state rs' ps' m').

(*Lemma sems_det:
  forall A ge tge sp f rs ps m,
  ge_preserved ge tge ->
  forall v v' mv mv',
  (@sem_value A (mk_ctx rs ps m sp ge) f v /\ @sem_value A (mk_ctx rs ps m sp tge) f v' -> v = v') /\
  (@sem_mem A (mk_ctx rs ps m sp ge) f mv /\ @sem_mem A (mk_ctx rs ps m sp tge) f mv' -> mv = mv').
Proof. Abort.*)

(*Lemma sem_value_det:
  forall A ge tge sp st f v v',
  ge_preserved ge tge ->
  @sem_value A ge sp st f v ->
  @sem_value A tge sp st f v' ->
  v = v'.
Proof.
  intros. destruct st.
  generalize (sems_det A ge tge sp (mk_instr_state rs m) f H v v'
                      m m);
  crush.
Qed.
Hint Resolve sem_value_det : rtlpar.

Lemma sem_value_det':
  forall FF ge sp s f v v',
  @sem_value FF ge sp s f v ->
  @sem_value FF ge sp s f v' ->
  v = v'.
Proof.
  simplify; eauto with rtlpar.
Qed.

Lemma sem_mem_det:
  forall A ge tge sp st f m m',
  ge_preserved ge tge ->
  @sem_mem A ge sp st f m ->
  @sem_mem A tge sp st f m' ->
  m = m'.
Proof.
  intros. destruct st.
  generalize (sems_det A ge tge sp (mk_instr_state rs m0) f H sp sp m m');
  crush.
Qed.
Hint Resolve sem_mem_det : rtlpar.

Lemma sem_mem_det':
  forall FF ge sp s f m m',
    @sem_mem FF ge sp s f m ->
    @sem_mem FF ge sp s f m' ->
    m = m'.
Proof.
  simplify; eauto with rtlpar.
Qed.

Hint Resolve Val.lessdef_same : rtlpar.

Lemma sem_regset_det:
  forall FF ge tge sp st f v v',
    ge_preserved ge tge ->
    @sem_regset FF ge sp st f v ->
    @sem_regset FF tge sp st f v' ->
    (forall x, v !! x = v' !! x).
Proof.
  intros; unfold regs_lessdef.
  inv H0; inv H1;
  eauto with rtlpar.
Qed.
Hint Resolve sem_regset_det : rtlpar.

Lemma sem_det:
  forall FF ge tge sp st f st' st'',
    ge_preserved ge tge ->
    @sem FF ge sp st f st' ->
    @sem FF tge sp st f st'' ->
    match_states st' st''.
Proof.
  intros.
  destruct st; destruct st'; destruct st''.
  inv H0; inv H1.
  constructor; eauto with rtlpar.
Qed.
Hint Resolve sem_det : rtlpar.

Lemma sem_det':
  forall FF ge sp st f st' st'',
    @sem FF ge sp st f st' ->
    @sem FF ge sp st f st'' ->
    match_states st' st''.
Proof. eauto with rtlpar. Qed.

(*|
Update functions.
|*)
*)

Fixpoint list_translation (l : list reg) (f : forest) {struct l} : list pred_expr :=
  match l with
  | nil => nil
  | i :: l => (f # (Reg i)) :: (list_translation l f)
  end.

Fixpoint replicate {A} (n: nat) (l: A) :=
  match n with
  | O => nil
  | S n => l :: replicate n l
  end.

Definition merge''' x y :=
  match x, y with
  | Some p1, Some p2 => Some (Pand p1 p2)
  | Some p, None | None, Some p => Some p
  | None, None => None
  end.

Definition merge'' x :=
  match x with
  | ((a, e), (b, el)) => (merge''' a b, Econs e el)
  end.

Definition predicated_prod {A B: Type} (p1: predicated A) (p2: predicated B) :=
  NE.map (fun x => match x with ((a, b), (c, d)) => (Pand a c, (b, d)) end)
         (NE.non_empty_prod p1 p2).

Definition predicated_map {A B: Type} (f: A -> B) (p: predicated A): predicated B :=
  NE.map (fun x => (fst x, f (snd x))) p.

(*map (fun x => (fst x, Econs (snd x) Enil)) pel*)
Definition merge' (pel: pred_expr) (tpel: predicated expression_list) :=
  predicated_map (uncurry Econs) (predicated_prod pel tpel).

Fixpoint merge (pel: list pred_expr): predicated expression_list :=
  match pel with
  | nil => NE.singleton (T, Enil)
  | a :: b => merge' a (merge b)
  end.

Definition map_pred_op {A B} (pf: option pred_op * (A -> B)) (pa: option pred_op * A): option pred_op * B :=
  match pa, pf with
  | (p, a), (p', f) => (merge''' p p', f a)
  end.

Definition map_predicated {A B} (pf: predicated (A -> B)) (pa: predicated A): predicated B :=
  predicated_map (fun x => (fst x) (snd x)) (predicated_prod pf pa).

Definition predicated_apply1 {A B} (pf: predicated (A -> B)) (pa: A): predicated B :=
  NE.map (fun x => (fst x, (snd x) pa)) pf.

Definition predicated_apply2 {A B C} (pf: predicated (A -> B -> C)) (pa: A) (pb: B): predicated C :=
  NE.map (fun x => (fst x, (snd x) pa pb)) pf.

Definition predicated_apply3 {A B C D} (pf: predicated (A -> B -> C -> D)) (pa: A) (pb: B) (pc: C): predicated D :=
  NE.map (fun x => (fst x, (snd x) pa pb pc)) pf.

(*Compute merge (((Some (Pvar 2), Ebase (Reg 4))::nil)::((Some (Pvar 3), Ebase (Reg 3))::(Some (Pvar 1), Ebase (Reg 3))::nil)::nil).*)

Definition predicated_from_opt {A: Type} (p: option pred_op) (a: A) :=
  match p with
  | Some p' => NE.singleton (p', a)
  | None => NE.singleton (T, a)
  end.

Definition update (f : forest) (i : instr) : forest :=
  match i with
  | RBnop => f
  | RBop p op rl r =>
    f # (Reg r) <-
    (map_predicated (predicated_from_opt p (Eop op)) (merge (list_translation rl f)))
  | RBload p chunk addr rl r =>
    f # (Reg r) <-
    (map_predicated
     (map_predicated (predicated_from_opt p (Eload chunk addr)) (merge (list_translation rl f)))
     (f # Mem))
  | RBstore p chunk addr rl r =>
    f # Mem <-
    (map_predicated
     (map_predicated
      (predicated_apply2 (map_predicated (predicated_from_opt p Estore) (f # (Reg r))) chunk addr)
      (merge (list_translation rl f))) (f # Mem))
  | RBsetpred p' c addr p => f
  end.

(*|
Implementing which are necessary to show the correctness of the translation validation by showing
that there aren't any more effects in the resultant RTLPar code than in the RTLBlock code.

Get a sequence from the basic block.
|*)

Fixpoint abstract_sequence (f : forest) (b : list instr) : forest :=
  match b with
  | nil => f
  | i :: l => abstract_sequence (update f i) l
  end.

(*|
Check equivalence of control flow instructions.  As none of the basic blocks should have been moved,
none of the labels should be different, meaning the control-flow instructions should match exactly.
|*)

Definition check_control_flow_instr (c1 c2: cf_instr) : bool :=
  if cf_instr_eq c1 c2 then true else false.

(*|
We define the top-level oracle that will check if two basic blocks are equivalent after a scheduling
transformation.
|*)

Definition empty_trees (bb: RTLBlock.bb) (bbt: RTLPar.bb) : bool :=
  match bb with
  | nil =>
    match bbt with
    | nil => true
    | _ => false
    end
  | _ => true
  end.

Definition schedule_oracle (bb: RTLBlock.bblock) (bbt: RTLPar.bblock) : bool :=
  check (abstract_sequence empty (bb_body bb))
        (abstract_sequence empty (concat (concat (bb_body bbt)))) &&
  check_control_flow_instr (bb_exit bb) (bb_exit bbt) &&
  empty_trees (bb_body bb) (bb_body bbt).

Definition check_scheduled_trees := beq2 schedule_oracle.

Ltac solve_scheduled_trees_correct :=
  intros; unfold check_scheduled_trees in *;
  match goal with
  | [ H: context[beq2 _ _ _], x: positive |- _ ] =>
    rewrite beq2_correct in H; specialize (H x)
  end; repeat destruct_match; crush.

Lemma check_scheduled_trees_correct:
  forall f1 f2,
    check_scheduled_trees f1 f2 = true ->
    (forall x y1,
        PTree.get x f1 = Some y1 ->
        exists y2, PTree.get x f2 = Some y2 /\ schedule_oracle y1 y2 = true).
Proof. solve_scheduled_trees_correct; eexists; crush. Qed.

Lemma check_scheduled_trees_correct2:
  forall f1 f2,
    check_scheduled_trees f1 f2 = true ->
    (forall x,
        PTree.get x f1 = None ->
        PTree.get x f2 = None).
Proof. solve_scheduled_trees_correct. Qed.

(*|
Abstract computations
=====================
|*)

(*Definition is_regs i := match i with mk_instr_state rs _ => rs end.
Definition is_mem i := match i with mk_instr_state _ m => m end.

Inductive state_lessdef : instr_state -> instr_state -> Prop :=
  state_lessdef_intro :
    forall rs1 rs2 m1,
    (forall x, rs1 !! x = rs2 !! x) ->
    state_lessdef (mk_instr_state rs1 m1) (mk_instr_state rs2 m1).

(*|
RTLBlock to abstract translation
--------------------------------

Correctness of translation from RTLBlock to the abstract interpretation language.
|*)

Ltac inv_simp :=
  repeat match goal with
  | H: exists _, _ |- _ => inv H
  end; simplify.

Lemma abstract_interp_empty3 :
  forall A ge sp st st',
    @sem A ge sp st empty st' ->
    match_states st st'.
Proof.
  inversion 1; subst; simplify.
  destruct st. inv H1. simplify.
  constructor. unfold regs_lessdef.
  intros. inv H0. specialize (H1 x). inv H1; auto.
  auto.
Qed.*)

Definition check_dest i r' :=
  match i with
  | RBop p op rl r => (r =? r')%positive
  | RBload p chunk addr rl r => (r =? r')%positive
  | _ => false
  end.

Lemma check_dest_dec i r : {check_dest i r = true} + {check_dest i r = false}.
Proof. destruct (check_dest i r); tauto. Qed.

Fixpoint check_dest_l l r :=
  match l with
  | nil => false
  | a :: b => check_dest a r || check_dest_l b r
  end.

Lemma check_dest_l_forall :
  forall l r,
  check_dest_l l r = false ->
  Forall (fun x => check_dest x r = false) l.
Proof. induction l; crush. Qed.

(*Lemma check_dest_l_ex :
  forall l r,
  check_dest_l l r = true ->
  exists a, In a l /\ check_dest a r = true.
Proof.
  induction l; crush.
  destruct (check_dest a r) eqn:?; try solve [econstructor; crush].
  simplify.
  exploit IHl. apply H. inv_simp. econstructor. simplify. right. eassumption.
  auto.
Qed.

Lemma check_dest_l_dec i r : {check_dest_l i r = true} + {check_dest_l i r = false}.
Proof. destruct (check_dest_l i r); tauto. Qed.

Lemma check_dest_l_dec2 l r :
  {Forall (fun x => check_dest x r = false) l}
  + {exists a, In a l /\ check_dest a r = true}.
Proof.
  destruct (check_dest_l_dec l r); [right | left];
  auto using check_dest_l_ex, check_dest_l_forall.
Qed.

Lemma check_dest_l_forall2 :
  forall l r,
  Forall (fun x => check_dest x r = false) l ->
  check_dest_l l r = false.
Proof.
  induction l; crush.
  inv H. apply orb_false_intro; crush.
Qed.

Lemma check_dest_l_ex2 :
  forall l r,
  (exists a, In a l /\ check_dest a r = true) ->
  check_dest_l l r = true.
Proof.
  induction l; crush.
  specialize (IHl r). inv H.
  apply orb_true_intro; crush.
  apply orb_true_intro; crush.
  right. apply IHl. exists x. auto.
Qed.

Lemma check_dest_update :
  forall f i r,
  check_dest i r = false ->
  (update f i) # (Reg r) = f # (Reg r).
Proof.
  destruct i; crush; try apply Pos.eqb_neq in H; apply genmap1; crush.
Qed.

Lemma check_dest_update2 :
  forall f r rl op p,
  (update f (RBop p op rl r)) # (Reg r) = Eop op (list_translation rl f) (f # Mem).
Proof. crush; rewrite map2; auto. Qed.

Lemma check_dest_update3 :
  forall f r rl p addr chunk,
  (update f (RBload p chunk addr rl r)) # (Reg r) = Eload chunk addr (list_translation rl f) (f # Mem).
Proof. crush; rewrite map2; auto. Qed.

Lemma abstr_comp :
  forall l i f x x0,
  abstract_sequence f (l ++ i :: nil) = x ->
  abstract_sequence f l = x0 ->
  x = update x0 i.
Proof. induction l; intros; crush; eapply IHl; eauto. Qed.

Lemma check_list_l_false :
  forall l x r,
  check_dest_l (l ++ x :: nil) r = false ->
  check_dest_l l r = false /\ check_dest x r = false.
Proof.
  simplify.
  apply check_dest_l_forall in H. apply Forall_app in H.
  simplify. apply check_dest_l_forall2; auto.
  apply check_dest_l_forall in H. apply Forall_app in H.
  simplify. inv H1. auto.
Qed.

Lemma check_list_l_true :
  forall l x r,
  check_dest_l (l ++ x :: nil) r = true ->
  check_dest_l l r = true \/ check_dest x r = true.
Proof.
  simplify.
  apply check_dest_l_ex in H; inv_simp.
  apply in_app_or in H. inv H. left.
  apply check_dest_l_ex2. exists x0. auto.
  inv H0; auto.
Qed.

Lemma abstract_sequence_update :
  forall l r f,
  check_dest_l l r = false ->
  (abstract_sequence f l) # (Reg r) = f # (Reg r).
Proof.
  induction l using rev_ind; crush.
  rewrite abstract_seq. rewrite check_dest_update. apply IHl.
  apply check_list_l_false in H. tauto.
  apply check_list_l_false in H. tauto.
Qed.



Lemma sem_update_RBnop :
  forall A ge sp st f st',
  @sem A ge sp st f st' -> sem ge sp st (update f RBnop) st'.
Proof. crush. Qed.

Lemma gen_list_base:
  forall FF ge sp l rs exps st1,
  (forall x, @sem_value FF ge sp st1 (exps # (Reg x)) (rs !! x)) ->
  sem_val_list ge sp st1 (list_translation l exps) rs ## l.
Proof.
  induction l.
  intros. simpl. constructor.
  intros. simpl. eapply Scons; eauto.
Qed.

Lemma abstract_seq_correct_aux:
  forall FF ge sp i st1 st2 st3 f,
    @step_instr FF ge sp st3 i st2 ->
    sem ge sp st1 f st3 ->
    sem ge sp st1 (update f i) st2.
Proof.
  intros; inv H; simplify.
  { simplify; eauto. } (*apply match_states_refl. }*)
  { inv H0. inv H6. destruct st1. econstructor. simplify.
    constructor. intros.
    destruct (resource_eq (Reg res) (Reg x)). inv e.
    rewrite map2. econstructor. eassumption. apply gen_list_base; eauto.
    rewrite Regmap.gss. eauto.
    assert (res <> x). { unfold not in *. intros. apply n. rewrite H0. auto. }
    rewrite Regmap.gso by auto.
    rewrite genmap1 by auto. auto.

    rewrite genmap1; crush. }
  { inv H0. inv H7. constructor. constructor. intros.
    destruct (Pos.eq_dec dst x); subst.
    rewrite map2. econstructor; eauto.
    apply gen_list_base. auto. rewrite Regmap.gss. auto.
    rewrite genmap1. rewrite Regmap.gso by auto. auto.
    unfold not in *; intros. inv H0. auto.
    rewrite genmap1; crush.
  }
  { inv H0. inv H7. constructor. constructor; intros.
    rewrite genmap1; crush.
    rewrite map2. econstructor; eauto.
    apply gen_list_base; auto.
  }
Qed.

Lemma regmap_list_equiv :
  forall A (rs1: Regmap.t A) rs2,
    (forall x, rs1 !! x = rs2 !! x) ->
    forall rl, rs1##rl = rs2##rl.
Proof. induction rl; crush. Qed.

Lemma sem_update_Op :
  forall A ge sp st f st' r l o0 o m rs v,
  @sem A ge sp st f st' ->
  Op.eval_operation ge sp o0 rs ## l m = Some v ->
  match_states st' (mk_instr_state rs m) ->
  exists tst,
  sem ge sp st (update f (RBop o o0 l r)) tst /\ match_states (mk_instr_state (Regmap.set r v rs) m) tst.
Proof.
  intros. inv H1. simplify.
  destruct st.
  econstructor. simplify.
  { constructor.
    { constructor. intros. destruct (Pos.eq_dec x r); subst.
      { pose proof (H5 r). rewrite map2. pose proof H. inv H. econstructor; eauto.
        { inv H9. eapply gen_list_base; eauto. }
        { instantiate (1 := (Regmap.set r v rs0)). rewrite Regmap.gss. erewrite regmap_list_equiv; eauto. } }
      { rewrite Regmap.gso by auto. rewrite genmap1; crush. inv H. inv H7; eauto. } }
    { inv H. rewrite genmap1; crush. eauto. } }
  { constructor; eauto. intros.
    destruct (Pos.eq_dec r x);
    subst; [repeat rewrite Regmap.gss | repeat rewrite Regmap.gso]; auto. }
Qed.

Lemma sem_update_load :
  forall A ge sp st f st' r o m a l m0 rs v a0,
  @sem A ge sp st f st' ->
  Op.eval_addressing ge sp a rs ## l = Some a0 ->
  Mem.loadv m m0 a0 = Some v ->
  match_states st' (mk_instr_state rs m0) ->
  exists tst : instr_state,
    sem ge sp st (update f (RBload o m a l r)) tst
    /\ match_states (mk_instr_state (Regmap.set r v rs) m0) tst.
Proof.
  intros. inv H2. pose proof H. inv H. inv H9.
  destruct st.
  econstructor; simplify.
  { constructor.
    { constructor. intros.
      destruct (Pos.eq_dec x r); subst.
      { rewrite map2. econstructor; eauto. eapply gen_list_base. intros.
        rewrite <- H6. eauto.
        instantiate (1 := (Regmap.set r v rs0)). rewrite Regmap.gss. auto. }
      { rewrite Regmap.gso by auto. rewrite genmap1; crush. } }
    { rewrite genmap1; crush. eauto. } }
  { constructor; auto; intros. destruct (Pos.eq_dec r x);
    subst; [repeat rewrite Regmap.gss | repeat rewrite Regmap.gso]; auto. }
Qed.

Lemma sem_update_store :
  forall A ge sp a0 m a l r o f st m' rs m0 st',
  @sem A ge sp st f st' ->
  Op.eval_addressing ge sp a rs ## l = Some a0 ->
  Mem.storev m m0 a0 rs !! r = Some m' ->
  match_states st' (mk_instr_state rs m0) ->
  exists tst, sem ge sp st (update f (RBstore o m a l r)) tst
              /\ match_states (mk_instr_state rs m') tst.
Proof.
  intros. inv H2. pose proof H. inv H. inv H9.
  destruct st.
  econstructor; simplify.
  { econstructor.
    { econstructor; intros. rewrite genmap1; crush. }
    { rewrite map2. econstructor; eauto. eapply gen_list_base. intros. rewrite <- H6.
      eauto. specialize (H6 r). rewrite H6. eauto. } }
  { econstructor; eauto. }
Qed.

Lemma sem_update :
  forall A ge sp st x st' st'' st''' f,
  sem ge sp st f st' ->
  match_states st' st''' ->
  @step_instr A ge sp st''' x st'' ->
  exists tst, sem ge sp st (update f x) tst /\ match_states st'' tst.
Proof.
  intros. destruct x; inv H1.
  { econstructor. split.
    apply sem_update_RBnop. eassumption.
    apply match_states_commut. auto. }
  { eapply sem_update_Op; eauto. }
  { eapply sem_update_load; eauto. }
  { eapply sem_update_store; eauto. }
Qed.

Lemma sem_update2_Op :
  forall A ge sp st f r l o0 o m rs v,
  @sem A ge sp st f (mk_instr_state rs m) ->
  Op.eval_operation ge sp o0 rs ## l m = Some v ->
  sem ge sp st (update f (RBop o o0 l r)) (mk_instr_state (Regmap.set r v rs) m).
Proof.
  intros. destruct st. constructor.
  inv H. inv H6.
  { constructor; intros. simplify.
    destruct (Pos.eq_dec r x); subst.
    { rewrite map2. econstructor. eauto.
      apply gen_list_base. eauto.
      rewrite Regmap.gss. auto. }
    { rewrite genmap1; crush. rewrite Regmap.gso; auto.  } }
  { simplify. rewrite genmap1; crush. inv H. eauto. }
Qed.

Lemma sem_update2_load :
  forall A ge sp st f r o m a l m0 rs v a0,
    @sem A ge sp st f (mk_instr_state rs m0) ->
    Op.eval_addressing ge sp a rs ## l = Some a0 ->
    Mem.loadv m m0 a0 = Some v ->
    sem ge sp st (update f (RBload o m a l r)) (mk_instr_state (Regmap.set r v rs) m0).
Proof.
  intros. simplify. inv H. inv H7. constructor.
  { constructor; intros. destruct (Pos.eq_dec r x); subst.
    { rewrite map2. rewrite Regmap.gss. econstructor; eauto.
      apply gen_list_base; eauto. }
    { rewrite genmap1; crush. rewrite Regmap.gso; eauto. }
  }
  { simplify. rewrite genmap1; crush. }
Qed.

Lemma sem_update2_store :
  forall A ge sp a0 m a l r o f st m' rs m0,
    @sem A ge sp st f (mk_instr_state rs m0) ->
    Op.eval_addressing ge sp a rs ## l = Some a0 ->
    Mem.storev m m0 a0 rs !! r = Some m' ->
    sem ge sp st (update f (RBstore o m a l r)) (mk_instr_state rs m').
Proof.
  intros. simplify. inv H. inv H7. constructor; simplify.
  { econstructor; intros. rewrite genmap1; crush. }
  { rewrite map2. econstructor; eauto. apply gen_list_base; eauto. }
Qed.

Lemma sem_update2 :
  forall A ge sp st x st' st'' f,
  sem ge sp st f st' ->
  @step_instr A ge sp st' x st'' ->
  sem ge sp st (update f x) st''.
Proof.
  intros.
  destruct x; inv H0;
  eauto using sem_update_RBnop, sem_update2_Op, sem_update2_load, sem_update2_store.
Qed.

Lemma abstr_sem_val_mem :
  forall A B ge tge st tst sp a,
    ge_preserved ge tge ->
    forall v m,
    (@sem_mem A ge sp st a m /\ match_states st tst -> @sem_mem B tge sp tst a m) /\
    (@sem_value A ge sp st a v /\ match_states st tst -> @sem_value B tge sp tst a v).
Proof.
  intros * H.
  apply expression_ind2 with

    (P := fun (e1: expression) =>
    forall v m,
    (@sem_mem A ge sp st e1 m /\ match_states st tst -> @sem_mem B tge sp tst e1 m) /\
    (@sem_value A ge sp st e1 v /\ match_states st tst -> @sem_value B tge sp tst e1 v))

    (P0 := fun (e1: expression_list) =>
    forall lv, @sem_val_list A ge sp st e1 lv /\ match_states st tst -> @sem_val_list B tge sp tst e1 lv);
  simplify; intros; simplify.
  { inv H1. inv H2. constructor. }
  { inv H2. inv H1. rewrite H0. constructor. }
  { inv H3. }
  { inv H3. inv H4. econstructor. apply H1; auto. simplify. eauto. constructor. auto. auto.
    apply H0; simplify; eauto. constructor; eauto.
    unfold ge_preserved in *. simplify. rewrite <- H2. auto.
  }
  { inv H3. }
  { inv H3. inv H4. econstructor. apply H1; eauto; simplify; eauto. constructor; eauto.
    apply H0; simplify; eauto. constructor; eauto.
    inv H. rewrite <- H4. eauto.
    auto.
  }
  { inv H4. inv H5. econstructor. apply H0; eauto. simplify; eauto. constructor; eauto.
    apply H2; eauto. simplify; eauto. constructor; eauto.
    apply H1; eauto. simplify; eauto. constructor; eauto.
    inv H. rewrite <- H5. eauto. auto.
  }
  { inv H4. }
  { inv H1. constructor. }
  { inv H3. constructor; auto. apply H0; eauto. apply Mem.empty. }
Qed.

Lemma abstr_sem_value :
  forall a A B ge tge sp st tst v,
    @sem_value A ge sp st a v ->
    ge_preserved ge tge ->
    match_states st tst ->
    @sem_value B tge sp tst a v.
Proof. intros; eapply abstr_sem_val_mem; eauto; apply Mem.empty. Qed.

Lemma abstr_sem_mem :
  forall a A B ge tge sp st tst v,
    @sem_mem A ge sp st a v ->
    ge_preserved ge tge ->
    match_states st tst ->
    @sem_mem B tge sp tst a v.
Proof. intros; eapply abstr_sem_val_mem; eauto. Qed.

Lemma abstr_sem_regset :
  forall a a' A B ge tge sp st tst rs,
    @sem_regset A ge sp st a rs ->
    ge_preserved ge tge ->
    (forall x, a # x = a' # x) ->
    match_states st tst ->
    exists rs', @sem_regset B tge sp tst a' rs' /\ (forall x, rs !! x = rs' !! x).
Proof.
  inversion 1; intros.
  inv H7.
  econstructor. simplify. econstructor. intros.
  eapply abstr_sem_value; eauto. rewrite <- H6.
  eapply H0. constructor; eauto.
  auto.
Qed.

Lemma abstr_sem :
  forall a a' A B ge tge sp st tst st',
    @sem A ge sp st a st' ->
    ge_preserved ge tge ->
    (forall x, a # x = a' # x) ->
    match_states st tst ->
    exists tst', @sem B tge sp tst a' tst' /\ match_states st' tst'.
Proof.
  inversion 1; subst; intros.
  inversion H4; subst.
  exploit abstr_sem_regset; eauto; inv_simp.
  do 3 econstructor; eauto.
  rewrite <- H3.
  eapply abstr_sem_mem; eauto.
Qed.

Lemma abstract_execution_correct':
  forall A B ge tge sp st' a a' st tst,
  @sem A ge sp st a st' ->
  ge_preserved ge tge ->
  check a a' = true ->
  match_states st tst ->
  exists tst', @sem B tge sp tst a' tst' /\ match_states st' tst'.
Proof.
  intros;
  pose proof (check_correct a a' H1);
  eapply abstr_sem; eauto.
Qed.

Lemma states_match :
  forall st1 st2 st3 st4,
  match_states st1 st2 ->
  match_states st2 st3 ->
  match_states st3 st4 ->
  match_states st1 st4.
Proof.
  intros * H1 H2 H3; destruct st1; destruct st2; destruct st3; destruct st4.
  inv H1. inv H2. inv H3; constructor.
  unfold regs_lessdef in *. intros.
  repeat match goal with
         | H: forall _, _, r : positive |- _ => specialize (H r)
         end.
  congruence.
  auto.
Qed.

Lemma step_instr_block_same :
  forall ge sp st st',
  step_instr_block ge sp st nil st' ->
  st = st'.
Proof. inversion 1; auto. Qed.

Lemma step_instr_seq_same :
  forall ge sp st st',
  step_instr_seq ge sp st nil st' ->
  st = st'.
Proof. inversion 1; auto. Qed.

Lemma sem_update' :
  forall A ge sp st a x st',
  sem ge sp st (update (abstract_sequence empty a) x) st' ->
  exists st'',
  @step_instr A ge sp st'' x st' /\
  sem ge sp st (abstract_sequence empty a) st''.
Proof.
  Admitted.

Lemma sem_separate :
  forall A (ge: @RTLBlockInstr.genv A) b a sp st st',
    sem ge sp st (abstract_sequence empty (a ++ b)) st' ->
    exists st'',
         sem ge sp st (abstract_sequence empty a) st''
      /\ sem ge sp st'' (abstract_sequence empty b) st'.
Proof.
  induction b using rev_ind; simplify.
  { econstructor. simplify. rewrite app_nil_r in H. eauto. apply abstract_interp_empty. }
  { simplify. rewrite app_assoc in H. rewrite abstract_seq in H.
    exploit sem_update'; eauto; inv_simp.
    exploit IHb; eauto; inv_simp.
    econstructor; split; eauto.
    rewrite abstract_seq.
    eapply sem_update2; eauto.
  }
Qed.

Lemma rtlpar_trans_correct :
  forall bb ge sp sem_st' sem_st st,
  sem ge sp sem_st (abstract_sequence empty (concat (concat bb))) sem_st' ->
  match_states sem_st st ->
  exists st', RTLPar.step_instr_block ge sp st bb st'
              /\ match_states sem_st' st'.
Proof.
  induction bb using rev_ind.
  { repeat econstructor. eapply abstract_interp_empty3 in H.
    inv H. inv H0. constructor; congruence. }
  { simplify. inv H0. repeat rewrite concat_app in H. simplify.
    rewrite app_nil_r in H.
    exploit sem_separate; eauto; inv_simp.
    repeat econstructor. admit. admit.
  }
Admitted.

(*Lemma abstract_execution_correct_ld:
  forall bb bb' cfi ge tge sp st st' tst,
    RTLBlock.step_instr_list ge sp st bb st' ->
    ge_preserved ge tge ->
    schedule_oracle (mk_bblock bb cfi) (mk_bblock bb' cfi) = true ->
    match_states_ld st tst ->
    exists tst', RTLPar.step_instr_block tge sp tst bb' tst'
                 /\ match_states st' tst'.
Proof.
  intros.*)
*)

Lemma match_states_list :
  forall A (rs: Regmap.t A) rs',
  (forall r, rs !! r = rs' !! r) ->
  forall l, rs ## l = rs' ## l.
Proof. induction l; crush. Qed.

Lemma PTree_matches :
  forall A (v: A) res rs rs',
  (forall r, rs !! r = rs' !! r) ->
  forall x, (Regmap.set res v rs) !! x = (Regmap.set res v rs') !! x.
Proof.
  intros; destruct (Pos.eq_dec x res); subst;
  [ repeat rewrite Regmap.gss by auto
  | repeat rewrite Regmap.gso by auto ]; auto.
Qed.

Lemma step_instr_matches :
  forall A a ge sp st st',
    @step_instr A ge sp st a st' ->
    forall tst,
      match_states st tst ->
      exists tst', step_instr ge sp tst a tst'
                   /\ match_states st' tst'.
Proof.
  induction 1; simplify;
  match goal with H: match_states _ _ |- _ => inv H end;
  try solve [repeat econstructor; try erewrite match_states_list;
  try apply PTree_matches; eauto;
  match goal with
    H: forall _, _ |- context[Mem.storev] => erewrite <- H; eauto
  end].
  - destruct p. match goal with H: eval_pred _ _ _ _ |- _ => inv H end.
    repeat econstructor; try erewrite match_states_list; eauto.
    erewrite <- eval_predf_pr_equiv; eassumption.
    apply PTree_matches; assumption.
    repeat (econstructor; try apply eval_pred_false); eauto. try erewrite match_states_list; eauto.
    erewrite <- eval_predf_pr_equiv; eassumption.
    econstructor; auto.
    match goal with H: eval_pred _ _ _ _ |- _ => inv H end.
    repeat econstructor; try erewrite match_states_list; eauto.
  - destruct p. match goal with H: eval_pred _ _ _ _ |- _ => inv H end.
    repeat econstructor; try erewrite match_states_list; eauto.
    erewrite <- eval_predf_pr_equiv; eassumption.
    apply PTree_matches; assumption.
    repeat (econstructor; try apply eval_pred_false); eauto. try erewrite match_states_list; eauto.
    erewrite <- eval_predf_pr_equiv; eassumption.
    econstructor; auto.
    match goal with H: eval_pred _ _ _ _ |- _ => inv H end.
    repeat econstructor; try erewrite match_states_list; eauto.
  - destruct p. match goal with H: eval_pred _ _ _ _ |- _ => inv H end.
    repeat econstructor; try erewrite match_states_list; eauto.
    match goal with
    H: forall _, _ |- context[Mem.storev] => erewrite <- H; eauto
    end.
    erewrite <- eval_predf_pr_equiv; eassumption.
    repeat (econstructor; try apply eval_pred_false); eauto. try erewrite match_states_list; eauto.
    match goal with
    H: forall _, _ |- context[Mem.storev] => erewrite <- H; eauto
    end.
    erewrite <- eval_predf_pr_equiv; eassumption.
    match goal with H: eval_pred _ _ _ _ |- _ => inv H end.
    repeat econstructor; try erewrite match_states_list; eauto.
    match goal with
    H: forall _, _ |- context[Mem.storev] => erewrite <- H; eauto
    end.
Qed.

Lemma step_instr_list_matches :
  forall a ge sp st st',
  step_instr_list ge sp st a st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr_list ge sp tst a tst'
                           /\ match_states st' tst'.
Proof.
  induction a; intros; inv H;
  try (exploit step_instr_matches; eauto; []; simplify;
       exploit IHa; eauto; []; simplify); repeat econstructor; eauto.
Qed.

Lemma step_instr_seq_matches :
  forall a ge sp st st',
  step_instr_seq ge sp st a st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr_seq ge sp tst a tst'
                           /\ match_states st' tst'.
Proof.
  induction a; intros; inv H;
  try (exploit step_instr_list_matches; eauto; []; simplify;
       exploit IHa; eauto; []; simplify); repeat econstructor; eauto.
Qed.

Lemma step_instr_block_matches :
  forall bb ge sp st st',
  step_instr_block ge sp st bb st' ->
  forall tst, match_states st tst ->
              exists tst', step_instr_block ge sp tst bb tst'
                           /\ match_states st' tst'.
Proof.
  induction bb; intros; inv H;
  try (exploit step_instr_seq_matches; eauto; []; simplify;
       exploit IHbb; eauto; []; simplify); repeat econstructor; eauto.
Qed.

Lemma rtlblock_trans_correct' :
  forall bb ge sp st x st'',
  RTLBlock.step_instr_list ge sp st (bb ++ x :: nil) st'' ->
  exists st', RTLBlock.step_instr_list ge sp st bb st'
              /\ step_instr ge sp st' x st''.
Proof.
  induction bb.
  crush. exists st.
  split. constructor. inv H. inv H6. auto.
  crush. inv H. exploit IHbb. eassumption. simplify.
  econstructor. split.
  econstructor; eauto. eauto.
Qed.

Lemma abstract_interp_empty A st : @sem A st empty (ctx_is st).
Proof. destruct st, ctx_is. simpl. repeat econstructor. Qed.

Lemma abstract_seq :
  forall l f i,
    abstract_sequence f (l ++ i :: nil) = update (abstract_sequence f l) i.
Proof. induction l; crush. Qed.

Lemma sem_update :
  forall A ge sp st x st' st'' st''' f,
  sem (mk_ctx st sp ge) f st' ->
  match_states st' st''' ->
  @step_instr A ge sp st''' x st'' ->
  exists tst, sem (mk_ctx st sp ge) (update f x) tst /\ match_states st'' tst.
Proof. Admitted.

Lemma rtlblock_trans_correct :
  forall bb ge sp st st',
    RTLBlock.step_instr_list ge sp st bb st' ->
    forall tst,
      match_states st tst ->
      exists tst', sem (mk_ctx tst sp ge) (abstract_sequence empty bb) tst'
                   /\ match_states st' tst'.
Proof.
  induction bb using rev_ind; simplify.
  { econstructor. simplify. apply abstract_interp_empty.
    inv H. auto. }
  { apply rtlblock_trans_correct' in H. simplify.
    rewrite abstract_seq.
    exploit IHbb; try eassumption; []; simplify.
    exploit sem_update. apply H1. symmetry; eassumption.
    eauto. simplify. econstructor. split. apply H3.
    auto. }
Qed.

Lemma abstract_execution_correct:
  forall bb bb' cfi cfi' ge tge sp st st' tst,
    RTLBlock.step_instr_list ge sp st bb st' ->
    ge_preserved ge tge ->
    schedule_oracle (mk_bblock bb cfi) (mk_bblock bb' cfi') = true ->
    match_states st tst ->
    exists tst', RTLPar.step_instr_block tge sp tst bb' tst'
                 /\ match_states st' tst'.
Proof.
  intros.
  unfold schedule_oracle in *. simplify. unfold empty_trees in H4.
  exploit rtlblock_trans_correct; try eassumption; []; simplify.
(*)  exploit abstract_execution_correct';
  try solve [eassumption | apply state_lessdef_match_sem; eassumption].
  apply match_states_commut. eauto. inv_simp.
  exploit rtlpar_trans_correct; try eassumption; []; inv_simp.
  exploit step_instr_block_matches; eauto. apply match_states_commut; eauto. inv_simp.
  repeat match goal with | H: match_states _ _ |- _ => inv H end.
  do 2 econstructor; eauto.
  econstructor; congruence.
Qed.*)Admitted.

(*|
Top-level functions
===================
|*)

Parameter schedule : RTLBlock.function -> RTLPar.function.

Definition transl_function (f: RTLBlock.function) : Errors.res RTLPar.function :=
  let tfcode := fn_code (schedule f) in
  if check_scheduled_trees f.(fn_code) tfcode then
    Errors.OK (mkfunction f.(fn_sig)
                          f.(fn_params)
                          f.(fn_stacksize)
                          tfcode
                          f.(fn_entrypoint))
  else
    Errors.Error (Errors.msg "RTLPargen: Could not prove the blocks equivalent.").

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : RTLBlock.program) : Errors.res RTLPar.program :=
  transform_partial_program transl_fundef p.
