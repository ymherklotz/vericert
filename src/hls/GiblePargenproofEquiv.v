(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <git@yannherklotz.com>
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

Require Import Coq.Logic.Decidable.
Require Import Coq.Structures.Equalities.

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
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Gible.
Require Import vericert.hls.HashTree.
Require Import vericert.hls.Predicate.
Require Import vericert.common.DecEq.
Require Import vericert.hls.Abstr.
Require vericert.common.NonEmpty.
Module NE := NonEmpty.
Import NE.NonEmptyNotation.

Module OE := MonadExtra(Option).
Import OE.MonadNotation.

#[local] Open Scope non_empty_scope.
#[local] Open Scope positive.
#[local] Open Scope pred_op.
#[local] Open Scope forest.

Fixpoint beq_expression (e1 e2: expression) {struct e1}: bool :=
  match e1, e2 with
  | Ebase r1, Ebase r2 => if resource_eq r1 r2 then true else false
  | Eop op1 el1, Eop op2 el2 =>
    if operation_eq op1 op2 then
    beq_expression_list el1 el2 else false
  | Eload chk1 addr1 el1 e1, Eload chk2 addr2 el2 e2 =>
    if memory_chunk_eq chk1 chk2
    then if addressing_eq addr1 addr2
         then if beq_expression_list el1 el2
              then beq_expression e1 e2 else false else false else false
  | Estore e1 chk1 addr1 el1 m1, Estore e2 chk2 addr2 el2 m2 =>
    if memory_chunk_eq chk1 chk2
    then if addressing_eq addr1 addr2
         then if beq_expression_list el1 el2
              then if beq_expression m1 m2
                   then beq_expression e1 e2 else false else false else false else false
  | _, _ => false
  end
with beq_expression_list (el1 el2: expression_list) {struct el1} : bool :=
  match el1, el2 with
  | Enil, Enil => true
  | Econs e1 t1, Econs e2 t2 => beq_expression e1 e2 && beq_expression_list t1 t2
  | _, _ => false
  end
.

Scheme expression_ind2 := Induction for expression Sort Prop
  with expression_list_ind2 := Induction for expression_list Sort Prop.
Definition beq_pred_expression (e1 e2: pred_expression) : bool :=
  match e1, e2 with
  | PEbase p1, PEbase p2 => if peq p1 p2 then true else false
  | PEsetpred c1 el1, PEsetpred c2 el2 =>
    if condition_eq c1 c2
    then beq_expression_list el1 el2 else false
  | _, _ => false
  end.

Definition beq_exit_expression (e1 e2: exit_expression) : bool :=
  match e1, e2 with
  | EEbase, EEbase => true
  | EEexit cf1, EEexit cf2 => if cf_instr_eq cf1 cf2 then true else false
  | _, _ => false
  end.

Lemma beq_expression_correct:
  forall e1 e2, beq_expression e1 e2 = true -> e1 = e2.
Proof.
  intro e1;
  apply expression_ind2 with
      (P := fun (e1 : expression) =>
            forall e2, beq_expression e1 e2 = true -> e1 = e2)
      (P0 := fun (e1 : expression_list) =>
             forall e2, beq_expression_list e1 e2 = true -> e1 = e2); simplify;
  try solve [repeat match goal with
                    | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
                    | [ H : context[if ?x then _ else _] |- _ ] => destruct x eqn:?
                    end; subst; f_equal; crush; eauto using Peqb_true_eq].
Qed.

Lemma beq_expression_refl: forall e, beq_expression e e = true.
Proof.
  intros.
  induction e using expression_ind2 with (P0 := fun el => beq_expression_list el el = true);
  crush; repeat (destruct_match; crush); [].
  crush. rewrite IHe. rewrite IHe0. auto.
Qed.

Lemma beq_expression_list_refl: forall e, beq_expression_list e e = true.
Proof. induction e; auto. simplify. rewrite beq_expression_refl. auto. Qed.

Lemma beq_expression_correct2:
  forall e1 e2, beq_expression e1 e2 = false -> e1 <> e2.
Proof.
  induction e1 using expression_ind2
    with (P0 := fun el1 => forall el2, beq_expression_list el1 el2 = false -> el1 <> el2).
  - intros. simplify. repeat (destruct_match; crush).
  - intros. simplify. repeat (destruct_match; crush). subst. apply IHe1 in H.
    unfold not in *. intros. apply H. inv H0. auto.
  - intros. simplify. repeat (destruct_match; crush); subst.
    unfold not in *; intros. inv H0. rewrite beq_expression_refl in H. discriminate.
    unfold not in *; intros. inv H. rewrite beq_expression_list_refl in Heqb. discriminate.
  - simplify. repeat (destruct_match; crush); subst;
    unfold not in *; intros.
    inv H0. rewrite beq_expression_refl in H; crush.
    inv H. rewrite beq_expression_refl in Heqb0; crush.
    inv H. rewrite beq_expression_list_refl in Heqb; crush.
  (* - simplify. repeat (destruct_match; crush); subst. *)
  (*   unfold not in *; intros. inv H0. rewrite beq_expression_list_refl in H; crush. *)
  - simplify. repeat (destruct_match; crush); subst.
  - simplify. repeat (destruct_match; crush); subst.
    apply andb_false_iff in H. inv H. unfold not in *; intros.
    inv H. rewrite beq_expression_refl in H0; discriminate.
    unfold not in *; intros. inv H. rewrite beq_expression_list_refl in H0; discriminate.
Qed.

Definition expression_dec: forall e1 e2: expression, {e1 = e2} + {e1 <> e2}.
Proof.
  intros.
  destruct (beq_expression e1 e2) eqn:?. apply beq_expression_correct in Heqb. auto.
  apply beq_expression_correct2 in Heqb. auto.
Defined.

Lemma beq_expression_list_correct:
  forall e1 e2, beq_expression_list e1 e2 = true -> e1 = e2.
Proof.
  induction e1; crush.
  - destruct_match; crush.
  - destruct_match; crush.
    apply IHe1 in H1; subst.
    apply beq_expression_correct in H0; subst.
    trivial.
Qed.

Lemma beq_expression_list_correct2:
  forall e1 e2, beq_expression_list e1 e2 = false -> e1 <> e2.
Proof.
  induction e1; crush.
  - destruct_match; crush.
  - destruct_match; crush.
    apply andb_false_iff in H. inv H. apply beq_expression_correct2 in H0.
    unfold not in *; intros. apply H0. inv H. auto.
    apply IHe1 in H0. unfold not in *; intros. apply H0. inv H.
    auto.
Qed.

Lemma beq_pred_expression_correct:
  forall e1 e2, beq_pred_expression e1 e2 = true -> e1 = e2.
Proof.
  destruct e1, e2; crush.
  - destruct_match; crush.
  - destruct_match; subst; crush.
    apply beq_expression_list_correct in H; subst.
    trivial.
Qed.

Lemma beq_pred_expression_refl:
  forall e, beq_pred_expression e e = true.
Proof.
  destruct e; crush; destruct_match; crush.
  apply beq_expression_list_refl.
Qed.

Lemma beq_pred_expression_correct2:
  forall e1 e2, beq_pred_expression e1 e2 = false -> e1 <> e2.
Proof.
  destruct e1, e2; unfold not; crush.
  + destruct_match; crush.
  + destruct_match; crush. inv H0.
    now rewrite beq_expression_list_refl in H.
Qed.

Lemma beq_exit_expression_correct:
  forall e1 e2, beq_exit_expression e1 e2 = true <-> e1 = e2.
Proof.
  destruct e1, e2; split; crush;
  destruct_match; subst; crush.
Qed.

Definition pred_expr_item_eq (pe1 pe2: pred_op * expression) : bool :=
  @equiv_dec _ SATSetoid _ (fst pe1) (fst pe2) && beq_expression (snd pe1) (snd pe2).

Definition pred_eexpr_item_eq (pe1 pe2: pred_op * exit_expression) : bool :=
  @equiv_dec _ SATSetoid _ (fst pe1) (fst pe2) && beq_exit_expression (snd pe1) (snd pe2).

Definition pred_expr_dec: forall (pe1 pe2: pred_op * expression),
    {pred_expr_item_eq pe1 pe2 = true} + {pred_expr_item_eq pe1 pe2 = false}.
Proof.
  intros; destruct (pred_expr_item_eq pe1 pe2) eqn:?; unfold not; [tauto | now right].
Defined.

Definition pred_expr_dec2: forall (pe1 pe2: pred_op * expression),
    {pred_expr_item_eq pe1 pe2 = true} + {~ pred_expr_item_eq pe1 pe2 = true}.
Proof.
  intros; destruct (pred_expr_item_eq pe1 pe2) eqn:?; unfold not; [tauto | now right].
Defined.

Definition pred_expression_dec:
  forall e1 e2: pred_expression, {e1 = e2} + {e1 <> e2}.
Proof.
  intros. destruct (beq_pred_expression e1 e2) eqn:?.
  eauto using beq_pred_expression_correct.
  eauto using beq_pred_expression_correct2.
Defined.

Lemma exit_expression_refl:
  forall e, beq_exit_expression e e = true.
Proof. destruct e; crush; destruct_match; crush. Qed.

Definition exit_expression_dec:
  forall e1 e2: exit_expression, {e1 = e2} + {e1 <> e2}.
Proof.
  intros. destruct (beq_exit_expression e1 e2) eqn:?.
  - left. eapply beq_exit_expression_correct; eauto.
  - right. unfold not; intros.
    assert (X: ~ (beq_exit_expression e1 e2 = true))
      by eauto with bool.
    subst. apply X. apply exit_expression_refl.
Defined.

Lemma pred_eexpression_dec:
  forall (e1 e2: exit_expression) (p1 p2: pred_op),
    {(p1, e1) = (p2, e2)} + {(p1, e1) <> (p2, e2)}.
Proof.
  pose proof (Predicate.eq_dec peq).
  pose proof (exit_expression_dec).
  decide equality.
Defined.

(*Fixpoint encode_expression_ne (max: predicate) (pe: pred_expr_ne) (h: hash_tree)
  : (PTree.t pred_op) * hash_tree :=
  match pe with
  | NE.singleton (p, e) =>
    let (p', h') := hash_value max e h in
    (Por (Pnot p) (Pvar p'), h')
  | (p, e) ::| pr =>
    let (p', h') := hash_value max e h in
    let (p'', h'') := encode_expression_ne max pr h' in
    (Pand (Por (Pnot p) (Pvar p')) p'', h'')
  end.*)

Fixpoint max_pred_expr (pe: pred_expr) : positive :=
  match pe with
  | NE.singleton (p, e) => max_predicate p
  | (p, e) ::| pe' => Pos.max (max_predicate p) (max_pred_expr pe')
  end.

Definition ge_preserved {A B C D: Type} (ge: Genv.t A B) (tge: Genv.t C D) : Prop :=
  (forall sp op vl m, Op.eval_operation ge sp op vl m =
                      Op.eval_operation tge sp op vl m)
  /\ (forall sp addr vl, Op.eval_addressing ge sp addr vl =
                         Op.eval_addressing tge sp addr vl).

Lemma ge_preserved_same:
  forall A B ge, @ge_preserved A B A B ge ge.
Proof. unfold ge_preserved; auto. Qed.
#[local] Hint Resolve ge_preserved_same : core.

Inductive match_states : instr_state -> instr_state -> Prop :=
| match_states_intro:
  forall ps ps' rs rs' m m',
    (forall x, rs !! x = rs' !! x) ->
    (forall x, ps !! x = ps' !! x) ->
    m = m' ->
    match_states (mk_instr_state rs ps  m) (mk_instr_state rs' ps' m').

Lemma match_states_refl x : match_states x x.
Proof. destruct x; constructor; crush. Qed.

Lemma match_states_commut x y : match_states x y -> match_states y x.
Proof. inversion 1; constructor; crush. Qed.

Lemma match_states_trans x y z :
  match_states x y -> match_states y z -> match_states x z.
Proof. repeat inversion 1; constructor; crush. Qed.

#[global] Instance match_states_Equivalence : Equivalence match_states :=
  { Equivalence_Reflexive := match_states_refl ;
    Equivalence_Symmetric := match_states_commut ;
    Equivalence_Transitive := match_states_trans ; }.

Inductive similar {A B} : @ctx A -> @ctx B -> Prop :=
| similar_intro :
    forall ist ist' sp ge tge,
    ge_preserved ge tge ->
    match_states ist ist' ->
    similar (mk_ctx ist sp ge) (mk_ctx ist' sp tge).

Lemma ge_preserved_refl:
  forall A B (a: Genv.t A B), ge_preserved a a.
Proof. auto. Qed.

Lemma similar_refl:
  forall A (a: @Abstr.ctx A), similar a a.
Proof. intros; destruct a; constructor; auto. reflexivity. Qed.

Lemma similar_commut:
  forall A B (a: @Abstr.ctx A) (b: @Abstr.ctx B), similar a b -> similar b a.
Proof.
  inversion 1; constructor; auto.
  - unfold ge_preserved in *; inv H0; split; intros.
    rewrite H4; auto. rewrite H5; auto.
  - symmetry; auto.
Qed.

Lemma similar_trans:
  forall A B C (a: @Abstr.ctx A) (b: @Abstr.ctx B) (c: @Abstr.ctx C),
    similar a b -> similar b c -> similar a c.
Proof.
  repeat inversion 1; constructor.
  - unfold ge_preserved in *; inv H0; inv H9; split; intros.
    rewrite H11. rewrite H0; auto.
    rewrite H12. rewrite H2. auto.
  - transitivity ist'; auto.
Qed.

#[global] Instance similar_Equivalence {A} : Equivalence (@similar A A) :=
  { Equivalence_Reflexive := similar_refl A ;
    Equivalence_Symmetric := similar_commut A A ;
    Equivalence_Transitive := @similar_trans A A A ; }.

Module HashExpr' <: MiniDecidableType.
  Definition t := expression.
  Definition eq_dec := expression_dec.
End HashExpr'.

Module HashExpr := Make_UDT(HashExpr').
Module Import HT := HashTree(HashExpr).

Module PHashExpr' <: MiniDecidableType.
  Definition t := pred_expression.
  Definition eq_dec := pred_expression_dec.
End PHashExpr'.

Module PHashExpr := Make_UDT(PHashExpr').
Module PHT := HashTree(PHashExpr).

Module EHashExpr' <: MiniDecidableType.
  Definition t := exit_expression.
  Definition eq_dec := exit_expression_dec.
End EHashExpr'.

Module EHashExpr := Make_UDT(EHashExpr').
Module EHT := HashTree(EHashExpr).

Fixpoint hash_predicate (max: predicate) (ap: pred_pexpr) (h: PHT.hash_tree)
  : pred_op * PHT.hash_tree :=
  match ap with
  | Ptrue => (Ptrue, h)
  | Pfalse => (Pfalse, h)
  | Plit (b, ap') =>
      let (p', h') := PHT.hash_value max ap' h in
      (Plit (b, p'), h')
  | Pand p1 p2 =>
      let (p1', h') := hash_predicate max p1 h in
      let (p2', h'') := hash_predicate max p2 h' in
      (Pand p1' p2', h'')
  | Por p1 p2 =>
      let (p1', h') := hash_predicate max p1 h in
      let (p2', h'') := hash_predicate max p2 h' in
      (Por p1' p2', h'')
  end.

Definition predicated_mutexcl {A: Type} (pe: predicated A): Prop :=
  (forall x y, NE.In x pe -> NE.In y pe -> x <> y -> fst x ⇒ ¬ fst y)
  /\ NE.norepet pe.

Lemma predicated_cons :
  forall A (a: pred_op * A) x,
    predicated_mutexcl (a ::| x) ->
    predicated_mutexcl x.
Proof.
  unfold predicated_mutexcl; intros. inv H. inv H1. split; auto.
  intros. apply H0; auto; constructor; tauto.
Qed.

Lemma predicated_singleton :
  forall A (a: (pred_op * A)), predicated_mutexcl (NE.singleton a).
Proof.
  unfold predicated_mutexcl; intros; split; intros.
  { inv H. now inv H0. }
  constructor.
Qed.

(*

Lemma norm_expr_constant :
  forall x m h t h' e p,
    HN.norm_expression m x h = (t, h') ->
    h ! e = Some p ->
    h' ! e = Some p.
Proof. Abort.

Definition sat_aequiv ap1 ap2 :=
  exists h p1 p2,
    sat_equiv p1 p2
    /\ hash_predicate 1 ap1 h = (p1, h)
    /\ hash_predicate 1 ap2 h = (p2, h).

Lemma aequiv_symm : forall a b, sat_aequiv a b -> sat_aequiv b a.
Proof.
  unfold sat_aequiv; simplify; do 3 eexists; simplify; [symmetry | |]; eauto.
Qed.

Lemma existsh :
  forall ap1,
  exists h p1,
    hash_predicate 1 ap1 h = (p1, h).
Proof. Admitted.

Lemma aequiv_refl : forall a, sat_aequiv a a.
Proof.
  unfold sat_aequiv; intros.
  pose proof (existsh a); simplify.
  do 3 eexists; simplify; eauto. reflexivity.
Qed.

Lemma aequiv_trans :
  forall a b c,
    sat_aequiv a b ->
    sat_aequiv b c ->
    sat_aequiv a c.
Proof.
  unfold sat_aequiv; intros.
  simplify.
Abort.

Lemma norm_expr_mutexcl :
  forall m pe h t h' e e' p p',
    HN.norm_expression m pe h = (t, h') ->
    predicated_mutexcl pe ->
    t ! e = Some p ->
    t ! e' = Some p' ->
    e <> e' ->
    p ⇒ ¬ p'.
Proof. Abort.*)

Definition pred_expr_eqb: forall pe1 pe2: pred_expr,
  {pe1 = pe2} + {pe1 <> pe2}.
Proof.
  pose proof expression_dec.
  pose proof NE.eq_dec.
  pose proof (Predicate.eq_dec peq).
  assert (forall a b: pred_op * expression, {a = b} + {a <> b})
   by decide equality.
  decide equality.
Defined.

Definition pred_pexpr_eqb: forall pe1 pe2: pred_pexpr,
  {pe1 = pe2} + {pe1 <> pe2}.
Proof.
  pose proof pred_expression_dec.
  pose proof (Predicate.eq_dec pred_expression_dec).
  apply X.
Defined.

Require cohpred_theory.Predicate.
Require cohpred_theory.Smtpredicate.
Module TV := cohpred_theory.Predicate.
Module STV := cohpred_theory.Smtpredicate.

Module TVL := TV.ThreeValued(PHashExpr).

Fixpoint transf_pred_op {A} (p: @Predicate.pred_op A): @TV.pred A :=
  match p with
  | Ptrue => TV.Ptrue
  | Pfalse => TV.Pfalse
  | Plit (b, p) =>
    if b then TV.Pbase p else TV.Pnot (TV.Pbase p)
  | Pand p1 p2 =>
    TV.Pand (transf_pred_op p1) (transf_pred_op p2)
  | Por p1 p2 =>
    TV.Por (transf_pred_op p1) (transf_pred_op p2)
  end.

(*|
This following equivalence checker takes two pred_pexpr, hashes them, and then
proves them equivalent.  However, it's not quite clear whether this actually
proves that, given that ``pe1`` results in a value, then ``pe2`` will also
result in a value.  The issue is that even though this proves that both hashed
predicates will result in the same value, how do we then show that the initial
predicates will also be correct and equivalent.
|*)

Definition beq_pred_pexpr' (pe1 pe2: pred_pexpr): bool :=
  if pred_pexpr_eqb pe1 pe2 then true else
  let (np1, h) := hash_predicate 1 pe1 (PTree.empty _) in
  let (np2, h') := hash_predicate 1 pe2 h in
  equiv_check np1 np2.

(*|
Given two predicated expressions, prove that they are equivalent.
|*)

Definition beq_pred_pexpr (pe1 pe2: pred_pexpr): bool :=
  if pred_pexpr_eqb pe1 pe2 then true else
  let (np1, h) := TVL.hash_predicate (transf_pred_op pe1) (Maps.PTree.empty _) in
  let (np2, h') := TVL.hash_predicate (transf_pred_op pe2) h in
  STV.check_smt_total (TV.equiv np1 np2).

Lemma inj_asgn_eg : forall a b, (a =? b)%positive = (a =? a)%positive -> a = b.
Proof.
  intros. destruct (peq a b); subst.
  auto. rewrite OrdersEx.Positive_as_OT.eqb_refl in H.
  now apply Peqb_true_eq.
Qed.

Lemma inj_asgn :
  forall a b, (forall (f: positive -> bool), f a = f b) -> a = b.
Proof. intros. apply inj_asgn_eg. eauto. Qed.

Lemma inj_asgn_false:
  forall n1 n2 , ~ (forall c: positive -> bool, c n1 = negb (c n2)).
Proof.
  unfold not; intros. specialize (H (fun x => true)).
  simplify. discriminate.
Qed.

Lemma negb_inj:
  forall a b,
    negb a = negb b -> a = b.
Proof. destruct a, b; crush. Qed.

Lemma sat_predicate_Plit_inj :
  forall p1 p2,
    Plit p1 == Plit p2 -> p1 = p2.
Proof.
  simplify. destruct p1, p2.
  destruct b, b0. f_equal. unfold sat_equiv in H. cbn in H. now apply inj_asgn.
  solve [exfalso; eapply inj_asgn_false; eauto].
  solve [exfalso; eapply inj_asgn_false; eauto].
  assert (p = p0). eapply inj_asgn. intros. specialize (H f).
  apply negb_inj in H. auto. rewrite H0; auto.
Qed.

Definition ind_preds t :=
  forall e1 e2 p1 p2 c,
    e1 <> e2 ->
    t ! e1 = Some p1 ->
    t ! e2 = Some p2 ->
    sat_predicate p1 c = true ->
    sat_predicate p2 c = false.

Definition ind_preds_l t :=
  forall (e1: predicate) e2 p1 p2 c,
    e1 <> e2 ->
    In (e1, p1) t ->
    In (e2, p2) t ->
    sat_predicate p1 c = true ->
    sat_predicate p2 c = false.

(*Lemma pred_equivalence_Some' :
  forall ta tb e pe pe',
    list_norepet (map fst ta) ->
    list_norepet (map fst tb) ->
    In (e, pe) ta ->
    In (e, pe') tb ->
    fold_right (fun p a => mk_pred_stmnt' (fst p) (snd p) ∧ a) T ta ==
    fold_right (fun p a => mk_pred_stmnt' (fst p) (snd p) ∧ a) T tb ->
    pe == pe'.
Proof.
  induction ta as [|hd tl Hta]; try solve [crush].
  - intros * NRP1 NRP2 IN1 IN2 FOLD. inv NRP1. inv IN1.
    simpl in FOLD.

Lemma pred_equivalence_Some :
  forall (ta tb: PTree.t pred_op) e pe pe',
    ta ! e = Some pe ->
    tb ! e = Some pe' ->
    mk_pred_stmnt ta == mk_pred_stmnt tb ->
    pe == pe'.
Proof.
  intros * SMEA SMEB EQ. unfold mk_pred_stmnt in *.
  repeat rewrite PTree.fold_spec in EQ.

Lemma pred_equivalence_None :
  forall (ta tb: PTree.t pred_op) e pe,
    (mk_pred_stmnt ta) == (mk_pred_stmnt tb) ->
    ta ! e = Some pe ->
    tb ! e = None ->
    equiv pe ⟂.
Abort.

Lemma pred_equivalence :
  forall (ta tb: PTree.t pred_op) e pe,
    equiv (mk_pred_stmnt ta) (mk_pred_stmnt tb) ->
    ta ! e = Some pe ->
    equiv pe ⟂ \/ (exists pe', tb ! e = Some pe' /\ equiv pe pe').
Proof.
  intros * EQ SME. destruct (tb ! e) eqn:HTB.
  { right. econstructor. split; eauto. eapply pred_equivalence_Some; eauto. }
  { left. eapply pred_equivalence_None; eauto. }
Qed.*)

Section CORRECT.

  Context {FUN TFUN: Type}.

  Context (ictx: @ctx FUN) (octx: @ctx TFUN) (HSIM: similar ictx octx).

  Lemma sem_value_mem_det:
    forall e v v' m m',
      (sem_value ictx e v -> sem_value octx e v' -> v = v')
      /\ (sem_mem ictx e m -> sem_mem octx e m' -> m = m').
  Proof using HSIM.
    induction e using expression_ind2
      with (P0 := fun p => forall v v',
                    sem_val_list ictx p v -> sem_val_list octx p v' -> v = v');
    inv HSIM; match goal with H: context [match_states] |- _ => inv H end; repeat progress simplify;
    try solve [match goal with
               | H: sem_value _ _ _, H2: sem_value _ _ _ |- _ => inv H; inv H2; auto
               | H: sem_mem _ _ _, H2: sem_mem _ _ _ |- _ => inv H; inv H2; auto
               | H: sem_val_list _ _ _, H2: sem_val_list _ _ _ |- _ => inv H; inv H2; auto
               end].
    - repeat match goal with
             | H: sem_value _ _ _ |- _ => inv H
             | H: sem_val_list {| ctx_ge := ge; |} ?e ?l1,
               H2: sem_val_list {| ctx_ge := tge |} ?e ?l2,
               IH: forall _ _, sem_val_list _ _ _ -> sem_val_list _ _ _ -> _ = _ |- _ =>
               assert (X: l1 = l2) by (apply IH; auto)
             | H: ge_preserved _ _ |- _ => inv H
             | |- context [ctx_rs] => unfold ctx_rs; cbn
             | H: context [ctx_mem] |- _ => unfold ctx_mem in H; cbn
             end; crush.
    - repeat match goal with H: sem_value _ _ _ |- _ => inv H end; simplify;
      assert (lv0 = lv) by (apply IHe; eauto); subst;
      match goal with H: ge_preserved _ _ |- _ => inv H end;
      match goal with H: context [Op.eval_addressing _ _ _ _ = Op.eval_addressing _ _ _ _] |- _
                      => rewrite H in * end;
      assert (a0 = a1) by crush;
      assert (m'2 = m'1) by (apply IHe0; eauto); crush.
    - inv H0; inv H3. simplify.
      assert (lv = lv0) by ( apply IHe2; eauto). subst.
      assert (a1 = a0). { inv H. rewrite H3 in *. crush. }
      assert (v0 = v1). { apply IHe1; auto. }
      assert (m'1 = m'2). { apply IHe3; auto. } crush.
    - inv H0. inv H3. f_equal. apply IHe; auto.
      apply IHe0; auto.
  Qed.

  Lemma sem_value_mem_corr:
    forall e v m,
      (sem_value ictx e v -> sem_value octx e v)
      /\ (sem_mem ictx e m -> sem_mem octx e m).
  Proof using HSIM.
    induction e using expression_ind2
      with (P0 := fun p => forall v,
                    sem_val_list ictx p v -> sem_val_list octx p v);
    inv HSIM; match goal with H: context [match_states] |- _ => inv H end; repeat progress simplify.
    - inv H0. unfold ctx_rs, ctx_ps, ctx_mem in *; cbn. rewrite H1. constructor.
    - inv H0. unfold ctx_rs, ctx_ps, ctx_mem in *; cbn. constructor.
    - inv H0. apply IHe in H6. econstructor; try eassumption.
      unfold ctx_rs, ctx_ps, ctx_mem in *; cbn in *. inv H. crush.
    - inv H0.
    - inv H0. eapply IHe in H10. eapply IHe0 in H8; auto.
      econstructor; try eassumption.
      unfold ctx_rs, ctx_ps, ctx_mem in *; cbn in *. inv H; crush.
    - inv H0.
    - inv H0.
    - inv H0. eapply IHe1 in H11; auto. eapply IHe2 in H12; auto. eapply IHe3 in H9; auto.
      econstructor; try eassumption.
      unfold ctx_rs, ctx_ps, ctx_mem in *; cbn in *. inv H; crush.
    - inv H0. econstructor.
    - inv H0. eapply IHe in H6; auto. eapply IHe0 in H8.
      econstructor; eassumption.
  Qed.

  Lemma sem_value_det:
    forall e v v', sem_value ictx e v -> sem_value octx e v' -> v = v'.
  Proof using HSIM.
    intros. eapply sem_value_mem_det; eauto; apply Mem.empty.
  Qed.

  Lemma sem_value_corr:
    forall e v, sem_value ictx e v -> sem_value octx e v.
  Proof using HSIM.
    intros. eapply sem_value_mem_corr; eauto; apply Mem.empty.
  Qed.

  Lemma sem_mem_det:
    forall e v v', sem_mem ictx e v -> sem_mem octx e v' -> v = v'.
  Proof using HSIM.
    intros. eapply sem_value_mem_det; eauto; apply (Vint (Int.repr 0%Z)).
  Qed.

  Lemma sem_mem_corr:
    forall e v, sem_mem ictx e v -> sem_mem octx e v.
  Proof using HSIM.
    intros. eapply sem_value_mem_corr; eauto; apply (Vint (Int.repr 0%Z)).
  Qed.

  Lemma sem_val_list_det:
    forall e l l', sem_val_list ictx e l -> sem_val_list octx e l' -> l = l'.
  Proof using HSIM.
    induction e; simplify.
    - inv H; inv H0; auto.
    - inv H; inv H0. f_equal. eapply sem_value_det; eauto; try apply Mem.empty.
      apply IHe; eauto.
  Qed.

  Lemma sem_val_list_corr:
    forall e l, sem_val_list ictx e l -> sem_val_list octx e l.
  Proof using HSIM.
    induction e; simplify.
    - inv H; constructor.
    - inv H. apply sem_value_corr in H3; auto; try apply Mem.empty;
      apply IHe in H5; constructor; assumption.
  Qed.

  Lemma sem_pred_det:
    forall e v v', sem_pred ictx e v -> sem_pred octx e v' -> v = v'.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_det; pose proof sem_val_list_det; inv HSIM;
      match goal with H: match_states _ _ |- _ => inv H end; simplify.
    inv H2; inv H5; auto. assert (lv = lv0) by (eapply H0; eauto). subst. unfold ctx_mem in *.
    crush.
  Qed.

  Lemma sem_pred_corr:
    forall e v, sem_pred ictx e v -> sem_pred octx e v.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_corr; pose proof sem_val_list_corr; inv HSIM;
      match goal with H: match_states _ _ |- _ => inv H end; simplify.
    inv H2; auto. apply H0 in H5. econstructor; eauto.
    unfold ctx_ps; cbn. rewrite H4. constructor.
  Qed.

  Lemma sem_exit_det:
    forall e v v', sem_exit ictx e v -> sem_exit octx e v' -> v = v'.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_det; pose proof sem_val_list_det; inv HSIM;
      match goal with H: match_states _ _ |- _ => inv H end; simplify.
    inv H2; inv H5; auto.
  Qed.

  Lemma sem_exit_corr:
    forall e v, sem_exit ictx e v -> sem_exit octx e v.
  Proof using HSIM.
    try solve [inversion 1]; pose proof sem_value_corr; pose proof sem_val_list_corr; inv HSIM;
      match goal with H: match_states _ _ |- _ => inv H end; simplify.
    inv H2; auto; constructor.
  Qed.

  Lemma sem_pexpr_det :
    forall p b1 b2, sem_pexpr ictx p b1 -> sem_pexpr octx p b2 -> b1 = b2.
  Proof.
    induction p; crush; inv H; inv H0; firstorder.
    destruct b.
    - apply sem_pred_det with (e:=p0); auto.
    - apply negb_inj. apply sem_pred_det with (e:=p0); auto.
  Qed.

  Lemma sem_pred_expr_det :
    forall A B p b1 b2 f (s: forall G, @Abstr.ctx G -> A -> B -> Prop),
      (forall p b1 b2, s _ ictx p b1 -> s _ octx p b2 -> b1 = b2) ->
      sem_pred_expr f (s _) ictx p b1 -> sem_pred_expr f (s _) octx p b2 -> b1 = b2.
  Proof.
    induction p; crush.
    - inv H0. inv H1. eauto.
    - inv H0; inv H1; eauto; exploit sem_pexpr_det; eauto; discriminate.
  Qed.

  Lemma sem_predset_det:
    forall f ps ps',
      sem_predset ictx f ps ->
      sem_predset octx f ps' ->
      forall x, ps !! x = ps' !! x.
  Proof.
    intros. inv H. inv H0. eauto using sem_pexpr_det.
  Qed.

  Lemma sem_regset_det:
    forall f rs rs',
      sem_regset ictx f rs ->
      sem_regset octx f rs' ->
      forall x, rs !! x = rs' !! x.
  Proof.
    intros. inv H. inv H0.
    specialize (H1 x). specialize (H x).
    eapply sem_pred_expr_det in H1; eauto.
    exact sem_value_det.
  Qed.

  Lemma sem_det :
    forall p i cf i' cf',
      sem ictx p (i, cf) ->
      sem octx p (i', cf') ->
      cf = cf' /\ match_states i i'.
  Proof.
    repeat inversion 1; subst; split.
    - eauto using sem_pred_expr_det, sem_exit_det.
    - inv H11; inv H12; inv H2; inv H3;
      constructor; intros;
      eauto using sem_pexpr_det, sem_pred_expr_det, sem_value_det, sem_mem_det.
  Qed.

  Lemma sem_pexpr_corr :
    forall p b, sem_pexpr ictx p b -> sem_pexpr octx p b.
  Proof.
    induction p; crush; inv H; constructor;
      try solve [try inv H3; firstorder].
    now apply sem_pred_corr.
  Qed.

  Lemma sem_pred_exec_beq_correct2 :
    forall A B (sem: forall G, @Abstr.ctx G -> A -> B -> Prop) a p r R,
      (forall x y,
          sem _ ictx x y ->
          exists y', sem _ octx x y' /\ R y y') ->
      sem_pred_expr a (sem _) ictx p r ->
      exists r', sem_pred_expr a (sem _) octx p r' /\ R r r'.
  Proof.
    induction p; crush.
    - inv H0. apply H in H4. simplify.
      exists x; split; auto.
      constructor; auto.
      now apply sem_pexpr_corr.
    - inv H0.
      + apply H in H6; simplify.
        exists x; split; auto.
        constructor; auto.
        now apply sem_pexpr_corr.
      + exploit IHp; auto. exact H6. intros. simplify.
        exists x; split; auto.
        apply sem_pred_expr_cons_false; auto.
        now apply sem_pexpr_corr.
  Qed.

  Lemma sem_pred_expr_corr :
    forall A B (sem: forall G, @Abstr.ctx G -> A -> B -> Prop) a p r,
      (forall x y, sem _ ictx x y -> sem _ octx x y) ->
      sem_pred_expr a (sem _) ictx p r ->
      sem_pred_expr a (sem _) octx p r.
  Proof.
    intros.
    assert
      (forall x y,
          sem _ ictx x y ->
          exists y', sem _ octx x y' /\ eq y y') by firstorder.
    pose proof (sem_pred_exec_beq_correct2 _ _ sem a p r _ H1 H0).
    crush.
  Qed.

  Lemma sem_correct:
    forall f i cf, sem ictx f (i, cf) -> sem octx f (i, cf).
  Proof.
    intros. inv H. constructor.
    - inv H2. constructor; intros. specialize (H x).
      apply sem_pred_expr_corr; auto. exact sem_value_corr.
    - inv H3; constructor; intros. specialize (H x).
      now apply sem_pexpr_corr.
    - apply sem_pred_expr_corr; auto. exact sem_mem_corr.
    - apply sem_pred_expr_corr; auto. exact sem_exit_corr.
  Qed.

End CORRECT.

Section SEM_PRED_EXEC.

  Context (A: Type).
  Context (ctx: @Abstr.ctx A).

  Lemma sem_pexpr_negate :
    forall p b,
      sem_pexpr ctx p b ->
      sem_pexpr ctx (¬ p) (negb b).
  Proof.
    induction p; crush.
    - destruct_match. destruct b0; crush. inv Heqp0.
      constructor. inv H. rewrite negb_involutive. auto.
      constructor. inv H. auto.
    - inv H. constructor.
    - inv H. constructor.
    - inv H. inv H3.
      + apply IHp1 in H. solve [constructor; auto].
      + apply IHp2 in H. solve [constructor; auto].
      + apply IHp1 in H2. apply IHp2 in H4. solve [constructor; auto].
    - inv H. inv H3.
      + apply IHp1 in H. solve [constructor; auto].
      + apply IHp2 in H. solve [constructor; auto].
      + apply IHp1 in H2. apply IHp2 in H4. solve [constructor; auto].
  Qed.

  Lemma sem_pexpr_negate2 :
    forall p b,
      sem_pexpr ctx (¬ p) (negb b) ->
      sem_pexpr ctx p b.
  Proof.
    induction p; crush.
    - destruct_match. destruct b0; crush. inv Heqp0.
      constructor. inv H. rewrite negb_involutive in *. auto.
      constructor. inv H. auto.
    - inv H. destruct b; try discriminate. constructor.
    - inv H. destruct b; try discriminate. constructor.
    - inv H. destruct b; try discriminate.
      + constructor. inv H1; eauto.
      + destruct b; try discriminate. constructor; eauto.
    - inv H. destruct b; try discriminate.
      + constructor. inv H1; eauto.
      + destruct b; try discriminate. constructor; eauto.
  Qed.

  Lemma sem_pexpr_negate2' :
    forall p b,
      sem_pexpr ctx (¬ p) b ->
      sem_pexpr ctx p (negb b).
  Proof.
    intros. rewrite <- negb_involutive in H.
    auto using sem_pexpr_negate2.
  Qed.

  Lemma sem_pexpr_negate' :
    forall p b,
      sem_pexpr ctx p (negb b) ->
      sem_pexpr ctx (¬ p) b.
  Proof.
    intros. rewrite <- negb_involutive.
    auto using sem_pexpr_negate.
  Qed.

  Lemma sem_pexpr_evaluable :
    forall f_p ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p, exists b, sem_pexpr ctx (from_pred_op f_p p) b.
  Proof.
    induction p; crush.
    - destruct_match. inv Heqp0. destruct b. econstructor. eauto.
      econstructor. eapply sem_pexpr_negate. eauto.
    - econstructor. constructor.
    - econstructor. constructor.
    - destruct x0, x; solve [eexists; constructor; auto].
    - destruct x0, x; solve [eexists; constructor; auto].
  Qed.

  Lemma sem_pexpr_eval1 :
    forall f_p ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        eval_predf ps p = false ->
        sem_pexpr ctx (from_pred_op f_p p) false.
  Proof.
    induction p; crush.
    - destruct_match. inv Heqp0.
      destruct b.
      + cbn in H0. rewrite <- H0. eauto.
      + replace false with (negb true) by auto.
        apply sem_pexpr_negate. cbn in H0.
        apply negb_true_iff in H0. rewrite negb_involutive in H0.
        rewrite <- H0. eauto.
     - constructor.
     - rewrite eval_predf_Pand in H0.
       apply andb_false_iff in H0. inv H0. eapply IHp1 in H1.
       pose proof (sem_pexpr_evaluable _ _ H p2) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace false with (false && x) by auto.
       constructor; auto.
       eapply IHp2 in H1.
       pose proof (sem_pexpr_evaluable _ _ H p1) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace false with (x && false) by eauto with bool.
       apply sem_pexpr_Pand; auto.
     - rewrite eval_predf_Por in H0.
       apply orb_false_iff in H0. inv H0.
       replace false with (false || false) by auto.
       apply sem_pexpr_Por; auto.
  Qed.

  Lemma sem_pexpr_eval2 :
    forall f_p ps,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        eval_predf ps p = true ->
        sem_pexpr ctx (from_pred_op f_p p) true.
  Proof.
    induction p; crush.
    - destruct_match. inv Heqp0.
      destruct b.
      + cbn in H0. rewrite <- H0. eauto.
      + replace true with (negb false) by auto.
        apply sem_pexpr_negate. cbn in H0.
        apply negb_true_iff in H0.
        rewrite <- H0. eauto.
     - constructor.
     - rewrite eval_predf_Pand in H0.
       apply andb_true_iff in H0. inv H0.
       replace true with (true && true) by auto.
       constructor; auto.
     - rewrite eval_predf_Por in H0.
       apply orb_true_iff in H0. inv H0. eapply IHp1 in H1.
       pose proof (sem_pexpr_evaluable _ _ H p2) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace true with (true || x) by auto.
       apply sem_pexpr_Por; auto.
       eapply IHp2 in H1.
       pose proof (sem_pexpr_evaluable _ _ H p1) as EVAL.
       inversion_clear EVAL as [x EVAL2].
       replace true with (x || true) by eauto with bool.
       apply sem_pexpr_Por; auto.
  Qed.

  Lemma sem_pexpr_eval :
    forall f_p ps b,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        eval_predf ps p = b ->
        sem_pexpr ctx (from_pred_op f_p p) b.
  Proof.
    intros; destruct b; eauto using sem_pexpr_eval1, sem_pexpr_eval2.
  Qed.

  Lemma sem_pexpr_eval_inv :
    forall f_p ps b,
      (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
      forall p,
        sem_pexpr ctx (from_pred_op f_p p) b ->
        eval_predf ps p = b.
  Proof.
    induction p; intros.
    - cbn in H0. destruct_match. destruct b0; cbn in *.
      + specialize (H p0). eapply sem_pexpr_det; eauto. apply similar_refl.
      + rewrite <- negb_involutive in H0. apply sem_pexpr_negate2 in H0.
        symmetry; apply negb_sym. eapply sem_pexpr_det; eauto.
        apply similar_refl.
    - now inv H0.
    - now inv H0.
    - inv H0; try inv H4; rewrite eval_predf_Pand.
      + apply IHp1 in H0. rewrite H0. auto.
      + apply IHp2 in H0. rewrite H0. auto with bool.
      + apply IHp2 in H5. apply IHp1 in H3. rewrite H3. rewrite H5. auto.
    - inv H0; try inv H4; rewrite eval_predf_Por.
      + apply IHp1 in H0. rewrite H0. auto.
      + apply IHp2 in H0. rewrite H0. auto with bool.
      + apply IHp2 in H5. apply IHp1 in H3. rewrite H3. rewrite H5. auto.
  Qed.

  Context {C B: Type}.
  Context (f: PTree.t pred_pexpr).
  Context (ps: PMap.t bool).
  Context (a_sem: @Abstr.ctx A -> C -> B -> Prop).

  Context (F_EVALULABLE: forall x, sem_pexpr ctx (get_forest_p' x f) ps !! x).

  Lemma sem_pexpr_equiv :
    forall p1 p2 b,
      p1 == p2 ->
      sem_pexpr ctx (from_pred_op f p1) b ->
      sem_pexpr ctx (from_pred_op f p2) b.
  Proof.
    intros.
    eapply sem_pexpr_eval_inv in H0; eauto.
    eapply sem_pexpr_eval; eauto.
  Qed.

  Lemma sem_pred_expr_in_true :
    forall pe v,
      sem_pred_expr f a_sem ctx pe v ->
      exists p e, NE.In (p, e) pe
                  /\ sem_pexpr ctx (from_pred_op f p) true
                  /\ a_sem ctx e v.
  Proof.
    induction pe; crush.
    - inv H. do 2 eexists; split; try split; eauto. constructor.
    - inv H.
      + do 2 eexists; split; try split; eauto. constructor; tauto.
      + exploit IHpe; eauto. simplify.
        do 2 eexists; split; try split; eauto. constructor; tauto.
  Qed.

End SEM_PRED_EXEC.

Module HashExprNorm(HS: Hashable).
  Module H := HashTree(HS).

  Definition norm_tree: Type := PTree.t pred_op * H.hash_tree.

  Fixpoint norm_expression (max: predicate) (pe: predicated HS.t) (h: H.hash_tree)
    : norm_tree :=
    match pe with
    | NE.singleton (p, e) =>
        let (hashed_e, h') := H.hash_value max e h in
        (PTree.set hashed_e p (PTree.empty _), h')
    | (p, e) ::| pr =>
        let (hashed_e, h') := H.hash_value max e h in
        let (norm_pr, h'') := norm_expression max pr h' in
        match norm_pr ! hashed_e with
        | Some pr_op =>
            (PTree.set hashed_e (pr_op ∨ p) norm_pr, h'')
        | None =>
            (PTree.set hashed_e p norm_pr, h'')
        end
    end.

  Definition mk_pred_stmnt' (e: predicate) p_e := ¬ p_e ∨ Plit (true, e).

  Definition mk_pred_stmnt t := PTree.fold (fun x a b => mk_pred_stmnt' a b ∧ x) t T.

  Definition mk_pred_stmnt_l (t: list (predicate * pred_op)) :=
    fold_left (fun x a => uncurry mk_pred_stmnt' a ∧ x) t T.

  Definition encode_expression max pe h :=
    let (tree, h) := norm_expression max pe h in
    (mk_pred_stmnt tree, h).

  Definition pred_expr_dec: forall pe1 pe2: predicated HS.t,
    {pe1 = pe2} + {pe1 <> pe2}.
  Proof.
    pose proof HS.eq_dec as X.
    pose proof (Predicate.eq_dec peq).
    pose proof (NE.eq_dec _ X).
    assert (forall a b: pred_op * HS.t, {a = b} + {a <> b})
     by decide equality.
    decide equality.
  Defined.

  Definition beq_pred_expr' (pe1 pe2: predicated HS.t) : bool :=
    if pred_expr_dec pe1 pe2 then true else
    let (p1, h) := encode_expression 1%positive pe1 (PTree.empty _) in
    let (p2, h') := encode_expression 1%positive pe2 h in
    equiv_check p1 p2.

  Lemma mk_pred_stmnt_equiv' :
    forall l l' e p,
      mk_pred_stmnt_l l == mk_pred_stmnt_l l' ->
      In (e, p) l ->
      list_norepet (map fst l) ->
      (exists p', In (e, p') l' /\ p == p')
      \/ ~ In e (map fst l') /\ p == ⟂.
  Proof. Abort.

  Lemma mk_pred_stmnt_equiv :
    forall tree tree',
      mk_pred_stmnt tree == mk_pred_stmnt tree'.
  Proof. Abort.

  Definition tree_equiv_check_el (np2: PTree.t pred_op) (n: positive) (p: pred_op): bool :=
    match np2 ! n with
    | Some p' => equiv_check p p'
    | None => equiv_check p ⟂
    end.

  Definition tree_equiv_check_None_el (np2: PTree.t pred_op) (n: positive) (p: pred_op): bool :=
    match np2 ! n with
    | Some p' => true
    | None => equiv_check p ⟂
    end.

  Definition beq_pred_expr (pe1 pe2: predicated HS.t) : bool :=
    if pred_expr_dec pe1 pe2 then true else
    let (np1, h) := norm_expression 1 pe1 (PTree.empty _) in
    let (np2, h') := norm_expression 1 pe2 h in
    forall_ptree (tree_equiv_check_el np2) np1
    && forall_ptree (tree_equiv_check_None_el np1) np2.

  Lemma beq_pred_expr_correct:
    forall np1 np2 e p p',
      forall_ptree (tree_equiv_check_el np2) np1 = true ->
      np1 ! e = Some p ->
      np2 ! e = Some p' ->
      p == p'.
  Proof.
    intros.
    eapply forall_ptree_true in H; try eassumption.
    unfold tree_equiv_check_el in H.
    rewrite H1 in H. now apply equiv_check_correct.
  Qed.

  Lemma beq_pred_expr_correct2:
    forall np1 np2 e p,
      forall_ptree (tree_equiv_check_el np2) np1 = true ->
      np1 ! e = Some p ->
      np2 ! e = None ->
      p == ⟂.
  Proof.
    intros.
    eapply forall_ptree_true in H; try eassumption.
    unfold tree_equiv_check_el in H.
    rewrite H1 in H. now apply equiv_check_correct.
  Qed.

  Lemma beq_pred_expr_correct3:
    forall np1 np2 e p,
      forall_ptree (tree_equiv_check_None_el np1) np2 = true ->
      np1 ! e = None ->
      np2 ! e = Some p ->
      p == ⟂.
  Proof.
    intros.
    eapply forall_ptree_true in H; try eassumption.
    unfold tree_equiv_check_None_el in H.
    rewrite H0 in H. now apply equiv_check_correct.
  Qed.

  Section PRED_PROOFS.

  Context {G B: Type}.
  Context (f: PTree.t pred_pexpr).
  Context (ps: PMap.t bool).
  Context (a_sem: @Abstr.ctx G -> HS.t -> B -> Prop).
  Context (ctx: @Abstr.ctx G).

  Context (F_EVALULABLE: forall x, sem_pexpr ctx (get_forest_p' x f) ps !! x).

  Variant sem_pred_tree: PTree.t HS.t -> PTree.t pred_op -> B -> Prop :=
  | sem_pred_tree_intro :
      forall expr e v et pt pr,
        sem_pexpr ctx (from_pred_op f pr) true ->
        a_sem ctx expr v ->
        pt ! e = Some pr ->
        et ! e = Some expr ->
        sem_pred_tree et pt v.

  Lemma norm_expression_in :
    forall pe et pt h x y,
      H.wf_hash_table h ->
      norm_expression 1 pe h = (pt, et) ->
      h ! x = Some y ->
      et ! x = Some y.
  Proof.
    induction pe; crush; repeat (destruct_match; try discriminate; []).
    - inv H0. eauto using H.hash_constant.
    - destruct_match.
      + inv H0. eapply IHpe.
        eapply H.wf_hash_table_distr; eauto. eauto.
        eauto using H.hash_constant.
      + inv H0. eapply IHpe.
        eapply H.wf_hash_table_distr; eauto. eauto.
        eauto using H.hash_constant.
  Qed.

  Lemma norm_expression_exists :
    forall pe et pt h x y,
      H.wf_hash_table h ->
      norm_expression 1 pe h = (pt, et) ->
      pt ! x = Some y ->
      exists z, et ! x = Some z.
  Proof.
    induction pe; crush; repeat (destruct_match; try discriminate; []).
    - inv H0. destruct (peq x h0); subst; inv H1.
      + eexists. eauto using H.hash_value_in.
      + rewrite PTree.gso in H2 by auto. now rewrite PTree.gempty in H2.
    - assert (H.wf_hash_table h1) by eauto using H.wf_hash_table_distr.
      destruct_match; inv H0.
      + destruct (peq h0 x); subst; eauto.
        rewrite PTree.gso in H1 by auto. eauto.
      + destruct (peq h0 x); subst; eauto.
        * pose proof Heqp0 as X.
          eapply H.hash_value_in in Heqp0.
          eapply norm_expression_in in Heqn; eauto.
        * rewrite PTree.gso in H1 by auto. eauto.
  Qed.

  Lemma norm_expression_wf :
    forall pe et pt h,
      H.wf_hash_table h ->
      norm_expression 1 pe h = (pt, et) ->
      H.wf_hash_table et.
  Proof.
    induction pe; crush; repeat (destruct_match; try discriminate; []).
    - inv H0. eauto using H.wf_hash_table_distr.
    - destruct_match.
      + inv H0. eapply IHpe.
        eapply H.wf_hash_table_distr; eauto. eauto.
      + inv H0. eapply IHpe.
        eapply H.wf_hash_table_distr; eauto. eauto.
  Qed.

  Definition pred_Ht_dec :
    forall x y: pred_op * HS.t, {x = y} + {x <> y}.
  Proof.
    pose proof HS.eq_dec.
    pose proof (@Predicate.eq_dec positive peq).
    decide equality.
  Defined.

  Lemma sem_pred_mutexcl :
    forall pe p t v,
      predicated_mutexcl ((p, t) ::| pe) ->
      sem_pred_expr f a_sem ctx pe v ->
      sem_pexpr ctx (from_pred_op f p) false.
  Proof.
    intros. unfold predicated_mutexcl in H.
    exploit sem_pred_expr_in_true; eauto; simplify.
    unfold "⇒" in *. inv H5.
    destruct (pred_Ht_dec (x, x0) (p, t)); subst.
    { inv e; exfalso; apply H7; auto. }
    assert (NE.In (x, x0) ((p, t) ::| pe)) by (constructor; tauto).
    assert (NE.In (p, t) ((p, t) ::| pe)) by (constructor; tauto).
    pose proof (H3 _ _ H H5 n).
    assert (forall c, eval_predf c x = true -> eval_predf c (¬ p) = true)
      by eauto.
    eapply sem_pexpr_eval_inv in H1; eauto.
    eapply sem_pexpr_eval; eauto. apply H9 in H1.
    unfold eval_predf in *. rewrite negate_correct in H1.
    symmetry in H1. apply negb_sym in H1. auto.
  Qed.

  Lemma exec_tree_exec_pe :
    forall pe et pt v h
      (MUTEXCL: predicated_mutexcl pe),
      H.wf_hash_table h ->
      norm_expression 1 pe h = (pt, et) ->
      sem_pred_tree et pt v ->
      sem_pred_expr f a_sem ctx pe v.
  Proof.
    induction pe; simplify; repeat (destruct_match; try discriminate; []).
    - inv Heqp. inv H0. inv H1.
      destruct (peq e h0); subst.
      2: { rewrite PTree.gso in H3 by auto.
           rewrite PTree.gempty in H3. discriminate. }
      assert (expr = t).
      { apply H.hash_value_in in Heqp0. rewrite H4 in Heqp0. now inv Heqp0. }
      subst. constructor; auto. rewrite PTree.gss in H3. inv H3; auto.
    - inv Heqp. inv H1. destruct_match; inv H0; destruct (peq h0 e); subst.
      + rewrite PTree.gss in H4. inv H4. inv H2. inv H1.
        * exploit IHpe. eauto using predicated_cons.
          eapply H.wf_hash_table_distr; eauto. eauto.
          econstructor. eauto. eauto. eauto. eauto. intros.
          assert (sem_pexpr ctx (from_pred_op f p) false)
            by (eapply sem_pred_mutexcl; eauto).
          eapply sem_pred_expr_cons_false; auto.
        * assert (et ! e = Some t).
          { eapply norm_expression_in. eapply H.wf_hash_table_distr; eauto.
            eauto. apply H.hash_value_in in Heqp0.  auto. }
          rewrite H1 in H5. inv H5.
          constructor; auto.
      + exploit IHpe. eauto using predicated_cons.
        eapply H.wf_hash_table_distr; eauto. eauto.
        econstructor. eauto. eauto. rewrite PTree.gso in H4; eauto. auto.
        intros.
        assert (sem_pexpr ctx (from_pred_op f p) false)
          by (eapply sem_pred_mutexcl; eauto).
        eapply sem_pred_expr_cons_false; auto.
      + rewrite PTree.gss in H4. inv H4.
        econstructor; auto.
        assert (et ! e = Some t).
          { eapply norm_expression_in. eapply H.wf_hash_table_distr; eauto.
            eauto. apply H.hash_value_in in Heqp0.  auto. }
        rewrite H0 in H5; inv H5. auto.
      + rewrite PTree.gso in H4 by auto.
        exploit IHpe. eauto using predicated_cons.
        eapply H.wf_hash_table_distr; eauto. eauto.
        econstructor. eauto. eauto. eauto. eauto. intros.
        assert (sem_pexpr ctx (from_pred_op f p) false)
          by (eapply sem_pred_mutexcl; eauto).
        eapply sem_pred_expr_cons_false; auto.
  Qed.

  Lemma exec_pe_exec_tree :
    forall pe et pt v h
      (MUTEXCL: predicated_mutexcl pe),
      H.wf_hash_table h ->
      norm_expression 1 pe h = (pt, et) ->
      sem_pred_expr f a_sem ctx pe v ->
      sem_pred_tree et pt v.
  Proof.
    induction pe; simplify; repeat (destruct_match; try discriminate; []).
    - inv H0. inv H1. econstructor; eauto. apply PTree.gss.
      eapply H.hash_value_in; eauto.
    - inv H1.
      + destruct_match.
        * inv H0. econstructor.
          2: { eauto. }
          2: { apply PTree.gss. }
          constructor; tauto.
          eapply norm_expression_in. eapply H.wf_hash_table_distr; eauto.
          eauto. eapply H.hash_value_in; eauto.
        * inv H0. econstructor. eauto. eauto. apply PTree.gss.
          eapply norm_expression_in. eapply H.wf_hash_table_distr; eauto.
          eauto. eapply H.hash_value_in; eauto.
      + destruct_match.
        * inv H0. exploit IHpe.
          eauto using predicated_cons.
          eapply H.wf_hash_table_distr; eauto.
          eauto. eauto. intros. inv H0.
          destruct (peq e h0); subst.
          -- rewrite H3 in Heqo. inv Heqo.
             econstructor.
             3: { apply PTree.gss. }
             constructor; tauto. eauto. auto.
          -- econstructor. eauto. eauto. rewrite PTree.gso by eauto. auto.
             auto.
        * inv H0. exploit IHpe.
          eauto using predicated_cons.
          eapply H.wf_hash_table_distr; eauto.
          eauto. eauto. intros. inv H0.
          destruct (peq e h0); subst.
          -- rewrite H3 in Heqo; discriminate.
          -- econstructor; eauto. rewrite PTree.gso by auto. auto.
  Qed.

  Lemma beq_pred_expr_correct_top:
    forall p1 p2 v
           (MUTEXCL1: predicated_mutexcl p1)
           (MUTEXCL2: predicated_mutexcl p2),
      beq_pred_expr p1 p2 = true ->
      sem_pred_expr f a_sem ctx p1 v ->
      sem_pred_expr f a_sem ctx p2 v.
  Proof.
    unfold beq_pred_expr; intros.
    destruct_match; subst; auto.
    repeat (destruct_match; []).
    symmetry in H. apply andb_true_eq in H. inv H.
    symmetry in H1. symmetry in H2.
    pose proof Heqn0. eapply norm_expression_wf in H.
    2: { unfold H.wf_hash_table; intros. now rewrite PTree.gempty in H3. }
    eapply exec_tree_exec_pe; eauto.
    eapply exec_pe_exec_tree in H0; auto.
    3: { eauto. }
    2: { unfold H.wf_hash_table; intros. now rewrite PTree.gempty in H3. }
    inv H0. destruct (t0 ! e) eqn:?.
    - assert (pr == p) by eauto using beq_pred_expr_correct.
      assert (sem_pexpr ctx (from_pred_op f p) true).
      { eapply sem_pexpr_eval; eauto. eapply sem_pexpr_eval_inv in H3; eauto. }
      econstructor. apply H7. eauto. eauto.
      eapply norm_expression_in; eauto.
    - assert (pr == ⟂) by eauto using beq_pred_expr_correct2.
      eapply sem_pexpr_eval_inv in H3; eauto. now rewrite H0 in H3.
  Qed.

  Lemma beq_pred_expr_correct_top2:
    forall p1 p2 v
           (MUTEXCL1: predicated_mutexcl p1)
           (MUTEXCL2: predicated_mutexcl p2),
      beq_pred_expr p1 p2 = true ->
      sem_pred_expr f a_sem ctx p2 v ->
      sem_pred_expr f a_sem ctx p1 v.
  Proof.
    unfold beq_pred_expr; intros.
    destruct_match; subst; auto.
    repeat (destruct_match; []).
    symmetry in H. apply andb_true_eq in H. inv H.
    symmetry in H1. symmetry in H2.
    pose proof Heqn0. eapply norm_expression_wf in H.
    2: { unfold H.wf_hash_table; intros. now rewrite PTree.gempty in H3. }
    eapply exec_tree_exec_pe; auto.
    2: { eauto. }
    unfold H.wf_hash_table; intros. now rewrite PTree.gempty in H3.
    eapply exec_pe_exec_tree in H0; auto.
    3: { eauto. }
    2: { auto. }
    inv H0. destruct (t ! e) eqn:?.
    - assert (p == pr) by eauto using beq_pred_expr_correct.
      assert (sem_pexpr ctx (from_pred_op f p) true).
      { eapply sem_pexpr_eval; eauto. eapply sem_pexpr_eval_inv in H3; eauto. }
      econstructor. apply H7. eauto. eauto.
      exploit norm_expression_exists.
      2: { eapply Heqn0. }  unfold H.wf_hash_table; intros * YH.
      now rewrite PTree.gempty in YH. eauto. simplify.
      exploit norm_expression_in. 2: { eauto. } auto. eauto. intros.
      crush.
    - assert (pr == ⟂) by eauto using beq_pred_expr_correct3.
      eapply sem_pexpr_eval_inv in H3; eauto. now rewrite H0 in H3.
  Qed.

  End PRED_PROOFS.

End HashExprNorm.

Module HN := HashExprNorm(HashExpr).
Module EHN := HashExprNorm(EHashExpr).

Definition check_mutexcl {A} (pe: predicated A) :=
  let preds := map fst (NE.to_list pe) in
  let pairs := map (fun x => x → negate (or_list (remove (Predicate.eq_dec peq) x preds))) preds in
  match sat_pred_simple (simplify (negate (and_list pairs))) with
  | None => true
  | _ => false
  end.

(* Import ListNotations. *)
(* Compute deep_simplify peq (and_list (map (fun x => x → negate (or_list (remove (Predicate.eq_dec peq) x [Plit (true, 2)]))) [Plit (true, 2)])). *)

Lemma check_mutexcl_correct:
  forall A (pe: predicated A),
    check_mutexcl pe = true ->
    predicated_mutexcl pe.
Proof. Admitted.

Lemma check_mutexcl_singleton :
  check_mutexcl (NE.singleton (T, EEbase)) = true.
Proof. crush. Qed.

Definition check_mutexcl_tree {A} (f: PTree.t (predicated A)) :=
  forall_ptree (fun _ => check_mutexcl) f.

Lemma check_mutexcl_tree_correct:
  forall A (f: PTree.t (predicated A)) i pe,
    check_mutexcl_tree f = true ->
    f ! i = Some pe ->
    predicated_mutexcl pe.
Proof.
  unfold check_mutexcl_tree; intros.
  eapply forall_ptree_true in H; eauto using check_mutexcl_correct.
Qed.

Definition check f1 f2 :=
  RTree.beq HN.beq_pred_expr f1.(forest_regs) f2.(forest_regs)
  && PTree.beq beq_pred_pexpr f1.(forest_preds) f2.(forest_preds)
  && EHN.beq_pred_expr f1.(forest_exit) f2.(forest_exit)
  && check_mutexcl_tree f1.(forest_regs)
  && check_mutexcl_tree f2.(forest_regs)
  && check_mutexcl f1.(forest_exit)
  && check_mutexcl f2.(forest_exit).

Lemma sem_pexpr_forward_eval1 :
  forall A ctx f_p ps,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
    forall p,
      @sem_pexpr A ctx (from_pred_op f_p p) false ->
      eval_predf ps p = false.
Proof.
  induction p; crush.
  - destruct_match. inv Heqp0. destruct b.
    cbn. specialize (H p0).
    eapply sem_pexpr_det; eauto. apply similar_refl.
    specialize (H p0).
    replace false with (negb true) in H0 by auto.
    eapply sem_pexpr_negate2 in H0. cbn.
    symmetry; apply negb_sym. cbn.
    eapply sem_pexpr_det; eauto. apply similar_refl.
  - inv H0.
  - inv H0. inv H2. rewrite eval_predf_Pand. rewrite IHp1; eauto.
    rewrite eval_predf_Pand. rewrite IHp2; eauto with bool.
  - inv H0. rewrite eval_predf_Por. rewrite IHp1; eauto.
Qed.

Lemma sem_pexpr_forward_eval2 :
  forall A ctx f_p ps,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
    forall p,
      @sem_pexpr A ctx (from_pred_op f_p p) true ->
      eval_predf ps p = true.
Proof.
  induction p; crush.
  - destruct_match. inv Heqp0. destruct b.
    cbn. specialize (H p0).
    eapply sem_pexpr_det; eauto. apply similar_refl.
    cbn. symmetry. apply negb_sym; cbn.
    replace true with (negb false) in H0 by auto.
    eapply sem_pexpr_negate2 in H0.
    eapply sem_pexpr_det; eauto. apply similar_refl.
  - inv H0.
  - inv H0. rewrite eval_predf_Pand. rewrite IHp1; eauto.
  - inv H0. inv H2. rewrite eval_predf_Por. rewrite IHp1; eauto.
    rewrite eval_predf_Por. rewrite IHp2; eauto with bool.
Qed.

Lemma sem_pexpr_forward_eval :
  forall A ctx f_p ps,
    (forall x, sem_pexpr ctx (get_forest_p' x f_p) ps !! x) ->
    forall p b,
      @sem_pexpr A ctx (from_pred_op f_p p) b ->
      eval_predf ps p = b.
Proof.
  intros; destruct b; eauto using sem_pexpr_forward_eval1, sem_pexpr_forward_eval2.
Qed.

Section BOOLEAN_EQUALITY.

  Context {A B: Type}.
  Context (beqA: A -> B -> bool).

  Fixpoint beq2' (m1: PTree.tree' A) (m2: PTree.tree' B) {struct m1} : bool :=
    match m1, m2 with
    | PTree.Node001 r1, PTree.Node001 r2 => beq2' r1 r2
    | PTree.Node010 x1, PTree.Node010 x2 => beqA x1 x2
    | PTree.Node011 x1 r1, PTree.Node011 x2 r2 => beqA x1 x2 && beq2' r1 r2
    | PTree.Node100 l1, PTree.Node100 l2 => beq2' l1 l2
    | PTree.Node101 l1 r1, PTree.Node101 l2 r2 => beq2' l1 l2 && beq2' r1 r2
    | PTree.Node110 l1 x1, PTree.Node110 l2 x2 => beqA x1 x2 && beq2' l1 l2
    | PTree.Node111 l1 x1 r1, PTree.Node111 l2 x2 r2  => beqA x1 x2 && beq2' l1 l2 && beq2' r1 r2
    | _, _ => false
    end.

  Definition beq2 (m1: PTree.t A) (m2 : PTree.t B) : bool :=
    match m1, m2 with
    | PTree.Empty, PTree.Empty => true
    | PTree.Nodes m1', PTree.Nodes m2' => beq2' m1' m2'
    | _, _ => false
    end.

  Let beq2_optA (o1: option A) (o2: option B) : bool :=
    match o1, o2 with
    | None, None => true
    | Some a1, Some a2 => beqA a1 a2
    | _, _ => false
    end.

  Lemma beq_correct_bool:
    forall m1 m2,
      beq2 m1 m2 = true <-> (forall x, beq2_optA (m1 ! x) (m2 ! x) = true).
  Proof.
    Local Transparent PTree.Node.
    assert (beq_NN: forall l1 o1 r1 l2 o2 r2,
               PTree.not_trivially_empty l1 o1 r1 ->
               PTree.not_trivially_empty l2 o2 r2 ->
               beq2 (PTree.Node l1 o1 r1) (PTree.Node l2 o2 r2) =
                 beq2 l1 l2 && beq2_optA o1 o2 && beq2 r1 r2).
    { intros.
      destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction;
        simpl; rewrite ? andb_true_r, ? andb_false_r; auto.
      rewrite andb_comm; auto.
      f_equal; rewrite andb_comm; auto. }
    induction m1 using PTree.tree_ind; [|induction m2 using PTree.tree_ind].
    - intros. simpl; split; intros.
      + destruct m2; try discriminate. simpl; auto.
      + replace m2 with (@PTree.Empty B); auto. apply PTree.extensionality; intros x.
        specialize (H x). destruct (m2 ! x); simpl; easy.
    - split; intros.
      + destruct (PTree.Node l o r); try discriminate. simpl; auto.
      + replace (PTree.Node l o r) with (@PTree.Empty A); auto. apply PTree.extensionality; intros x.
        specialize (H0 x). destruct ((PTree.Node l o r) ! x); simpl in *; easy.
    - rewrite beq_NN by auto. split; intros.
      + InvBooleans. rewrite ! PTree.gNode. destruct x.
        * apply IHm0; auto.
        * apply IHm1; auto.
        * auto.
      + apply andb_true_intro; split; [apply andb_true_intro; split|].
        * apply IHm1. intros. specialize (H1 (xO x)); rewrite ! PTree.gNode in H1; auto.
        * specialize (H1 xH); rewrite ! PTree.gNode in H1; auto.
        * apply IHm0. intros. specialize (H1 (xI x)); rewrite ! PTree.gNode in H1; auto.
  Qed.

  Theorem beq2_correct:
    forall m1 m2,
      beq2 m1 m2 = true <->
        (forall (x: PTree.elt),
            match m1 ! x, m2 ! x with
            | None, None => True
            | Some y1, Some y2 => beqA y1 y2 = true
            | _, _ => False
            end).
  Proof.
    intros. rewrite beq_correct_bool. unfold beq2_optA. split; intros.
    - specialize (H x). destruct (m1 ! x), (m2 ! x); intuition congruence.
    - specialize (H x). destruct (m1 ! x), (m2 ! x); intuition auto.
  Qed.

End BOOLEAN_EQUALITY.

Section GENERIC_CONTEXT.

Context {A: Type}.
Context (ctx: @ctx A).

(*|
Suitably restrict the predicate set so that one can evaluate a hashed predicate
using that predicate set.  However, one issue might be that we do not know that
all the atoms of the original formula are actually evaluable.
|*)

Definition match_pred_states
  (ht: PHT.hash_tree) (p_out: pred_op) (pred_set: predset) :=
  forall (p: positive) (br: bool) (p_in: pred_expression),
    PredIn p p_out ->
    ht ! p = Some p_in ->
    sem_pred ctx p_in (pred_set !! p).

Lemma eval_hash_predicate :
  forall max p_in ht p_out ht' br pred_set,
    hash_predicate max p_in ht = (p_out, ht') ->
    sem_pexpr ctx p_in br ->
    match_pred_states ht' p_out pred_set ->
    eval_predf pred_set p_out = br.
Proof.
  induction p_in; simplify.
  + repeat destruct_match. inv H.
    unfold eval_predf. cbn.
    inv H0. inv H4. unfold match_pred_states in H1.
    specialize (H1 h br).
Abort.

Local Open Scope monad_scope.
Fixpoint sem_valueF (e: expression) : option val :=
  match e with
  | Ebase (Reg r) => Some ((ctx_rs ctx) !! r)
  | Eop op args =>
    do lv <- sem_val_listF args;
    Op.eval_operation (ctx_ge ctx) (ctx_sp ctx) op lv (ctx_mem ctx)
  | Eload chunk addr args mexp =>
    do m' <- sem_memF mexp;
    do lv <- sem_val_listF args;
    do a <- Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr lv;
    Mem.loadv chunk m' a
  | _ => None
  end
with sem_memF (e: expression) : option mem :=
  match e with
  | Ebase Mem => Some (ctx_mem ctx)
  | Estore vexp chunk addr args mexp =>
    do m' <- sem_memF mexp;
    do v <- sem_valueF vexp;
    do lv <- sem_val_listF args;
    do a <- Op.eval_addressing (ctx_ge ctx) (ctx_sp ctx) addr lv;
    Mem.storev chunk m' a v
  | _ => None
  end
with sem_val_listF (e: expression_list) : option (list val) :=
  match e with
  | Enil => Some nil
  | Econs e l =>
    do v <- sem_valueF e;
    do lv <- sem_val_listF l;
    Some (v :: lv)
  end.

Definition sem_predF (e: pred_expression): option bool :=
  match e with
  | PEbase p => Some ((ctx_ps ctx) !! p)
  | PEsetpred c args =>
    do lv <- sem_val_listF args;
    Op.eval_condition c lv (ctx_mem ctx)
  end.
Local Close Scope monad_scope.

Definition sem_pexprF := TVL.eval_predicate sem_predF.

Lemma sem_valueF_correct :
  forall e v m,
    (sem_valueF e = Some v -> sem_value ctx e v)
    /\ (sem_memF e = Some m -> sem_mem ctx e m).
Proof.
  induction e using expression_ind2 with
    (P0 := fun p => forall l, sem_val_listF p = Some l -> sem_val_list ctx p l); intros.
  - split; intros; destruct r; try discriminate; cbn in *; inv H; constructor.
  - split; intros.
    + cbn in *; unfold Option.bind in *; destruct_match; try discriminate.
      econstructor; eauto.
    + cbn in *. discriminate.
  - split; intros; cbn in *; try discriminate; unfold Option.bind in *;
      repeat (destruct_match; try discriminate; []).
    econstructor; eauto. eapply IHe0; auto.
  - split; intros; cbn in *; try discriminate; unfold Option.bind in *;
      repeat (destruct_match; try discriminate; []).
    econstructor; eauto. eapply IHe3; eauto. eapply IHe1; eauto.
  - cbn in *. inv H. constructor.
  - cbn in *; unfold Option.bind in *;
      repeat (destruct_match; try discriminate; []). inv H. constructor; eauto.
      eapply IHe; auto. apply (ctx_mem ctx).
Qed.

Lemma sem_val_listF_correct :
  forall l vl,
    sem_val_listF l = Some vl ->
    sem_val_list ctx l vl.
Proof.
  induction l.
  - intros. cbn in *. inv H. constructor.
  - cbn; intros. unfold Option.bind in *;
      repeat (destruct_match; try discriminate; []). inv H. constructor; eauto.
    eapply sem_valueF_correct; eauto. apply (ctx_mem ctx).
Qed.

Lemma sem_valueF_correct2 :
  forall e v m,
    (sem_value ctx e v -> sem_valueF e = Some v)
    /\ (sem_mem ctx e m -> sem_memF e = Some m).
Proof.
  induction e using expression_ind2 with
    (P0 := fun p => forall l, sem_val_list ctx p l -> sem_val_listF p = Some l); intros.
  - split; inversion 1; cbn; auto.
  - split; inversion 1; subst; clear H. cbn; unfold Option.bind.
    erewrite IHe; eauto.
  - split; inversion 1; subst; clear H. cbn; unfold Option.bind.
    specialize (IHe0 v m'). inv IHe0.
    erewrite H0; eauto. erewrite IHe; eauto. rewrite H8; auto.
  - split; inversion 1; subst; clear H. cbn; unfold Option.bind.
    specialize (IHe3 v0 m'); inv IHe3.
    specialize (IHe1 v0 m'); inv IHe1.
    erewrite H0; eauto.
    erewrite H1; eauto.
    erewrite IHe2; eauto.
    rewrite H10; auto.
  - inv H. auto.
  - inv H. cbn; unfold Option.bind.
    specialize (IHe v (ctx_mem ctx)). inv IHe.
    erewrite H; eauto.
    erewrite IHe0; eauto.
Qed.

Lemma sem_val_listF_correct2 :
  forall l vl,
    sem_val_list ctx l vl ->
    sem_val_listF l = Some vl.
Proof.
  induction l.
  - inversion 1; subst; auto.
  - inversion 1; subst; clear H.
    specialize (sem_valueF_correct2 e v (ctx_mem ctx)); inversion 1; clear H.
    cbn; unfold Option.bind. erewrite H0; eauto. erewrite IHl; eauto.
Qed.

(* Definition eval_pexpr_atom {G} (ctx: @Abstr.ctx G)  (p: pred_expression) := *)

Lemma sem_pexpr_beq_correct :
  forall p1 p2,
    beq_pred_pexpr p1 p2 = true ->
    sem_pexprF (transf_pred_op p1) = sem_pexprF (transf_pred_op p2).
Proof.
  unfold beq_pred_pexpr; intros.
  destruct_match; subst; auto.
  repeat destruct_match.
  pose proof STV.valid_check_smt_total.
  unfold sem_pexprF.

(*|
This should only require a proof of sem_pexpr_beq_correct, the rest is
straightforward.
|*)

Lemma pred_pexpr_beq_pred_pexpr :
  forall pr a b br,
    PTree.beq beq_pred_pexpr a b = true ->
    sem_pexpr ctx (from_pred_op a pr) br ->
    sem_pexpr ctx (from_pred_op b pr) br.
Proof.
  induction pr; crush.
  - destruct_match. inv Heqp0. destruct b0.
    + unfold get_forest_p' in *.
      apply PTree.beq_correct with (x := p0) in H.
      destruct a ! p0; destruct b ! p0; try (exfalso; assumption); auto.
      eapply sem_pexpr_beq_correct; eauto.
    + replace br with (negb (negb br)) by (now apply negb_involutive).
      replace br with (negb (negb br)) in H0 by (now apply negb_involutive).
      apply sem_pexpr_negate. apply sem_pexpr_negate2 in H0.
      unfold get_forest_p' in *.
      apply PTree.beq_correct with (x := p0) in H.
      destruct a ! p0; destruct b ! p0; try (exfalso; assumption); auto.
      eapply sem_pexpr_beq_correct; eauto.
  - inv H0; try inv H4.
    + eapply IHpr1 in H0; eauto. apply sem_pexpr_Pand_false; tauto.
    + eapply IHpr2 in H0; eauto. apply sem_pexpr_Pand_false; tauto.
    + eapply IHpr1 in H3; eauto. eapply IHpr2 in H5; eauto.
      apply sem_pexpr_Pand_true; auto.
  - inv H0; try inv H4.
    + eapply IHpr1 in H0; eauto. apply sem_pexpr_Por_true; tauto.
    + eapply IHpr2 in H0; eauto. apply sem_pexpr_Por_true; tauto.
    + eapply IHpr1 in H3; eauto. eapply IHpr2 in H5; eauto.
      apply sem_pexpr_Por_false; auto.
Qed.

(*|
This lemma requires a theorem that equivalence of symbolic predicates means they
will be.  This further needs three-valued logic to be able to compare arbitrary
predicates with each other, that will also show that the predicate will also be
computable.
|*)

Lemma sem_pred_exec_beq_correct :
  forall A B (sem: Abstr.ctx -> A -> B -> Prop) p a b r,
    PTree.beq beq_pred_pexpr a b = true ->
    sem_pred_expr a sem ctx p r ->
    sem_pred_expr b sem ctx p r.
Proof.
  induction p; intros; inv H0.
  - constructor; auto. eapply pred_pexpr_beq_pred_pexpr; eauto.
  - constructor; auto. eapply pred_pexpr_beq_pred_pexpr; eauto.
  - apply sem_pred_expr_cons_false; eauto.
    eapply pred_pexpr_beq_pred_pexpr; eauto.
Qed.

End GENERIC_CONTEXT.

Lemma tree_beq_pred_pexpr :
  forall a b x,
    RTree.beq beq_pred_pexpr (forest_preds a) (forest_preds b) = true ->
    beq_pred_pexpr a #p x b #p x = true.
Proof.
  intros. unfold "#p". unfold get_forest_p'.
  apply PTree.beq_correct with (x := x) in H.
  destruct_match; destruct_match; auto.
  unfold beq_pred_pexpr. destruct_match; auto.
Qed.

Lemma tree_beq_pred_expr :
  forall a b x,
    RTree.beq HN.beq_pred_expr (forest_regs a) (forest_regs b) = true ->
    HN.beq_pred_expr a #r x b #r x = true.
Proof.
  intros. unfold "#r" in *.
  apply PTree.beq_correct with (x := (R_indexed.index x)) in H.
  unfold RTree.get in *.
  unfold pred_expr in *.
  destruct_match; destruct_match; auto.
  unfold HN.beq_pred_expr. destruct_match; auto.
Qed.

Section CORRECT.

Context {FUN TFUN: Type}.
Context (ictx: @ctx FUN) (octx: @ctx TFUN) (HSIM: similar ictx octx).

Lemma abstr_check_correct :
  forall i' a b cf,
    check a b = true ->
    sem ictx a (i', cf) ->
    exists ti', sem octx b (ti', cf) /\ match_states i' ti'.
Proof.
  intros.
  assert (EVALUABLE: (exists ps, forall x, sem_pexpr ictx (get_forest_p' x (forest_preds a)) ps !! x)).
  { inv H0. inv H4. eauto. }
  unfold check in H. simplify.
  inv H0. inv H10. inv H11.
  eexists; split; constructor; auto.
  - constructor. intros.
    eapply sem_pred_exec_beq_correct; eauto.
    eapply sem_pred_expr_corr; eauto. now apply sem_value_corr.
    eapply HN.beq_pred_expr_correct_top; eauto.
    { unfold "#r"; destruct_match; eauto using check_mutexcl_tree_correct, predicated_singleton. }
    { unfold "#r"; destruct_match; eauto using check_mutexcl_tree_correct, predicated_singleton. }
    eapply tree_beq_pred_expr; eauto.
  - (* This is where three-valued logic would be needed. *)
    constructor. intros. apply sem_pexpr_beq_correct with (p1 := a #p x0).
    apply tree_beq_pred_pexpr; auto.
    apply sem_pexpr_corr with (ictx:=ictx); auto.
  - eapply sem_pred_exec_beq_correct; eauto.
    eapply sem_pred_expr_corr; eauto. now apply sem_mem_corr.
    eapply HN.beq_pred_expr_correct_top; eauto.
    { unfold "#r"; destruct_match; eauto using check_mutexcl_tree_correct, predicated_singleton. }
    { unfold "#r"; destruct_match; eauto using check_mutexcl_tree_correct, predicated_singleton. }
    eapply tree_beq_pred_expr; eauto.
  - eapply sem_pred_exec_beq_correct; eauto.
    eapply sem_pred_expr_corr; eauto. now apply sem_exit_corr.
    eapply EHN.beq_pred_expr_correct_top; eauto using check_mutexcl_correct.
Qed.

(*|
Proof Sketch:

Two abstract states can be equivalent, without it being obvious that they can
actually both be executed assuming one can be executed.  One will therefore have
to add a few more assumptions to makes it possible to execute the other.

It currently assumes that all the predicates in the predicate tree are
evaluable, which is actually something that can either be checked, or something
that can be proven constructively.  I believe that it should already be possible
using the latter, so here it will only be assumed.

Similarly, the current assumption is that mutual exclusivity of predicates is
being checked within the ``check`` function, which could possibly also be proven
constructively about the update function.  This is a simpler short-term fix
though.
|*)

End CORRECT.
