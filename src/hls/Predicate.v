Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.SetoidDec.
Require Import Coq.Logic.Decidable.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Sat.

Definition predicate : Type := positive.

Inductive pred_op : Type :=
| Plit: (bool * predicate) -> pred_op
| Ptrue: pred_op
| Pfalse: pred_op
| Pand: pred_op -> pred_op -> pred_op
| Por: pred_op -> pred_op -> pred_op.

Declare Scope pred_op.

Notation "A ∧ B" := (Pand A B) (at level 20) : pred_op.
Notation "A ∨ B" := (Por A B) (at level 25) : pred_op.
Notation "⟂" := (Pfalse) : pred_op.
Notation "'T'" := (Ptrue) : pred_op.

Fixpoint sat_predicate (p: pred_op) (a: asgn) : bool :=
  match p with
  | Plit (b, p') => if b then a (Pos.to_nat p') else negb (a (Pos.to_nat p'))
  | Ptrue => true
  | Pfalse => false
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

Fixpoint trans_pred (p: pred_op) :
  {fm: formula | forall a,
      sat_predicate p a = true <-> satFormula fm a}.
  refine
  (match p with
     | Plit (b, p') => exist _ (((b, Pos.to_nat p') :: nil) :: nil) _
     | Ptrue => exist _ nil _
     | Pfalse => exist _ (nil::nil) _
     | Pand p1 p2 =>
      match trans_pred p1, trans_pred p2 with
      | exist _ p1' _, exist _ p2' _ => exist _ (p1' ++ p2') _
      end
     | Por p1 p2 =>
      match trans_pred p1, trans_pred p2 with
      | exist _ p1' _, exist _ p2' _ => exist _ (mult p1' p2') _
      end
   end); split; intros; simpl in *; auto; try solve [crush].
  - destruct b; auto. apply negb_true_iff in H. auto.
  - destruct b. inv H. inv H0; auto. apply negb_true_iff. inv H. inv H0; eauto. contradiction.
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

Definition sat_pred (p: pred_op) :
  ({al : alist | sat_predicate p (interp_alist al) = true}
   + {forall a : asgn, sat_predicate p a = false}).
  refine
  ( match trans_pred p with
    | exist _ fm _ =>
      match satSolve fm with
      | inleft (exist _ a _) => inleft (exist _ a _)
      | inright _ => inright _
      end
    end ).
  - apply i in s0. auto.
  - intros. specialize (n a). specialize (i a).
    destruct (sat_predicate p a). exfalso.
    apply n. apply i. auto. auto.
Defined.

Definition sat_pred_simple (p: pred_op) :=
  match sat_pred p with
  | inleft (exist _ al _) => Some al
  | inright _ => None
  end.

#[local] Open Scope pred_op.

Fixpoint negate (p: pred_op) :=
  match p with
  | Plit (b, pr) => Plit (negb b, pr)
  | T => ⟂
  | ⟂ => T
  | A ∧ B => negate A ∨ negate B
  | A ∨ B => negate A ∧ negate B
  end.

Notation "¬ A" := (negate A) (at level 15) : pred_op.

Lemma negate_correct :
  forall h a, sat_predicate (negate h) a = negb (sat_predicate h a).
Proof.
  induction h; crush.
  - repeat destruct_match; subst; crush; symmetry; apply negb_involutive.
  - rewrite negb_andb; crush.
  - rewrite negb_orb; crush.
Qed.

Definition unsat p := forall a, sat_predicate p a = false.
Definition sat p := exists a, sat_predicate p a = true.

Lemma unsat_correct1 :
  forall a b c,
    unsat (Pand a b) ->
    sat_predicate a c = true ->
    sat_predicate b c = false.
Proof.
  unfold unsat in *. intros.
  simplify. specialize (H c).
  apply andb_false_iff in H. inv H. rewrite H0 in H1. discriminate.
  auto.
Qed.

Lemma unsat_correct2 :
  forall a b c,
    unsat (Pand a b) ->
    sat_predicate b c = true ->
    sat_predicate a c = false.
Proof.
  unfold unsat in *. intros.
  simplify. specialize (H c).
  apply andb_false_iff in H. inv H. auto. rewrite H0 in H1. discriminate.
Qed.

Lemma unsat_not a: unsat (a ∧ (¬ a)).
Proof.
  unfold unsat; simplify.
  rewrite negate_correct.
  auto with bool.
Qed.

Lemma unsat_commut a b: unsat (a ∧ b) -> unsat (b ∧ a).
Proof. unfold unsat; simplify; eauto with bool. Qed.

Lemma sat_dec a: {sat a} + {unsat a}.
Proof.
  unfold sat, unsat.
  destruct (sat_pred a).
  intros. left. destruct s.
  exists (Sat.interp_alist x). auto.
  intros. tauto.
Qed.

Definition sat_equiv p1 p2 := forall c, sat_predicate p1 c = sat_predicate p2 c.

Lemma equiv_symm : forall a b, sat_equiv a b -> sat_equiv b a.
Proof. crush. Qed.

Lemma equiv_trans : forall a b c, sat_equiv a b -> sat_equiv b c -> sat_equiv a c.
Proof. crush. Qed.

Lemma equiv_refl : forall a, sat_equiv a a.
Proof. crush. Qed.

#[global]
Instance Equivalence_SAT : Equivalence sat_equiv :=
  { Equivalence_Reflexive := equiv_refl ;
    Equivalence_Symmetric := equiv_symm ;
    Equivalence_Transitive := equiv_trans ;
  }.

#[global]
Instance SATSetoid : Setoid pred_op :=
  { equiv := sat_equiv; }.

#[global]
Instance PandProper : Proper (equiv ==> equiv ==> equiv) Pand.
Proof.
  unfold Proper. simplify. unfold "==>".
  intros.
  unfold sat_equiv in *. intros.
  simplify. rewrite H0. rewrite H.
  auto.
Qed.

#[global]
Instance PorProper : Proper (equiv ==> equiv ==> equiv) Por.
Proof.
  unfold Proper, "==>". simplify.
  intros.
  unfold sat_equiv in *. intros.
  simplify. rewrite H0. rewrite H.
  auto.
Qed.

#[global]
Instance sat_predicate_Proper : Proper (equiv ==> eq ==> eq) sat_predicate.
Proof.
  unfold Proper, "==>". simplify.
  intros.
  unfold sat_equiv in *. subst.
  apply H.
Qed.

Lemma sat_imp_equiv :
  forall a b,
    unsat (a ∧ ¬ b ∨ ¬ a ∧ b) -> a == b.
Proof.
  simplify; unfold unsat, sat_equiv.
  intros. specialize (H c); simplify.
  rewrite negate_correct in *.
  destruct (sat_predicate b c) eqn:X;
  destruct (sat_predicate a c) eqn:X2;
  crush.
Qed.

Lemma sat_predicate_and :
  forall a b c,
    sat_predicate (a ∧ b) c = sat_predicate a c && sat_predicate b c.
Proof. crush. Qed.

Lemma sat_predicate_or :
  forall a b c,
    sat_predicate (a ∨ b) c = sat_predicate a c || sat_predicate b c.
Proof. crush. Qed.

Lemma sat_equiv2 :
  forall a b,
    a == b -> unsat (a ∧ ¬ b ∨ ¬ a ∧ b).
Proof.
  unfold unsat, equiv; simplify.
  repeat rewrite negate_correct.
  repeat rewrite H.
  rewrite andb_negb_r.
  rewrite andb_negb_l. auto.
Qed.

Lemma sat_equiv3 :
  forall a b,
    unsat (a ∧ ¬ b ∨ b ∧ ¬ a) -> a == b.
Proof.
  simplify. unfold unsat, sat_equiv in *; intros.
  specialize (H c); simplify.
  rewrite negate_correct in *.
  destruct (sat_predicate b c) eqn:X;
  destruct (sat_predicate a c) eqn:X2;
  crush.
Qed.

Lemma sat_equiv4 :
  forall a b,
    a == b -> unsat (a ∧ ¬ b ∨ b ∧ ¬ a).
Proof.
  unfold unsat, equiv; simplify.
  repeat rewrite negate_correct.
  repeat rewrite H.
  rewrite andb_negb_r. auto.
Qed.

Definition equiv_check p1 p2 :=
  match sat_pred_simple (p1 ∧ ¬ p2 ∨ p2 ∧ ¬ p1) with
  | None => true
  | _ => false
  end.

Lemma equiv_check_correct :
  forall p1 p2, equiv_check p1 p2 = true -> p1 == p2.
Proof.
  unfold equiv_check. unfold sat_pred_simple. intros.
  destruct_match; try discriminate; [].
  destruct_match. destruct_match. discriminate.
  eapply sat_equiv3; eauto.
Qed.

Lemma equiv_check_correct2 :
  forall p1 p2, p1 == p2 -> equiv_check p1 p2 = true.
Proof.
  unfold equiv_check, equiv, sat_pred_simple. intros.
  destruct_match; auto. destruct_match; try discriminate. destruct_match.
  simplify.
  apply sat_equiv4 in H. unfold unsat in H. simplify.
  clear Heqs. rewrite H in e. discriminate.
Qed.

Lemma equiv_check_dec :
  forall p1 p2, equiv_check p1 p2 = true <-> p1 == p2.
Proof.
  intros; split; eauto using equiv_check_correct, equiv_check_correct2.
Qed.

Lemma equiv_check_decidable :
  forall p1 p2, decidable (p1 == p2).
Proof.
  intros. destruct (equiv_check p1 p2) eqn:?.
  unfold decidable.
  left. apply equiv_check_dec; auto.
  unfold decidable, not; right; intros.
  apply equiv_check_dec in H. crush.
Qed.

Lemma equiv_check_decidable2 :
  forall p1 p2, {p1 == p2} + {p1 =/= p2}.
Proof.
  intros. destruct (equiv_check p1 p2) eqn:?.
  unfold decidable.
  left. apply equiv_check_dec; auto.
  unfold decidable, not; right; intros.
  simpl. unfold complement. intros.
  apply not_true_iff_false in Heqb. apply Heqb.
  apply equiv_check_dec. eauto.
Qed.

#[global]
Instance DecidableSATSetoid : DecidableSetoid SATSetoid :=
  { setoid_decidable := equiv_check_decidable }.

#[global]
Instance SATSetoidEqDec : EqDec SATSetoid := equiv_check_decidable2.

Definition Pimplies p p' := ¬ p ∨ p'.

Notation "A → B" := (Pimplies A B) (at level 30) : pred_op.

Definition implies p p' :=
  forall c, sat_predicate p c = true -> sat_predicate p' c = true.

Notation "A ⇒ B" := (implies A B) (at level 35) : pred_op.

Lemma Pimplies_implies: forall p p', (p → p') ∧ p ⇒ p'.
Proof.
  unfold "→", "⇒"; simplify.
  apply orb_prop in H0. inv H0; auto. rewrite negate_correct in H.
  apply negb_true_iff in H. crush.
Qed.

#[global]
Instance PimpliesProper : Proper (equiv ==> equiv ==> equiv) Pimplies.
Proof.
  unfold Proper, "==>". simplify. unfold "→".
  intros.
  unfold sat_equiv in *. intros.
  simplify. repeat rewrite negate_correct. rewrite H0. rewrite H.
  auto.
Qed.

Definition simplify' (p: pred_op) :=
  match p with
  | A ∧ T => A
  | T ∧ A => A
  | _ ∧ ⟂ => ⟂
  | ⟂ ∧ _ => ⟂
  | _ ∨ T => T
  | T ∨ _ => T
  | A ∨ ⟂ => A
  | ⟂ ∨ A => A
  | A => A
  end.

Lemma pred_op_dec :
  forall p1 p2: pred_op,
  { p1 = p2 } + { p1 <> p2 }.
Proof. pose proof Pos.eq_dec. repeat decide equality. Qed.

Fixpoint simplify (p: pred_op) :=
  match p with
  | A ∧ B =>
    let A' := simplify A in
    let B' := simplify B in
    simplify' (A' ∧ B')
  | A ∨ B =>
    let A' := simplify A in
    let B' := simplify B in
    simplify' (A' ∨ B')
  | T => T
  | ⟂ => ⟂
  | Plit a => Plit a
  end.

Lemma simplify'_correct :
  forall h a,
    sat_predicate (simplify' h) a = sat_predicate h a.
Proof.
  destruct h; crush; repeat destruct_match; crush;
  solve [rewrite andb_true_r; auto | rewrite orb_false_r; auto].
Qed.

Lemma simplify_correct :
  forall h a,
    sat_predicate (simplify h) a = sat_predicate h a.
Proof.
  Local Opaque simplify'.
  induction h; crush.
  - replace (sat_predicate h1 a && sat_predicate h2 a)
      with (sat_predicate (simplify h1) a && sat_predicate (simplify h2) a)
      by crush.
    rewrite simplify'_correct. crush.
  - replace (sat_predicate h1 a || sat_predicate h2 a)
      with (sat_predicate (simplify h1) a || sat_predicate (simplify h2) a)
      by crush.
    rewrite simplify'_correct. crush.
    Local Transparent simplify'.
Qed.
