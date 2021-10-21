Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Sat.

Definition predicate : Type := positive.

Inductive pred_op : Type :=
| Pvar: (bool * predicate) -> pred_op
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
  | Pvar (b, p') => if b then a (Pos.to_nat p') else negb (a (Pos.to_nat p'))
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
     | Pvar (b, p') => exist _ (((b, Pos.to_nat p') :: nil) :: nil) _
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
  | Pvar (b, pr) => Pvar (negb b, pr)
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
