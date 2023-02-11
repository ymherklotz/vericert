Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.SetoidDec.
Require Import Coq.Logic.Decidable.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Sat.
Require Import HashTree.

Declare Scope pred_op.

Section PRED_DEFINITION.

  Context {A: Type}.

  Definition predicate := A.

  Inductive pred_op : Type :=
  | Plit: (bool * predicate) -> pred_op
  | Ptrue: pred_op
  | Pfalse: pred_op
  | Pand: pred_op -> pred_op -> pred_op
  | Por: pred_op -> pred_op -> pred_op.

  Fixpoint negate (p: pred_op) :=
    match p with
    | Plit (b, pr) => Plit (negb b, pr)
    | Ptrue => Pfalse
    | Pfalse => Ptrue
    | Pand A B => Por (negate A) (negate B)
    | Por A B => Pand (negate A) (negate B)
    end.

  Definition Pimplies (p: pred_op) p' := Por (negate p) p'.

  Fixpoint predicate_use (p: pred_op) : list predicate :=
    match p with
    | Plit (b, p) => p :: nil
    | Ptrue => nil
    | Pfalse => nil
    | Pand a b => predicate_use a ++ predicate_use b
    | Por a b => predicate_use a ++ predicate_use b
    end.

  Definition combine_pred (p1 p2: option pred_op): option pred_op :=
    match p1, p2 with
    | Some p1, Some p2 => Some (Pand p1 p2)
    | Some p, _ | _, Some p => Some p
    | None, None => None
    end.

  Definition simplify' (p: pred_op) :=
    match p with
    (* | (Plit (b1, a)) ∧ (Plit (b2, b)) as p' => *)
    (*     if Pos.eqb a b then *)
    (*       if negb (xorb b1 b2) then Plit (b1, a) else ⟂ *)
    (*     else p' *)
    (* | (Plit (b1, a)) ∨ (Plit (b2, b)) as p' => *)
    (*     if Pos.eqb a b then *)
    (*       if negb (xorb b1 b2) then Plit (b1, a) else T *)
    (*     else p' *)
    | Pand A Ptrue => A
    | Pand Ptrue A => A
    | Pand _ Pfalse => Pfalse
    | Pand Pfalse _ => Pfalse
    | Por _ Ptrue => Ptrue
    | Por Ptrue _ => Ptrue
    | Por A Pfalse => A
    | Por Pfalse A => A
    | A => A
    end.

  Fixpoint simplify (p: pred_op) :=
    match p with
    | Pand A B =>
        let A' := simplify A in
        let B' := simplify B in
        simplify' (Pand A' B')
    | Por A B =>
        let A' := simplify A in
        let B' := simplify B in
        simplify' (Por A' B')
    | Ptrue => Ptrue
    | Pfalse => Pfalse
    | Plit a => Plit a
    end.

  Section DEEP_SIMPLIFY.

    Context (eqd: forall a b: A, {a = b} + {a <> b}).

    Definition deep_simplify' (p: pred_op) :=
      match p with
      | Pand A Ptrue => A
      | Pand Ptrue A => A
      | Pand _ Pfalse => Pfalse
      | Pand Pfalse _ => Pfalse
      | Por _ Ptrue => Ptrue
      | Por Ptrue _ => Ptrue
      | Por A Pfalse => A
      | Por Pfalse A => A

      | Pand (Plit (b1, a)) (Plit (b2, b)) =>
          if eqd a b then
            if bool_eqdec b1 b2 then
              Plit (b1, a)
            else Pfalse
          else Pand (Plit (b1, a)) (Plit (b2, b))
      | Por (Plit (b1, a)) (Plit (b2, b)) =>
          if eqd a b then
            if bool_eqdec b1 b2 then
              Plit (b1, a)
            else Ptrue
          else Por (Plit (b1, a)) (Plit (b2, b))

      | A => A
      end.

    Fixpoint deep_simplify (p: pred_op) :=
      match p with
      | Pand A B =>
          let A' := deep_simplify A in
          let B' := deep_simplify B in
          deep_simplify' (Pand A' B')
      | Por A B =>
          let A' := deep_simplify A in
          let B' := deep_simplify B in
          deep_simplify' (Por A' B')
      | Ptrue => Ptrue
      | Pfalse => Pfalse
      | Plit a => Plit a
      end.

    Fixpoint predin (a: predicate) (p: pred_op): bool :=
      match p with
      | Ptrue | Pfalse => false
      | Pand p1 p2 | Por p1 p2 => predin a p1 || predin a p2
      | Plit (_, a') => eqd a a'
      end.

  End DEEP_SIMPLIFY.

End PRED_DEFINITION.

Notation "A ∧ B" := (Pand A B) (at level 20) : pred_op.
Notation "A ∨ B" := (Por A B) (at level 25) : pred_op.
Notation "⟂" := (Pfalse) : pred_op.
Notation "'T'" := (Ptrue) : pred_op.
Notation "¬ A" := (negate A) (at level 15) : pred_op.
Notation "A → B" := (Pimplies A B) (at level 30) : pred_op.

#[local] Open Scope pred_op.

Fixpoint sat_predicate (p: pred_op) (a: asgn) : bool :=
  match p with
  | Plit (b, p') => if b then a (Pos.to_nat p') else negb (a (Pos.to_nat p'))
  | Ptrue => true
  | Pfalse => false
  | Pand p1 p2 => sat_predicate p1 a && sat_predicate p2 a
  | Por p1 p2 => sat_predicate p1 a || sat_predicate p2 a
  end.

Inductive sat_predicateP (a: asgn): pred_op -> bool -> Prop :=
| sat_prediacteP_Plit: forall b p',
  sat_predicateP a (Plit (b, p')) (if b then a (Pos.to_nat p') else negb (a (Pos.to_nat p')))
| sat_prediacteP_Ptrue:
  sat_predicateP a Ptrue true
| sat_prediacteP_Pfalse:
  sat_predicateP a Pfalse false
| sat_predicateP_Por_true1: forall p1 p2,
  sat_predicateP a p1 true ->
  sat_predicateP a (Por p1 p2) true
| sat_predicateP_Por_true2: forall p1 p2,
  sat_predicateP a p2 true ->
  sat_predicateP a (Por p1 p2) true
| sat_predicateP_Por_false: forall p1 p2,
  sat_predicateP a p1 false ->
  sat_predicateP a p2 false ->
  sat_predicateP a (Por p1 p2) false
| sat_predicateP_Pand_false1: forall p1 p2,
  sat_predicateP a p1 false ->
  sat_predicateP a (Pand p1 p2) false
| sat_predicateP_Pand_false2: forall p1 p2,
  sat_predicateP a p2 false ->
  sat_predicateP a (Pand p1 p2) false
| sat_predicateP_Pand_true: forall p1 p2,
  sat_predicateP a p1 true ->
  sat_predicateP a p2 true ->
  sat_predicateP a (Pand p1 p2) true.

Lemma sat_pred_equiv_sat_predicateP:
  forall a p, sat_predicateP a p (sat_predicate p a).
Proof.
  induction p; crush.
  - destruct_match. constructor.
  - constructor.
  - constructor.
  - destruct (sat_predicate p1 a) eqn:?. cbn.
    destruct (sat_predicate p2 a) eqn:?. cbn.
    all: solve [constructor; auto].
  - destruct (sat_predicate p1 a) eqn:?. cbn. solve [constructor; auto].
    destruct (sat_predicate p2 a) eqn:?. cbn.
    all: solve [constructor; auto].
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

Lemma negate_correct :
  forall (h: @pred_op positive) a, sat_predicate (negate h) a = negb (sat_predicate h a).
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

Lemma pred_op_dec :
  forall p1 p2: @pred_op positive,
    { p1 = p2 } + { p1 <> p2 }.
Proof. pose proof Pos.eq_dec. repeat decide equality. Qed.

Lemma simplify'_correct :
  forall h a,
    sat_predicate (simplify' h) a = sat_predicate h a.
Proof.
(*destruct h; crush; repeat destruct_match; crush;
  solve [rewrite andb_true_r; auto | rewrite orb_false_r; auto].
Qed.*) Admitted.

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

Definition bar (p1: lit): lit := (negb (fst p1), (snd p1)).

Definition stseytin_or (cur p1 p2: lit) : formula :=
  (bar cur :: p1 :: p2 :: nil)
    :: (cur :: bar p1 :: nil)
    :: (cur :: bar p2 :: nil) :: nil.

Definition stseytin_and (cur p1 p2: lit) : formula :=
  (cur :: bar p1 :: bar p2 :: nil)
    :: (bar cur :: p1 :: nil)
    :: (bar cur :: p2 :: nil) :: nil.

Fixpoint xtseytin (next: nat) (p: pred_op) {struct p} : (nat * lit * formula) :=
  match p with
  | Plit (b, p') => (next, (b, Pos.to_nat p'), nil)
  | Ptrue =>
      ((next+1)%nat, (true, next), ((true, next)::nil)::nil)
  | Pfalse =>
      ((next+1)%nat, (true, next), ((false, next)::nil)::nil)
  | Por p1 p2 =>
      let '(m1, n1, f1) := xtseytin next p1 in
      let '(m2, n2, f2) := xtseytin m1 p2 in
      ((m2+1)%nat, (true, m2), stseytin_or (true, m2) n1 n2 ++ f1 ++ f2)
  | Pand p1 p2 =>
      let '(m1, n1, f1) := xtseytin next p1 in
      let '(m2, n2, f2) := xtseytin m1 p2 in
      ((m2+1)%nat, (true, m2), stseytin_and (true, m2) n1 n2 ++ f1 ++ f2)
  end.

Lemma stseytin_and_correct :
  forall cur p1 p2 fm c,
    stseytin_and cur p1 p2 = fm ->
    satLit cur c ->
    satLit p1 c /\ satLit p2 c ->
    satFormula fm c.
Proof.
  intros.
  unfold stseytin_and in *. rewrite <- H.
  unfold satLit in *. destruct p1. destruct p2. destruct cur.
  simpl in *|-. cbn. unfold satLit. cbn. crush.
Qed.

Lemma stseytin_and_correct2 :
  forall cur p1 p2 fm c,
    stseytin_and cur p1 p2 = fm ->
    satFormula fm c ->
    satLit cur c <-> satLit p1 c /\ satLit p2 c.
Proof.
  intros. split. intros. inv H1. unfold stseytin_and in *.
  inv H0; try contradiction. Admitted.

Lemma stseytin_or_correct :
  forall cur p1 p2 fm c,
    stseytin_or cur p1 p2 = fm ->
    satLit cur c ->
    satLit p1 c \/ satLit p2 c ->
    satFormula fm c.
Proof.
  intros.
  unfold stseytin_or in *. rewrite <- H. inv H1.
  unfold satLit in *. destruct p1. destruct p2. destruct cur.
  simpl in *|-. cbn. unfold satLit. cbn. crush.
  unfold satLit in *. destruct p1. destruct p2. destruct cur.
  simpl in *|-. cbn. unfold satLit. cbn. crush.
Qed.

Lemma stseytin_or_correct2 :
  forall cur p1 p2 fm c,
    stseytin_or cur p1 p2 = fm ->
    satFormula fm c ->
    satLit cur c <-> satLit p1 c \/ satLit p2 c.
Proof. Admitted.

Lemma xtseytin_correct :
  forall p next l n fm c,
    xtseytin next p = (n, l, fm) ->
    sat_predicate p c = true <-> satFormula ((l::nil)::fm) c.
Proof.
  induction p.
  - intros. simplify. destruct p.
    inv H. split.
    intros. destruct b. split; crush.
    apply negb_true_iff in H.
    split; crush.
    intros. inv H. inv H0; try contradiction.
    inv H. simplify. rewrite <- H0.
    destruct b.
    rewrite -> H0; auto.
    rewrite -> H0; auto.
  - admit.
  - admit.
  - intros. split. intros. simpl in H0.
    apply andb_prop in H0. inv H0.
    cbn in H.
    repeat destruct_match; try discriminate; []. inv H. eapply IHp1 in Heqp.
    eapply IHp2 in Heqp1. apply Heqp1 in H2.
    apply Heqp in H1. inv H1. inv H2.
    assert
      (satFormula
         (((true, n1) :: bar l0 :: bar l1 :: nil)
            :: (bar (true, n1) :: l0 :: nil)
            :: (bar (true, n1) :: l1 :: nil) :: nil) c).
    eapply stseytin_and_correct. unfold stseytin_and. eauto.
    unfold satLit. simpl. admit.
    inv H; try contradiction. inv H1; try contradiction. eauto.
Admitted.

Fixpoint max_predicate (p: pred_op) : positive :=
  match p with
  | Plit (b, p) => p
  | Ptrue => 1
  | Pfalse => 1
  | Pand a b => Pos.max (max_predicate a) (max_predicate b)
  | Por a b => Pos.max (max_predicate a) (max_predicate b)
  end.

Definition tseytin (p: pred_op) :
  {fm: formula | forall a,
      sat_predicate p a = true <-> satFormula fm a}.
  refine (
      (match xtseytin (Pos.to_nat (max_predicate p + 1)) p as X
             return xtseytin (Pos.to_nat (max_predicate p + 1)) p = X ->
                    {fm: formula | forall a, sat_predicate p a = true <-> satFormula fm a}
       with (m, n, fm) => fun H => exist _ ((n::nil) :: fm) _
       end) (eq_refl (xtseytin (Pos.to_nat (max_predicate p + 1)) p))).
  intros. eapply xtseytin_correct; eauto. Defined.

Definition tseytin_simple (p: pred_op) : formula :=
  let m := Pos.to_nat (max_predicate p + 1) in
  let '(m, n, fm) := xtseytin m p in
  (n::nil) :: fm.

Definition sat_pred_tseytin (p: pred_op) :
  ({al : alist | sat_predicate p (interp_alist al) = true}
   + {forall a : asgn, sat_predicate p a = false}).
  refine
    ( match tseytin p with
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

Definition sat_pred_simple (p: pred_op) : option alist :=
  match sat_pred_tseytin p with
  | inleft (exist _ a _) => Some a
  | inright _ => None
  end.

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

#[local] Open Scope positive.

(* Compute tseytin_simple (Por (negate (Pand (Por (Plit (true, 1)) (Plit (true, 2))) (Plit (true, 3)))) (Plit (false, 4))). *)
(* Compute sat_pred_simple (Por Pfalse (Pand (Plit (true, 1)) (Plit (false, 1)))). *)

Lemma sat_dec a: {sat a} + {unsat a}.
Proof.
  unfold sat, unsat.
  destruct (sat_pred a).
  intros. left. destruct s.
  exists (Sat.interp_alist x). auto.
  intros. tauto.
Qed.

Definition equiv_check p1 p2 :=
  match sat_pred_simple (simplify (p1 ∧ ¬ p2 ∨ p2 ∧ ¬ p1)) with
  | None => true
  | _ => false
  end.

(* Compute equiv_check Pfalse (Pand (Plit (true, 1%positive)) (Plit (false, 1%positive))). *)

Lemma equiv_check_correct :
  forall p1 p2, equiv_check p1 p2 = true -> p1 == p2.
Proof.
  unfold equiv_check. unfold sat_pred_simple. intros.
  destruct_match; try discriminate; [].
  destruct_match. destruct_match. discriminate.
  eapply sat_equiv3; eauto.
  unfold unsat; intros.
  rewrite <- simplify_correct. eauto.
Qed.

Opaque simplify.
Opaque simplify'.

Lemma equiv_check_correct2 :
  forall p1 p2, p1 == p2 -> equiv_check p1 p2 = true.
Proof.
  unfold equiv_check, equiv, sat_pred_simple. intros.
  destruct_match; auto. destruct_match; try discriminate.
  destruct_match.
  simplify.
  apply sat_equiv4 in H. unfold unsat in H. simplify.
  clear Heqs. rewrite simplify_correct in e.
  specialize (H (interp_alist a)). simplify.
  rewrite H1 in e. rewrite H0 in e. discriminate.
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

#[global]
 Instance simplifyProper : Proper (equiv ==> equiv) simplify.
Proof.
  unfold Proper, "==>". simplify. unfold "→".
  intros. unfold sat_equiv; intros.
  rewrite ! simplify_correct; auto.
Qed.

Lemma predicate_lt :
  forall p p0,
    In p0 (predicate_use p) -> p0 <= max_predicate p.
Proof.
  induction p; crush.
  - destruct_match. inv H; try lia; contradiction.
  - eapply Pos.max_le_iff.
    eapply in_app_or in H. inv H; eauto.
  - eapply Pos.max_le_iff.
    eapply in_app_or in H. inv H; eauto.
Qed.
