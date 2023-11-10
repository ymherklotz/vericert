Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.SetoidDec.
Require Import Coq.Logic.Decidable.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Sat.
Require Import vericert.hls.HashTree.

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

  Inductive PredIn (a: predicate): pred_op -> Prop :=
  | PredIn_Plit: forall b, PredIn a (Plit (b, a))
  | PredIn_Pand: forall p1 p2,
    PredIn a p1 \/ PredIn a p2 ->
    PredIn a (Pand p1 p2)
  | PredIn_Por: forall p1 p2,
    PredIn a p1 \/ PredIn a p2 ->
    PredIn a (Por p1 p2).

  Section DEEP_SIMPLIFY.

    Context (eqd: forall a b: A, {a = b} + {a <> b}).

    Definition eq_dec: forall a b: pred_op,
      {a = b} + {a <> b}.
    Proof.
      pose proof bool_eq_dec.
      assert (forall a b: bool * predicate, {a = b} + {a <> b})
        by decide equality.
      induction a; destruct b; decide equality.
    Defined.

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

      | Pand A B =>
        if eq_dec A B then A
        else Pand A B

      | Por A B =>
        if eq_dec A B then A
        else Por A B

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

    Lemma predin_PredIn:
      forall a p, PredIn a p <-> predin a p = true.
    Proof.
      induction p; split; try solve [inversion 1 | discriminate].
      - cbn. destruct p. inversion 1; subst. destruct eqd; auto.
      - intros. cbn in *. destruct p. destruct eqd. subst. constructor. discriminate.
      - inversion 1. apply orb_true_intro. tauto.
      - intros. cbn in *. constructor. apply orb_prop in H. tauto.
      - inversion 1. apply orb_true_intro. tauto.
      - intros. cbn in *. apply orb_prop in H. constructor. tauto.
    Qed.

  End DEEP_SIMPLIFY.

End PRED_DEFINITION.

Definition dfltp {A} (p: option (@Predicate.pred_op A)) := Option.default Ptrue p.

Notation "A ∧ B" := (Pand A B) (at level 20) : pred_op.
Notation "A ∨ B" := (Por A B) (at level 25) : pred_op.
Notation "⟂" := (Pfalse) : pred_op.
Notation "'T'" := (Ptrue) : pred_op.
Notation "¬ A" := (negate A) (at level 15) : pred_op.
Notation "A → B" := (Pimplies A B) (at level 30) : pred_op.

#[local] Open Scope pred_op.

Fixpoint sat_predicate (p: pred_op) (a: asgn) : bool :=
  match p with
  | Plit (b, p') => if b then a p' else negb (a p')
  | Ptrue => true
  | Pfalse => false
  | Pand p1 p2 => sat_predicate p1 a && sat_predicate p2 a
  | Por p1 p2 => sat_predicate p1 a || sat_predicate p2 a
  end.

Inductive sat_predicateP (a: asgn): pred_op -> bool -> Prop :=
| sat_prediacteP_Plit: forall b p',
  sat_predicateP a (Plit (b, p')) (if b then a p' else negb (a p'))
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
  destruct h; crush; repeat destruct_match; crush;
  solve [rewrite andb_true_r; auto | rewrite orb_false_r; auto].
Qed.

Local Opaque simplify'.
Lemma simplify_correct :
  forall h a,
    sat_predicate (simplify h) a = sat_predicate h a.
Proof.
  induction h; crush.
  - replace (sat_predicate h1 a && sat_predicate h2 a)
      with (sat_predicate (simplify h1) a && sat_predicate (simplify h2) a)
      by crush.
    rewrite simplify'_correct. crush.
  - replace (sat_predicate h1 a || sat_predicate h2 a)
      with (sat_predicate (simplify h1) a || sat_predicate (simplify h2) a)
      by crush.
    rewrite simplify'_correct. crush.
Qed.
Local Transparent simplify'.

Lemma Plit_inj :
  forall A (a b: bool * A), Plit a = Plit b -> a = b.
Proof. now inversion 1. Qed.

Lemma deep_simplify'_correct :
  forall peq h a,
    sat_predicate (deep_simplify' peq h) a = sat_predicate h a.
Proof.
  destruct h; auto; cbn in *;
    destruct h1; destruct h2; intuition auto with *; destruct_match; auto;
    clear Heqs; inv e; solve [now rewrite andb_diag | now rewrite orb_diag].
Qed.

Lemma deep_simplify_correct :
  forall peq h a,
    sat_predicate (deep_simplify peq h) a = sat_predicate h a.
Proof.
  induction h; auto;
    intros; cbn -[deep_simplify']; rewrite deep_simplify'_correct;
    cbn; rewrite IHh1; now rewrite IHh2.
Qed.

Fixpoint mult {A: Type} (a b: list (list A)) : list (list A) :=
  match a with
  | nil => nil
  | l :: ls => mult ls b ++ (List.map (fun x => l ++ x) b)
  end.

Lemma sat_formula_concat:
  forall a b agn,
    sat_formula a agn ->
    sat_formula b agn ->
    sat_formula (a ++ b) agn.
Proof. induction a; crush. Qed.

Lemma sat_formula_concat2:
  forall a b agn,
    sat_formula (a ++ b) agn ->
    sat_formula a agn /\ sat_formula b agn.
Proof.
  induction a; simplify;
    try apply IHa in H1; crush.
Qed.

Lemma sat_clause_concat:
  forall a a1 a0,
    sat_clause a a1 ->
    sat_clause (a0 ++ a) a1.
Proof. induction a0; crush. Qed.

Lemma sat_clause_concat2:
  forall a a1 a0,
    sat_clause a0 a1 ->
    sat_clause (a0 ++ a) a1.
Proof.
  induction a0; crush.
  inv H; crush.
Qed.

Lemma sat_clause_concat3:
  forall a b c,
    sat_clause (a ++ b) c ->
    sat_clause a c \/ sat_clause b c.
Proof.
  induction a; crush.
  inv H; crush.
  apply IHa in H0; crush.
  inv H0; crush.
Qed.

Lemma sat_formula_mult':
  forall p2 a a0,
    sat_formula p2 a0 \/ sat_clause a a0 ->
    sat_formula (map (fun x : list lit => a ++ x) p2) a0.
Proof.
  induction p2; crush.
  - inv H. inv H0. apply sat_clause_concat. auto.
    apply sat_clause_concat2; auto.
  - apply IHp2.
    inv H; crush; inv H0; crush.
Qed.

Lemma sat_formula_mult2':
  forall p2 a a0,
    sat_formula (map (fun x : list lit => a ++ x) p2) a0 ->
    sat_clause a a0 \/ sat_formula p2 a0.
Proof.
  induction p2; crush.
  apply IHp2 in H1. inv H1; crush.
  apply sat_clause_concat3 in H0.
  inv H0; crush.
Qed.

Lemma sat_formula_mult:
  forall p1 p2 a,
    sat_formula p1 a \/ sat_formula p2 a ->
    sat_formula (mult p1 p2) a.
Proof.
  induction p1; crush.
  apply sat_formula_concat; crush.
  inv H. inv H0.
  apply IHp1. auto.
  apply IHp1. auto.
  apply sat_formula_mult';
    inv H; crush.
Qed.

Lemma sat_formula_mult2:
  forall p1 p2 a,
    sat_formula (mult p1 p2) a ->
    sat_formula p1 a \/ sat_formula p2 a.
Proof.
  induction p1; crush.
  apply sat_formula_concat2 in H; crush.
  apply IHp1 in H0.
  inv H0; crush.
  apply sat_formula_mult2' in H1. inv H1; crush.
Qed.

Fixpoint trans_pred (p: pred_op) :
  {fm: formula | forall a,
      sat_predicate p a = true <-> sat_formula fm a}.
  refine
    (match p with
     | Plit (b, p') => exist _ (((b, p') :: nil) :: nil) _
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
  - apply sat_formula_concat.
    apply andb_prop in H. inv H. apply i in H0. auto.
    apply andb_prop in H. inv H. apply i0 in H1. auto.
  - apply sat_formula_concat2 in H. simplify. apply andb_true_intro.
    split. apply i in H0. auto.
    apply i0 in H1. auto.
  - apply orb_prop in H. inv H; apply sat_formula_mult. apply i in H0. auto.
    apply i0 in H0. auto.
  - apply orb_true_intro.
    apply sat_formula_mult2 in H. inv H. apply i in H0. auto.
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

Fixpoint xtseytin (next: positive) (p: pred_op) {struct p} : (positive * lit * formula) :=
  match p with
  | Plit (b, p') => (next, (b, p'), nil)
  | Ptrue =>
      ((next+1)%positive, (true, next), ((true, next)::nil)::nil)
  | Pfalse =>
      ((next+1)%positive, (true, next), ((false, next)::nil)::nil)
  | Por p1 p2 =>
      let '(m1, n1, f1) := xtseytin next p1 in
      let '(m2, n2, f2) := xtseytin m1 p2 in
      ((m2+1)%positive, (true, m2), stseytin_or (true, m2) n1 n2 ++ f1 ++ f2)
  | Pand p1 p2 =>
      let '(m1, n1, f1) := xtseytin next p1 in
      let '(m2, n2, f2) := xtseytin m1 p2 in
      ((m2+1)%positive, (true, m2), stseytin_and (true, m2) n1 n2 ++ f1 ++ f2)
  end.

Lemma stseytin_and_correct :
  forall cur p1 p2 fm c,
    stseytin_and cur p1 p2 = fm ->
    sat_lit cur c ->
    sat_lit p1 c /\ sat_lit p2 c ->
    sat_formula fm c.
Proof.
  intros.
  unfold stseytin_and in *. rewrite <- H.
  unfold sat_lit in *. destruct p1. destruct p2. destruct cur.
  simpl in *|-. cbn. unfold sat_lit. cbn. crush.
Qed.

Lemma stseytin_and_correct2 :
  forall cur p1 p2 c,
    sat_formula (stseytin_and cur p1 p2) c ->
    sat_lit cur c <-> sat_lit p1 c /\ sat_lit p2 c.
Proof.
  intros. split; intros; unfold stseytin_and in *.
  - cbn in *. inv H. destruct cur. inv H0. inv H2. inv H3. clear H4.
    unfold bar in *; cbn in *. destruct p1. destruct p2. cbn in *.
    inv H2. unfold sat_lit in H3. cbn in H3. destruct (c v); cbn in *; discriminate.
    inv H3; try contradiction.
    inv H0. unfold sat_lit in H2. cbn in H2. destruct (c v); cbn in *; discriminate.
    inv H2; try contradiction. eauto.
  - cbn in *. inv H0. inv H. inv H0. auto. unfold bar in *. destruct p1, p2; cbn in *. 
    inv H.  inv H1. inv H0. cbn in *. rewrite H in H4. destruct b; discriminate.
    inv H0; try contradiction. inv H. inv H2. cbn in *. rewrite H in H4. destruct b0; discriminate.
Qed.

Lemma stseytin_and_correct3 :
  forall cur p1 p2 c,
    sat_lit cur c <-> sat_lit p1 c /\ sat_lit p2 c ->
    sat_formula (stseytin_and cur p1 p2) c.
Proof.
  intros. split; intros; unfold stseytin_and in *;
  assert (forall a b, a <> b -> a = negb b) by (destruct a, b; eauto with bool; try contradiction).
  - inv H. cbn. destruct cur, p1, p2; unfold sat_lit in *. cbn in *.
    destruct (bool_eq_dec (c v0) b0); subst;
    destruct (bool_eq_dec (c v1) b1); subst; firstorder.
  - cbn in *; split; [|split]; auto; inv H; unfold sat_lit in *; destruct cur, p1, p2; cbn in *;
    destruct (bool_eq_dec (c v) b); subst; try tauto.
    + destruct (bool_eq_dec (c v0) b0); subst; try tauto. firstorder.
    + destruct (bool_eq_dec (c v1) b1); subst; firstorder.
Qed.

Lemma stseytin_or_correct :
  forall cur p1 p2 fm c,
    stseytin_or cur p1 p2 = fm ->
    sat_lit cur c ->
    sat_lit p1 c \/ sat_lit p2 c ->
    sat_formula fm c.
Proof.
  intros.
  unfold stseytin_or in *. rewrite <- H. inv H1.
  unfold sat_lit in *. destruct p1. destruct p2. destruct cur.
  simpl in *|-. cbn. unfold sat_lit. cbn. crush.
  unfold sat_lit in *. destruct p1. destruct p2. destruct cur.
  simpl in *|-. cbn. unfold sat_lit. cbn. crush.
Qed.

Lemma stseytin_or_correct2 :
  forall cur p1 p2 fm c,
    stseytin_or cur p1 p2 = fm ->
    sat_formula fm c ->
    sat_lit cur c <-> sat_lit p1 c \/ sat_lit p2 c.
Proof. Abort.

Lemma xtseytin_correct :
  forall p next l n fm c,
    xtseytin next p = (n, l, fm) ->
    sat_predicate p c = true <-> sat_formula ((l::nil)::fm) c.
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
(*    eapply IHp2 in Heqp1. apply Heqp1 in H2.
    apply Heqp in H1. inv H1. inv H2.
    assert
      (sat_formula
         (((true, n1) :: bar l0 :: bar l1 :: nil)
            :: (bar (true, n1) :: l0 :: nil)
            :: (bar (true, n1) :: l1 :: nil) :: nil) c).
    eapply stseytin_and_correct. unfold stseytin_and. eauto.
    unfold sat_lit. simpl. admit.
    inv H; try contradiction. inv H1; try contradiction. eauto.*)
Abort.

Fixpoint max_predicate (p: pred_op) : positive :=
  match p with
  | Plit (b, p) => p
  | Ptrue => 1
  | Pfalse => 1
  | Pand a b => Pos.max (max_predicate a) (max_predicate b)
  | Por a b => Pos.max (max_predicate a) (max_predicate b)
  end.

  Lemma max_predicate_deep_simplify' :
    forall peq curr r,
      (r <= max_predicate (deep_simplify' peq curr))%positive ->
      (r <= max_predicate curr)%positive.
  Proof.
    destruct curr; cbn -[deep_simplify']; auto.
    - intros. unfold deep_simplify' in H.
      destruct curr1; destruct curr2; try (destruct_match; cbn in *); lia.
    - intros. unfold deep_simplify' in H.
      destruct curr1; destruct curr2; try (destruct_match; cbn in *); lia.
  Qed.

  Lemma max_predicate_deep_simplify :
    forall peq curr r,
      (r <= max_predicate (deep_simplify peq curr))%positive ->
      (r <= max_predicate curr)%positive.
  Proof.
    induction curr; try solve [cbn; auto]; cbn -[deep_simplify'] in *.
    - intros. apply max_predicate_deep_simplify' in H. cbn -[deep_simplify'] in *.
      assert (HX: (r <= max_predicate (deep_simplify peq curr1))%positive \/ (r <= max_predicate (deep_simplify peq curr2))%positive) by lia.
      inv HX; [eapply IHcurr1 in H0 | eapply IHcurr2 in H0]; lia.
    - intros. apply max_predicate_deep_simplify' in H. cbn -[deep_simplify'] in *.
      assert (HX: (r <= max_predicate (deep_simplify peq curr1))%positive \/ (r <= max_predicate (deep_simplify peq curr2))%positive) by lia.
      inv HX; [eapply IHcurr1 in H0 | eapply IHcurr2 in H0]; lia.
  Qed.

  Lemma max_predicate_negate : 
    forall p, max_predicate (negate p) = max_predicate p.
  Proof.
    induction p; intuition; cbn; rewrite IHp1; now rewrite IHp2.
  Qed.

Lemma xtseytin_gt:
  forall p next n l fm,
    xtseytin next p = (n, l, fm) ->
    (next <= n)%positive.
Proof.
  induction p; cbn; intros; try lia.
  - destruct_match. inv H; subst. lia.
  - inv H; try lia.
  - inv H; try lia.
  - repeat (destruct_match; try discriminate; []).
  inv H. eapply IHp1 in Heqp. eapply IHp2 in Heqp3. lia.
  - repeat (destruct_match; try discriminate; []).
  inv H. eapply IHp1 in Heqp. eapply IHp2 in Heqp3. lia.
Qed.

Lemma xtseytin_correct' :
  forall p next l n fm c,
    (max_predicate p < next)%positive ->
    xtseytin next p = (n, l, fm) ->
    sat_formula ((l::nil)::fm) c ->
    sat_predicate p c = true.
Proof.
  induction p.
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). subst. inv H0. inv H1.
    inv H0; auto. destruct b.
    + now inv H1.
    + inv H1. now rewrite H3.
  - intros; cbn in *; auto.
  - intros. cbn in *; exfalso. inv H0. inv H1. cbn in H2. inv H2. inv H1; auto.
    inv H0; auto. inv H2. inv H1. congruence.
  - intros; cbn in *. repeat (destruct_match; try discriminate; []); subst. inv H0.
    inv H1. inv H0; auto.
    cbn in *.
    simplify. unfold bar in *. cbn in *. inv H1. apply sat_formula_concat2 in H5. inv H5.
    inv H2. inv H5. congruence. inv H5; try contradiction.
    inv H3. inv H5. congruence. inv H5; try contradiction.
    erewrite IHp1; eauto; try lia.
    erewrite IHp2; eauto; try lia. pose proof (xtseytin_gt _ _ _ _ _ Heqp). lia.
  - intros; cbn in *. repeat (destruct_match; try discriminate; []); subst. inv H0.
    inv H1. inv H0; auto.
    cbn in *.
    simplify. unfold bar in *. cbn in *. inv H1. apply sat_formula_concat2 in H5. inv H5.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp) as HMAX.
    inv H0. inv H5. congruence. inv H5.
    erewrite IHp1; eauto. lia. inv H0; try contradiction.
    erewrite IHp2; eauto with bool. lia.
Qed.

Definition merge_asgn next (c1 c2: positive -> bool) := 
  fun x => if (x <? next)%positive then c1 x else c2 x.

Lemma merge_asgn_left :
  forall next a b p,
    (p < next)%positive -> merge_asgn next a b p = a p.
Proof.
  intros. unfold merge_asgn. apply Pos.ltb_lt in H. now rewrite H.
Qed.

Lemma merge_asgn_right :
  forall next a b p,
    (p >= next)%positive -> merge_asgn next a b p = b p.
Proof.
  intros. unfold merge_asgn.
  assert (next <= p)%positive by lia. eapply OrdersEx.Positive_as_DT.ltb_ge in H0. now rewrite H0.
Qed.

Lemma merge_asgn_middle :
  forall next a b p next' c,
    (next' <= next)%positive -> (p < next)%positive -> merge_asgn next' c (merge_asgn next a b) p = merge_asgn next' c a p.
Proof.
  intros. unfold merge_asgn.
  pose proof (Pos.ltb_spec0 p next). inv H1; try lia. auto.
Qed.

Lemma sat_predicate_merge :
  forall p n a b,
    (max_predicate p < n)%positive ->
    sat_predicate p (merge_asgn n a b) = sat_predicate p a.
Proof.
  induction p.
  - cbn; intros; repeat (destruct_match; try discriminate; []); subst.
    destruct b0; now rewrite merge_asgn_left by lia.
  - cbn; intros; auto.
  - cbn; intros; auto.
  - cbn; intros. rewrite IHp1 by lia. now rewrite IHp2 by lia.
  - cbn; intros. rewrite IHp1 by lia. now rewrite IHp2 by lia.
Qed.

Lemma sat_lit_merge_left :
  forall p n a b,
    (snd p < n)%positive ->
    sat_lit p (merge_asgn n a b) = sat_lit p a.
Proof.
  intros. destruct p; cbn in *; unfold sat_lit. cbn.
  now rewrite merge_asgn_left by lia.
Qed.

Lemma sat_lit_merge_right :
  forall p n a b,
    (snd p >= n)%positive ->
    sat_lit p (merge_asgn n a b) = sat_lit p b.
Proof.
  intros. destruct p; cbn in *; unfold sat_lit. cbn.
  now rewrite merge_asgn_right by lia.
Qed.

Lemma sat_lit_merge_middle :
  forall p n n' a b c,
    (n' <= n)%positive ->
    (snd p < n)%positive ->
    sat_lit p (merge_asgn n' c (merge_asgn n a b)) = sat_lit p (merge_asgn n' c a).
Proof.
  intros. destruct p; cbn in *; unfold sat_lit. cbn. rewrite merge_asgn_middle by lia. auto.
Qed.

Lemma sat_clause_merge :
  forall p n a b c d n' n'',
    (n <= n')%positive ->
    Forall (fun x => (snd x < n)%positive \/ (n' <= snd x < n'')%positive) p ->
    sat_clause p (merge_asgn n a (merge_asgn n' b (merge_asgn n'' c d))) = sat_clause p (merge_asgn n a c).
Proof.
  induction p.
  - intros. auto. 
  - intros * HLT **. inv H. exploit IHp; eauto. intros.
    cbn. inv H2.
    rewrite H. rewrite sat_lit_merge_left by lia. rewrite <- sat_lit_merge_left with (n := n) (b := c) by lia. auto.
    rewrite H. repeat rewrite sat_lit_merge_right by lia. rewrite sat_lit_merge_left by lia.
    rewrite <- sat_lit_merge_right with (n := n) (a := a0) by lia. auto.
Qed.

Lemma sat_clause_merge2 :
  forall p n a b,
    Forall (fun x => (snd x < n)%positive) p ->
    sat_clause p (merge_asgn n a b) = sat_clause p a.
Proof.
  induction p.
  - intros. auto. 
  - intros * **. inv H.
    cbn in *. rewrite IHp; auto. now rewrite sat_lit_merge_left by lia.
Qed.

Lemma sat_clause_merge3 :
  forall p n a b,
    Forall (fun x => (snd x >= n)%positive) p ->
    sat_clause p (merge_asgn n a b) = sat_clause p b.
Proof.
  induction p.
  - intros. auto. 
  - intros * **. inv H.
    cbn in *. rewrite IHp; auto. now rewrite sat_lit_merge_right by lia.
Qed.

Lemma sat_clause_merge4 :
  forall p n n' a b c,
    (n' <= n)%positive ->
    Forall (fun x => (snd x < n)%positive) p ->
    sat_clause p (merge_asgn n' c (merge_asgn n a b)) = sat_clause p (merge_asgn n' c a).
Proof.
  induction p.
  - intros. auto. 
  - intros * HP **. inv H.
    cbn in *. rewrite IHp; auto.
    rewrite sat_lit_merge_middle by lia. auto.
Qed.

Lemma sat_lit_merge5 :
  forall n n' n'' a1 b d p c b0
  (HP : (n <= n')%positive)
  (H2 : (p < n)%positive \/ (n' <= p < n'')%positive),
  (merge_asgn n a1 (merge_asgn n' b (merge_asgn n'' c d)) p = b0) = (merge_asgn n' a1 c p = b0).
Proof.
  intros. unfold merge_asgn. repeat destruct_match; try lia; auto.
  - apply Pos.ltb_ge in Heqb0. apply Pos.ltb_lt in Heqb1. lia.
  - apply Pos.ltb_ge in Heqb1. apply Pos.ltb_lt in Heqb0. lia.
  - apply Pos.ltb_ge in Heqb0. apply Pos.ltb_ge in Heqb1. apply Pos.ltb_ge in Heqb2. lia.
Qed.

Lemma sat_clause_merge5 :
  forall n n' n'' a b c a0 d,
    (n <= n')%positive ->
    Forall (fun x : bool * positive => (snd x < n)%positive \/ (n' <= snd x < n'')%positive) a ->
    sat_clause a (merge_asgn n a0 (merge_asgn n' b (merge_asgn n'' c d))) = sat_clause a (merge_asgn n' a0 c).
Proof.
  induction a.
  - intros. auto. 
  - intros * HP **. inv H.
    cbn in *. rewrite IHa; auto. f_equal.
    unfold sat_lit in *; cbn in *. destruct a; cbn in *. rewrite sat_lit_merge5; auto.
Qed.

Lemma sat_formula_merge :
  forall p n a b c d n' n'',
    (n <= n')%positive ->
    Forall (fun y => Forall (fun x => (snd x < n)%positive \/ (n' <= snd x < n'')%positive) y) p ->
    sat_formula p (merge_asgn n a (merge_asgn n' b (merge_asgn n'' c d))) = sat_formula p (merge_asgn n a c).
Proof.
  induction p.
  - intros. auto. 
  - intros * HLT **. inv H. exploit IHp; eauto. intros.
    cbn. rewrite H. rewrite sat_clause_merge by (auto; try lia). auto.
Qed.

Lemma sat_formula_merge2 :
  forall p n a b c d n' n'',
    (n <= n')%positive ->
    Forall (fun y => Forall (fun x => (snd x < n)%positive \/ (n <= snd x < n')%positive) y) p ->
    sat_formula p (merge_asgn n a (merge_asgn n' b (merge_asgn n'' c d))) = sat_formula p (merge_asgn n a b).
Proof.
  induction p.
  - intros. auto. 
  - intros * HLT **. inv H. exploit IHp; eauto. intros.
    cbn. rewrite H. rewrite sat_clause_merge4. auto. auto.
    apply Forall_forall; intros; eapply Forall_forall in H2; eauto. lia.
Qed.

Lemma sat_formula_merge3 :
  forall p n a b c d n' n'',
    (n <= n')%positive ->
    Forall (fun y => Forall (fun x => (snd x < n)%positive \/ (n' <= snd x < n'')%positive) y) p ->
    sat_formula p (merge_asgn n a (merge_asgn n' b (merge_asgn n'' c d))) = sat_formula p (merge_asgn n' a c).
Proof.
  induction p.
  - intros. auto. 
  - intros * HLT **. inv H. exploit IHp; eauto. intros.
    cbn. rewrite H. f_equal.
    rewrite sat_clause_merge5; auto.
Qed.

Lemma sat_clause_merge6 :
  forall p n a b,
    Forall (fun x => (snd x < n)%positive) p ->
    sat_clause p (merge_asgn n a b) = sat_clause p a.
Proof.
  induction p.
  - intros. auto. 
  - intros * **. inv H.
    cbn in *. rewrite IHp; auto. now rewrite sat_lit_merge_left by lia.
Qed.

Lemma xtseytin_range :
  forall p next n l fm,
  xtseytin next p = (n, l, fm) ->
  Forall (fun y => Forall (fun x => (snd x < max_predicate p + 1)%positive \/ (next <= snd x < n)%positive) y) fm
  /\ ((snd l < max_predicate p + 1)%positive \/ (next <= snd l < n)%positive).
Proof.
  induction p.
  - cbn; intros. destruct_match. inv H. constructor. constructor. cbn. lia.
  - cbn; intros. inv H. repeat (constructor; cbn; try lia).
  - cbn; intros. inv H. repeat (constructor; cbn; try lia).
  - cbn; intros. repeat destruct_match; subst. inv H.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp).
    pose proof (xtseytin_gt _ _ _ _ _ Heqp3).
    eapply IHp1 in Heqp. eapply IHp2 in Heqp3. split.
    inv Heqp. inv Heqp3. inv H2; inv H4.  
    + repeat (constructor; cbn; try lia).
      rewrite Pos.add_comm. rewrite <- Pos.add_max_distr_l. setoid_rewrite Pos.add_comm.
      eapply POrderedType.Positive_as_OT.max_lt_iff. tauto.
      rewrite Pos.add_comm. rewrite <- Pos.add_max_distr_l. setoid_rewrite Pos.add_comm.
      eapply POrderedType.Positive_as_OT.max_lt_iff. tauto.
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. repeat (constructor; cbn; try lia).
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. repeat (constructor; cbn; try lia).
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. repeat (constructor; cbn; try lia).
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. lia.
  - cbn; intros. repeat destruct_match; subst. inv H.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp).
    pose proof (xtseytin_gt _ _ _ _ _ Heqp3).
    eapply IHp1 in Heqp. eapply IHp2 in Heqp3. split.
    inv Heqp. inv Heqp3. inv H2; inv H4.  
    + repeat (constructor; cbn; try lia).
      rewrite Pos.add_comm. rewrite <- Pos.add_max_distr_l. setoid_rewrite Pos.add_comm.
      eapply POrderedType.Positive_as_OT.max_lt_iff. tauto.
      rewrite Pos.add_comm. rewrite <- Pos.add_max_distr_l. setoid_rewrite Pos.add_comm.
      eapply POrderedType.Positive_as_OT.max_lt_iff. tauto.
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. repeat (constructor; cbn; try lia).
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. repeat (constructor; cbn; try lia).
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. repeat (constructor; cbn; try lia).
      eapply Forall_app; split. apply Forall_forall; intros. apply Forall_forall; intros. 
      eapply Forall_forall in H1; eauto. eapply Forall_forall in H1; eauto. lia.
      apply Forall_forall; intros. apply Forall_forall; intros.
      eapply Forall_forall in H3; eauto. eapply Forall_forall in H3; eauto. lia.
    + destruct l0, l1; cbn in *. lia.
Qed.

Opaque stseytin_and. 
Opaque stseytin_or. 
Lemma exists_xtseytin_form_correct :
  forall p next n l fm,
    (max_predicate p < next)%positive ->
    xtseytin next p = (n, l, fm) ->
    forall c, exists c', sat_formula fm (merge_asgn next c c').
Proof.
  induction p.
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). inv H0. subst. cbn.
    now exists (fun _ => true).
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). inv H0. subst. cbn. 
    exists (fun _ => true). unfold sat_lit. cbn. unfold merge_asgn.
    rewrite Pos.ltb_irrefl. tauto.
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). inv H0. subst. cbn.
    exists (fun _ => false). unfold sat_lit. cbn. unfold merge_asgn.
    rewrite Pos.ltb_irrefl. tauto.
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). inv H0. subst. cbn.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp) as MAX.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp3) as MAX2.
    pose proof (IHp1 next _ _ _ ltac:(lia) Heqp c).
    pose proof (IHp2 p0 _ _ _ ltac:(lia) Heqp3 c).
    destruct H0 as [c1 SAT1].
    destruct H1 as [c2 SAT2].
    exists (merge_asgn p0 c1 (merge_asgn p4 c2 (fun _ => ((merge_asgn next c c1) (snd l0) == (fst l0)) && ((merge_asgn p0 c c2) (snd l1) == (fst l1))))).
    destruct l1, l0; cbn in *.
    apply sat_formula_concat; [|apply sat_formula_concat].
    + eapply stseytin_and_correct3; eauto; split; intros.
      * Admitted.

Lemma xtseytin_correct'_unsat :
  forall p next l n fm,
    (max_predicate p < next)%positive ->
    xtseytin next p = (n, l, fm) ->
    forall c, sat_predicate p c = true ->
    (exists c', sat_formula ((l::nil)::fm) (merge_asgn next c c')).
Proof. 
  induction p.
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). subst. inv H0.
    cbn. exists (fun _ => false). destruct b; unfold sat_lit; eauto; cbn.
    + rewrite merge_asgn_left by lia. tauto.
    + rewrite merge_asgn_left by lia. apply negb_true_iff in H1. tauto.
  - intros. cbn in *. eauto. inv H0. cbn. 
    exists (fun _ => true). eauto. split. left. rewrite sat_lit_merge_right; unfold sat_lit; auto.
    cbn. lia. split; auto. left. unfold sat_lit. cbn. rewrite merge_asgn_right by lia. auto.
  - intros. cbn in *. inv H0. discriminate.
  - Opaque stseytin_and. intros; cbn -[stseytin_and] in *. repeat (destruct_match; try discriminate; []); subst. inv H0.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp) as MAX.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp3) as MAX2.
    assert (HMAX1: (max_predicate p1 < next)%positive) by lia.
    assert (HMAX2: (max_predicate p2 < p0)%positive) by lia.
    apply andb_prop in H1. inv H1.
    specialize (IHp1 _ _ _ _ HMAX1 Heqp _ H0).
    specialize (IHp2 _ _ _ _ HMAX2 Heqp3 _ H2). simplify.
    exists (merge_asgn p0 x0 (merge_asgn p4 x (fun _ => true))).
    pose proof (xtseytin_range _ _ _ _ _ Heqp) as RANGE1. inversion RANGE1 as [RANGE1' RANGE1'']. clear RANGE1.
    pose proof (xtseytin_range _ _ _ _ _ Heqp3) as RANGE2. inversion RANGE2 as [RANGE2' RANGE2'']. clear RANGE2.
    inv H4; try contradiction. inv H3; try contradiction.
    destruct l0 as [l0l l0r]. destruct l1 as [l1l l1r]. cbn in *.
    split; [|apply sat_formula_concat; [| apply sat_formula_concat]].
    + left. repeat rewrite sat_lit_merge_right by (cbn; lia). unfold sat_lit; auto.
    + apply stseytin_and_correct3; split; intros; [split|].
      * inv RANGE1''.
        -- rewrite sat_lit_merge_left by (cbn; lia). now rewrite sat_lit_merge_left in H1 by (cbn; lia).
        -- repeat rewrite sat_lit_merge_right by (cbn; lia). rewrite sat_lit_merge_left by (cbn; lia).
           now rewrite sat_lit_merge_right in H1 by (cbn; lia).
      * inv RANGE2''.
        -- repeat rewrite sat_lit_merge_left by (cbn; lia). now rewrite sat_lit_merge_left in H4 by (cbn; lia).
        -- repeat rewrite sat_lit_merge_right by (cbn; lia). rewrite sat_lit_merge_left by (cbn; lia).
           now rewrite sat_lit_merge_right in H4 by (cbn; lia).
      * now repeat rewrite sat_lit_merge_right by (cbn; lia).
    + rewrite sat_formula_merge2. auto. lia.
      do 2 (apply Forall_forall; intros). do 2 (eapply Forall_forall in RANGE1'; eauto). lia.
    + rewrite sat_formula_merge3. auto. lia.
      do 2 (apply Forall_forall; intros). do 2 (eapply Forall_forall in RANGE2'; eauto). lia.
    Transparent stseytin_and.
  - Opaque stseytin_or.
    intros; cbn -[stseytin_or] in *. repeat (destruct_match; try discriminate; []); subst. inv H0.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp) as MAX.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp3) as MAX2.
    assert (HMAX1: (max_predicate p1 < next)%positive) by lia.
    assert (HMAX2: (max_predicate p2 < p0)%positive) by lia.
    apply orb_prop in H1. inv H1.
    + specialize (IHp1 _ _ _ _ HMAX1 Heqp _ H0). simplify. inv H2; try contradiction.
      exists (merge_asgn p0 x (fun _ => true)).
      pose proof (xtseytin_range _ _ _ _ _ Heqp) as RANGE1. inversion RANGE1 as [RANGE1' RANGE1'']. clear RANGE1.
      destruct l0 as [l0l l0r]. cbn in *.
      split; [|apply sat_formula_concat; [| apply sat_formula_concat]].
      * left. repeat rewrite sat_lit_merge_right by (cbn; lia). unfold sat_lit; auto.
      * eapply stseytin_or_correct; eauto; cbn in *; try left.
        ++ repeat rewrite sat_lit_merge_right by (cbn; lia). unfold sat_lit; auto.
        ++ inv RANGE1''.
           -- repeat rewrite sat_lit_merge_left by (cbn; lia). now rewrite sat_lit_merge_left in H1 by (cbn; lia).
           -- repeat rewrite sat_lit_merge_right by (cbn; lia). repeat rewrite sat_lit_merge_left by (cbn; lia). 
              now rewrite sat_lit_merge_right in H1 by (cbn; lia).
      * admit.
      * admit.
    (*   + rewrite sat_formula_merge2. auto. lia. *)
    (*     do 2 (apply Forall_forall; intros). do 2 (eapply Forall_forall in RANGE1'; eauto). lia. *)
    (*   + rewrite sat_formula_merge3. auto. lia. *)
    (*     do 2 (apply Forall_forall; intros). do 2 (eapply Forall_forall in RANGE2'; eauto). lia. *)
    (* + specialize (IHp2 _ _ _ _ HMAX2 Heqp3 _ H2). *)
    (*   pose proof (xtseytin_range _ _ _ _ _ Heqp3) as RANGE2. inversion RANGE2 as [RANGE2' RANGE2'']. clear RANGE2. *)
    (*   destruct l1 as [l1l l1r]. cbn in *. *) Admitted.
    Transparent stseytin_and.

Lemma xtseytin_correct'_unsat' :
  forall p next l n fm,
    (max_predicate p < next)%positive ->
    xtseytin next p = (n, l, fm) ->
    (forall c, ~ sat_formula ((l::nil)::fm) c) ->
    forall c, sat_predicate p c = false.
Proof.
  induction p.
  - intros. cbn in *. repeat (destruct_match; try discriminate; []). subst. inv H0.
    destruct b.
    + specialize (H1 c). case_eq (c p0); auto; intros. exfalso; eapply H1. split. left. auto. constructor.
    + specialize (H1 c). case_eq (c p0); auto; intros. exfalso; eapply H1. split. left. auto. constructor.
  - intros; cbn in *; auto. inv H0. exfalso. eapply H1. split. left. unfold sat_lit. cbn. instantiate (1:=fun x => true). cbn. auto.
    cbn. intuition. left. unfold sat_lit. auto.
  - intros; cbn in *; auto.
  - Opaque stseytin_and. intros; cbn -[stseytin_and] in *. repeat (destruct_match; try discriminate; []); subst. inv H0.
    pose proof (xtseytin_gt _ _ _ _ _ Heqp) as MAX.
    assert (HMAX1: (max_predicate p1 < next)%positive) by lia.
    assert (HMAX2: (max_predicate p2 < p0)%positive) by lia.
    specialize (IHp1 _ _ _ _ HMAX1 Heqp).
    specialize (IHp2 _ _ _ _ HMAX2 Heqp3).
    destruct (c p4) eqn:C1. specialize H1 with c.
    exploit IHp1; eauto. Admitted.

(* Definition tseytin' (p: pred_op) : *)
(*   {fm: formula | forall a, *)
(*       sat_predicate p a = true <-> sat_formula fm a}. *)
(*   refine ( *)
(*       (match xtseytin (max_predicate p + 1) p as X *)
(*              return xtseytin (max_predicate p + 1) p = X -> *)
(*                     {fm: formula | forall a, sat_predicate p a = true <-> sat_formula fm a} *)
(*        with (m, n, fm) => fun H => exist _ ((n::nil) :: fm) _ *)
(*        end) (eq_refl (xtseytin (max_predicate p + 1) p))). *)
(*   intros. eapply xtseytin_correct; eauto. Defined. *)

Definition tseytin (p: pred_op) :
  {fm: formula | ((forall c, ~ sat_formula fm c) ->
    forall c, sat_predicate p c = false) /\ (forall c, sat_formula fm c ->
    sat_predicate p c = true)}.
Proof.
  refine (
      (match xtseytin (max_predicate p + 1) p as X
             return xtseytin (max_predicate p + 1) p = X ->
                    {fm: formula | ((forall c, ~ sat_formula fm c) ->
    forall c, sat_predicate p c = false) /\ (forall c, sat_formula fm c ->
    sat_predicate p c = true)}
       with (m, n, fm) => fun H => exist _ ((n::nil) :: fm) _
       end) (eq_refl (xtseytin (max_predicate p + 1) p))).
  intros. split; intros.
  - case_eq (sat_predicate p c); auto; intros. exfalso. 
    exploit xtseytin_correct'_unsat; eauto. lia. simplify. inv H2; eauto.
    eapply H0; split; eauto.
  - eapply xtseytin_correct'; eauto; lia.
Defined.

Definition tseytin_simple (p: pred_op) : formula :=
  let m := (max_predicate p + 1)%positive in
  let '(m, n, fm) := xtseytin m p in
  (n::nil) :: fm.

Definition sat_pred_tseytin (p: pred_op) :
  ({al : alist | sat_predicate p (interp_alist al) = true}
   + {forall a : asgn, sat_predicate p a = false}).
Proof.
  refine
    ( match tseytin p with
      | exist _ fm _ =>
          match sat_solve fm with
          | inleft (exist _ a _) => inleft (exist _ a _)
          | inright _ => inright _
          end
      end ).
  - inv a0. eapply H0; auto.
  - inv a. eapply H. eauto.
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
          match sat_solve fm with
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

Definition eq_list_to_pred_op (eq_list: list (positive * positive)): pred_op :=
  fold_left (fun a b => a ∧ ((Plit (true, fst b) ∨ Plit (false, snd b))
                          ∧ (Plit (true, snd b) ∨ Plit (false, fst b))))
                        eq_list T.

Definition equiv_check_eq_list eq_list p1 p2 :=
  match sat_pred_simple (simplify (¬ (eq_list_to_pred_op eq_list) ∨ (p1 ∧ ¬ p2 ∨ p2 ∧ ¬ p1))) with
  | None => true
  | _ => false
  end.

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

Lemma equiv_check_eq_list_correct :
  forall eq_list p1 p2,
    equiv_check_eq_list eq_list p1 p2 = true ->
    forall c, sat_predicate (eq_list_to_pred_op eq_list) c = true ->
    sat_predicate p1 c = sat_predicate p2 c.
Proof.
  unfold equiv_check_eq_list. unfold sat_pred_simple. intros.
  destruct_match; try discriminate; [].
  destruct_match. destruct_match. discriminate.
  assert (negb (sat_predicate (eq_list_to_pred_op eq_list) c) = false)
    by (rewrite H0; auto).
  clear Heqs.
  specialize (e c).
  rewrite simplify_correct in e. rewrite sat_predicate_or in e. rewrite <- negate_correct in H1.
  rewrite H1 in e. rewrite orb_false_l in e.
  destruct (sat_predicate p1 c) eqn:X;
    destruct (sat_predicate p2 c) eqn:X2;
    crush.
  rewrite negate_correct in *. rewrite X in *. rewrite X2 in *. auto.
  rewrite negate_correct in *. rewrite X in *. rewrite X2 in *. auto.
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

Lemma PredIn_decidable:
  forall A (a: A) p (eqd: forall a b: A, { a = b } + { a <> b }),
    { PredIn a p } + { ~ PredIn a p }.
Proof.
  intros. destruct (predin eqd a p) eqn:?.
  - apply predin_PredIn in Heqb. tauto.
  - right. unfold not; intros. apply not_true_iff_false in Heqb.
    apply Heqb. now apply predin_PredIn.
Qed.

Lemma sat_predicate_pred_not_in :
  forall p a a' op,
    (forall x, x <> p -> a x = a' x) ->
    ~ PredIn p op ->
    sat_predicate op a = sat_predicate op a'.
Proof.
  induction op; intros H; auto.
  - destruct p0. intros. destruct (peq p p0); subst.
    + exfalso. apply H0. constructor.
    + cbn. assert (p0 <> p) by auto. apply H in H1. rewrite H1. auto.
  - intros. assert (~ PredIn p op1 /\ ~ PredIn p op2).
    split; unfold not; intros; apply H0; constructor; tauto.
    inv H1. specialize (IHop1 H H2). specialize (IHop2 H H3).
    cbn. rewrite IHop1. rewrite IHop2. auto.
  - intros. assert (~ PredIn p op1 /\ ~ PredIn p op2).
    split; unfold not; intros; apply H0; constructor; tauto.
    inv H1. specialize (IHop1 H H2). specialize (IHop2 H H3).
    cbn. rewrite IHop1. rewrite IHop2. auto.
Qed.

Lemma sat_predicateP_det :
  forall a p b b',
    sat_predicateP a p b ->
    sat_predicateP a p b' ->
    b = b'.
Proof. induction p; crush; inv H; inv H0; auto. Qed.

Lemma equiv_sat_predicate_sat_predicateP :
  forall p p' a b,
    p == p' ->
    sat_predicateP a p b ->
    sat_predicateP a p' b.
Proof.
  intros.
  pose proof (sat_pred_equiv_sat_predicateP a p).
  pose proof (sat_pred_equiv_sat_predicateP a p').
  pose proof (sat_predicateP_det a p _ _ H1 H0).
  rewrite H in H3. now rewrite H3 in H2.
Qed.

Definition and_list {A} (p: list (@pred_op A)): @pred_op A :=
  fold_left Pand p T.

Definition or_list {A} (p: list (@pred_op A)): @pred_op A :=
  fold_left Por p ⟂.
