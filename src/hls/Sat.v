(**
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

Require Import Arith Bool List.
Require Import Coq.funind.Recdef.
Require Coq.MSets.MSetPositive.
Require Coq.MSets.MSetProperties.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Program.Wf.
Require Import Vericertlib.

Module PSet := MSetPositive.PositiveSet.
Module PSetProp := MSetProperties.OrdProperties(PSet).

#[local] Open Scope positive.

(** * Problem Definition *)

Definition var := positive.
(** We identify propositional variables with natural numbers. *)

Definition lit := (bool * var)%type.
(** A literal is a combination of a truth value and a variable. *)

Definition clause := list lit.
(** A clause is a list (disjunction) of literals. *)

Definition formula := list clause.
(** A formula is a list (conjunction) of clauses. *)

Definition asgn := var -> bool.
(** An assignment is a function from variables to their truth values. *)

Definition satLit (l : lit) (a : asgn) :=
  a (snd l) = fst l.
(** An assignment satisfies a literal if it maps it to true. *)

Fixpoint satClause (cl : clause) (a : asgn) {struct cl} : Prop :=
  match cl with
  | nil => False
  | l :: cl' => satLit l a \/ satClause cl' a
  end.
(** An assignment satisfies a clause if it satisfies at least one of its
  literals.
 *)

Fixpoint satFormula (fm: formula) (a: asgn) {struct fm} : Prop :=
  match fm with
  | nil => True
  | cl :: fm' => satClause cl a /\ satFormula fm' a
  end.
(** An assignment satisfies a formula if it satisfies all of its clauses. *)

(** * Subroutines *)

(** You'll probably want to compare booleans for equality at some point. *)
Definition bool_eq_dec : forall (x y : bool), {x = y} + {x <> y}.
  decide equality.
Defined.

(** You'll probably want to compare booleans for equality at some point. *)
Definition boolpositive_eq_dec : forall (x y : (bool * positive)), {x = y} + {x <> y}.
  pose proof bool_eq_dec.
  pose proof peq.
  decide equality.
Defined.

(** A literal and its negation can't be true simultaneously. *)
Lemma contradictory_assignment : forall s l cl a,
    s <> fst l
    -> satLit l a
    -> satLit (s, snd l) a
    -> satClause cl a.
  intros.
  red in H0, H1.
  simpl in H1.
  subst.
  tauto.
Qed.

#[local] Hint Resolve contradictory_assignment : core.

(** Augment an assignment with a new mapping. *)
Definition upd (a : asgn) (l : lit) : asgn :=
  fun v : var =>
    if peq v (snd l)
    then fst l
    else a v.

(** Some lemmas about [upd] *)

Lemma satLit_upd_eq : forall l a,
    satLit l (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (peq (snd l) (snd l)); tauto.
Qed.

#[local] Hint Resolve satLit_upd_eq : core.

Lemma satLit_upd_neq : forall v l s a,
    v <> snd l
    -> satLit (s, v) (upd a l)
    -> satLit (s, v) a.
  unfold satLit, upd; simpl; intros.
  destruct (peq v (snd l)); tauto.
Qed.

#[local] Hint Resolve satLit_upd_neq : core.

Lemma satLit_upd_neq2 : forall v l s a,
    v <> snd l
    -> satLit (s, v) a
    -> satLit (s, v) (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (peq v (snd l)); tauto.
Qed.

#[local] Hint Resolve satLit_upd_neq2 : core.

Lemma satLit_contra : forall s l a cl,
    s <> fst l
    -> satLit (s, snd l) (upd a l)
    -> satClause cl a.
  unfold satLit, upd; simpl; intros.
  destruct (peq (snd l) (snd l)); intuition auto with *.
Qed.

#[local] Hint Resolve satLit_contra : core.

Ltac magic_solver := simpl; intros; subst; intuition eauto; firstorder;
                     match goal with
                     | [ H1 : satLit ?l ?a, H2 : satClause ?cl ?a |- _ ] =>
                       assert (satClause cl (upd a l)); firstorder
                     end.

(** Strongly-specified function to update a clause to reflect the effect of making a particular
  literal true.  *)
Definition setClause : forall (cl : clause) (l : lit),
    {cl' : clause |
      forall a, satClause cl (upd a l) <-> satClause cl' a}
    + {forall a, satLit l a -> satClause cl a}.
  refine (fix setClause (cl: clause) (l: lit) {struct cl} :=
            match cl with
            | nil => inleft (exist _ nil _)
            | x :: xs =>
              match setClause xs l with
              | inright p => inright _
              | inleft (exist _ cl' H) =>
                match peq (snd x) (snd l), bool_eq_dec (fst x) (fst l) with
                | left p_eq, left bool_eq => inright _
                | left eq, right ne => inleft (exist _ cl' _)
                | right neq, _ => inleft (exist _ (x :: cl') _)
                end
              end
            end); clear setClause; try magic_solver.
  - intros; simpl; left; apply injective_projections in bool_eq; subst; auto.
  - split; intros. simpl in H0. inversion H0. eapply satLit_contra; eauto.
    destruct x; simpl in *; subst. auto.
    apply H. eauto.
    simpl. right. apply H; eauto.
  - split; intros; simpl in *. inversion H0. destruct x; simpl in *; subst.
    left. eauto.
    right. apply H. eauto.
    inversion H0. left. apply satLit_upd_neq2. auto. auto.
    right. apply H. auto.
Defined.

(** For testing purposes, we define a weakly-specified function as a thin
  wrapper around [setClause].
 *)
Definition setClauseSimple (cl : clause) (l : lit) :=
  match setClause cl l with
  | inleft (exist _ cl' _) => Some cl'
  | inright _ => None
  end.

(*Eval compute in setClauseSimple ((false, 1%nat) :: nil) (true, 1%nat).*)
(*Eval compute in setClauseSimple nil (true, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (true, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (false, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: nil) (false, 1).
Eval compute in setClauseSimple ((true, 0) :: (true, 1) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: (true, 1) :: nil) (false, 1).
Eval compute in setClauseSimple ((true, 0) :: (false, 1) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: (false, 1) :: nil) (false, 1).*)

(** It's useful to have this strongly-specified nilness check. *)
Definition isNil : forall (A : Set) (ls : list A), {ls = nil} + {ls <> nil}.
  destruct ls; [left|right]; [auto|]; unfold not; intros; inversion H.
Defined.
Arguments isNil [A].

(** Some more lemmas that I found helpful.... *)

Lemma satLit_idem_lit : forall l a l',
    satLit l a
    -> satLit l' a
    -> satLit l' (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (peq (snd l') (snd l)); congruence.
Qed.

#[local] Hint Resolve satLit_idem_lit : core.

Lemma satLit_idem_clause : forall l a cl,
    satLit l a
    -> satClause cl a
    -> satClause cl (upd a l).
  induction cl; simpl; intuition.
Qed.

#[local] Hint Resolve satLit_idem_clause : core.

Lemma satLit_idem_formula : forall l a fm,
    satLit l a
    -> satFormula fm a
    -> satFormula fm (upd a l).
  induction fm; simpl; intuition.
Qed.

#[local] Hint Resolve satLit_idem_formula : core.

(** Function that updates an entire formula to reflect setting a literal to true.  *)
Definition setFormula : forall (fm : formula) (l : lit),
    {fm' : formula |
      forall a, satFormula fm (upd a l) <-> satFormula fm' a}
    + {forall a, satLit l a -> ~satFormula fm a}.
  refine (fix setFormula (fm: formula) (l: lit) {struct fm} :=
            match fm with
            | nil => inleft (exist _ nil _)
            | cl' :: fm' =>
              match setFormula fm' l with
              | inright p => inright _
              | inleft (exist _ fm'' H) =>
                match setClause cl' l with
                | inright H' => inleft (exist _ fm'' _)
                | inleft (exist _ cl'' _) =>
                  if isNil cl''
                  then inright _
                  else inleft (exist _ (cl'' :: fm'') _)
                end
              end
            end); clear setFormula; magic_solver.
Defined.

Definition setFormulaSimple (fm : formula) (l : lit) :=
  match setFormula fm l with
  | inleft (exist _ fm' _) => Some fm'
  | inright _ => None
  end.

(* Eval compute in setFormulaSimple (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil) (true, 1%nat). *)
(* Eval compute in setFormulaSimple nil (true, 0). *)
(* Eval compute in setFormulaSimple (((true, 0) :: nil) :: nil) (true, 0). *)
(* Eval compute in setFormulaSimple (((false, 0) :: nil) :: nil) (true, 0). *)
(* Eval compute in setFormulaSimple (((false, 1) :: nil) :: nil) (true, 0). *)
(* Eval compute in setFormulaSimple (((false, 1) :: (true, 0) :: nil) :: nil) (true, 0). *)
(* Eval compute in setFormulaSimple (((false, 1) :: (false, 0) :: nil) :: nil) (true, 0). *)

#[local] Hint Extern 1 False => discriminate : core.

Local Hint Extern 1 False =>
match goal with
| [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
end : core.

(** Code that either finds a unit clause in a formula or declares that there are none.  *)
Definition findUnitClause : forall (fm: formula),
    {l : lit | In (l :: nil) fm}
    + {forall l, ~In (l :: nil) fm}.
  refine (fix findUnitClause (fm: formula) {struct fm} :=
            match fm with
            | nil => inright _
            | (l :: nil) :: fm' => inleft (exist _ l _)
            | _ :: fm' =>
              match findUnitClause fm' with
              | inleft (exist _ l _) => inleft (exist _ l _)
              | inright H => inright _
              end
            end
         ); clear findUnitClause; magic_solver.
Defined.

(** The literal in a unit clause must always be true in a satisfying assignment.  *)
Lemma unitClauseTrue : forall l a fm,
    In (l :: nil) fm
    -> satFormula fm a
    -> satLit l a.
  induction fm; intuition auto with *.
  inversion H.
  inversion H; subst; simpl in H0; intuition.
  apply IHfm; eauto. inv H0. eauto.
Qed.

#[local] Hint Resolve unitClauseTrue : core.

(** Unit propagation.  The return type of [unitPropagate] signifies that three results are possible:
  - [None]: There are no unit clauses.
  - [Some (inleft _)]: There is a unit clause, and here is a formula reflecting
    setting its literal to true.
  - [Some (inright _)]: There is a unit clause, and propagating it reveals that
    the formula is unsatisfiable.
 *)
Definition unitPropagate : forall (fm : formula), option (sigT (fun fm' : formula =>
                                                                  {l : lit |
                                                                    (forall a, satFormula fm a -> satLit l a)
                                                                    /\ forall a, satFormula fm (upd a l) <-> satFormula fm' a})
                                                          + {forall a, ~satFormula fm a}).
  refine (fix unitPropagate (fm: formula) {struct fm} :=
            match findUnitClause fm with
            | inright H => None
            | inleft (exist _ l _) =>
              match setFormula fm l with
              | inright _ => Some (inright _)
              | inleft (exist _ fm' _) =>
                Some (inleft (existT _ fm' (exist _ l _)))
              end
            end
         ); clear unitPropagate; magic_solver.
Defined.


Definition unitPropagateSimple (fm : formula) :=
  match unitPropagate fm with
  | None => None
  | Some (inleft (existT _ fm' (exist _ l _))) => Some (Some (fm', l))
  | Some (inright _) => Some None
  end.

(*Eval compute in unitPropagateSimple (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil).
Eval compute in unitPropagateSimple nil.
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 1) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 0) :: (false, 1) :: nil) :: nil).
Eval compute in unitPropagateSimple (((false, 0) :: (false, 1) :: nil) :: ((true, 0) :: nil) :: nil).*)


(** * The SAT Solver *)

(** This section defines a DPLL SAT solver in terms of the subroutines.  *)

(** An arbitrary heuristic to choose the next variable to split on *)
Definition chooseSplit (fm : formula) :=
  match fm with
  | ((l :: _) :: _) => l
  | _ => (true, 1)
  end.

Definition negate (l : lit) := (negb (fst l), snd l).

#[local] Hint Unfold satFormula : core.

Lemma satLit_dec : forall l a,
    {satLit l a} + {satLit (negate l) a}.
  destruct l.
  unfold satLit; simpl; intro.
  destruct b; destruct (a v); simpl; auto.
Qed.

(** We'll represent assignments as lists of literals instead of functions. *)
Definition alist := list lit.

Fixpoint interp_alist (al : alist) : asgn :=
  match al with
  | nil => fun _ => true
  | l :: al' => upd (interp_alist al') l
  end.

(*Eval compute in boundedSatSimple 100 nil.
Eval compute in boundedSatSimple 100 (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil).*)

Definition lit_set_cl (cl: clause) :=
  fold_right PSet.add PSet.empty (map snd cl).

Lemma lit_set_cl_in_set :
  forall cl v,
    In v (map snd cl) ->
    PSet.In v (lit_set_cl cl).
Proof.
  induction cl; crush.
  destruct a; cbn [snd] in *; inv H.
  - cbn. apply PSetProp.P.FM.add_1; auto.
  - cbn. apply PSetProp.P.FM.add_2.
    now apply IHcl.
Qed.

Lemma lit_set_cl_not_in_set :
  forall cl v,
    ~ In v (map snd cl) ->
    ~ PSet.In v (lit_set_cl cl).
Proof.
  induction cl; crush.
  destruct a; cbn [snd] in *.
  assert (p <> v /\ ~ In v (map snd cl))
    by (split; unfold not; intros; apply H; tauto).
  inv H0. cbn. unfold not; intros. 
  eapply IHcl; eauto.
  unfold lit_set_cl.
  eapply PSetProp.P.Dec.F.add_3; eassumption.
Qed.

Lemma lit_set_cl_in_set2 :
  forall cl v,
    PSet.In v (lit_set_cl cl) ->
    In v (map snd cl).
Proof.
  intros. destruct (in_dec peq v (map snd cl)); auto.
  apply lit_set_cl_not_in_set in n. contradiction.
Qed.

Definition lit_set (fm: formula) :=
  fold_right PSet.union PSet.empty (map lit_set_cl fm).

(* Compute NSet.cardinal (lit_set (((true, 1)::(true, 1)::(true, 1)::nil)::nil)). *)

Definition sat_measure_cl (cl: clause) := PSet.cardinal (lit_set_cl cl).

Definition sat_measure (fm: formula) := PSet.cardinal (lit_set fm).

Lemma elim_clause :
  forall (cl: clause) l, In l cl -> exists H, setClause cl l = inright H.
Proof.
  induction cl; intros; simpl in *; try contradiction.
  destruct (setClause cl l) eqn:?; [|econstructor; eauto].
  destruct s. inversion H; subst. clear H.
  destruct (peq (snd l) (snd l)); [| contradiction].
  destruct (bool_eq_dec (fst l) (fst l)); [| contradiction].
  econstructor. eauto. apply IHcl in H0.
  inversion H0. rewrite H1 in Heqs. discriminate.
Qed.

Lemma sat_measure_setClause' :
  forall cl cl' l A,
    setClause cl l = inleft (exist _ cl' A) ->
    ~ In (snd l) (map snd cl').
Proof.
  induction cl; intros.
  { simpl in *. inv H. unfold not in *. intros. inv H. }
  simpl in H.
  repeat (destruct_match; crush; []). destruct_match.
  repeat (destruct_match; crush; []). inv H. eapply IHcl; eauto.
  inv H. unfold not. intros. inv H. contradiction. eapply IHcl; eauto.
Qed.

Lemma sat_measure_setClause'' :
  forall cl cl' l A,
    setClause cl l = inleft (exist _ cl' A) ->
    forall l',
      l' <> snd l ->
      In l' (map snd cl) ->
      In l' (map snd cl').
Proof.
  induction cl; intros.
  { inversion H1. }
  { inversion H1. subst. simpl in H.
    repeat (destruct_match; crush; []). inv H. simpl.
    inv H1. eauto. right. eapply IHcl; eauto.
    simpl in H. repeat (destruct_match; crush; []). destruct_match.
    repeat (destruct_match; crush; []). inv H. eapply IHcl; eauto.
    inv H1; crush. inv H. simplify. auto.
    inv H. simpl. right. eapply IHcl; eauto.
  }
Qed.

Definition InFm l (fm: formula) := exists cl b, In cl fm /\ In (b, l) cl.

Lemma satFormulaHasEmpty :
  forall fm,
    In nil fm ->
    forall a, ~ satFormula fm a.
Proof.
  induction fm; crush.
  unfold not; intros. inv H0. inv H; auto.
  eapply IHfm; eauto.
Qed.

Lemma InFm_chooseSplit :
  forall l b c,
    InFm (snd (chooseSplit ((l :: b) :: c))) ((l :: b) :: c).
Proof.
  simpl; intros. destruct l; cbn.
  exists ((b0, v) :: b). exists b0.
  split; constructor; auto.
Qed.

Lemma InFm_negated_chooseSplit :
  forall l b c,
    InFm (snd (negate (chooseSplit ((l :: b) :: c)))) ((l :: b) :: c).
Proof.
  simpl; intros. destruct l; cbn.
  exists ((b0, v) :: b). exists b0.
  split; constructor; auto.
Qed.

Definition hasNoNil : forall fm: formula, {In nil fm} + {~ In nil fm}.
  refine (fix hasNoNil (fm: formula) {struct fm} :=
    match fm with
    | cl :: fm' =>
      match isNil cl with
      | left clIsNil => left _
      | right clIsNotNil =>
        match hasNoNil fm' with
        | left hasNilfm' => left _
        | right hasNoNilfm' => right _
        end
      end
    | nil => right _
    end
  ); auto.
  - subst. apply in_eq.
  - apply in_cons; assumption.
Defined.

Lemma sat_measure_setClause :
  forall cl cl' l b A,
    (forall b', ~ In (b', l) cl) ->
    setClause cl (b, l) = inleft (exist _ cl' A) ->
    lit_set_cl cl = lit_set_cl cl'.
Proof.
  induction cl; intros.
  - inv H0. auto.
  - cbn in H0. repeat (destruct_match; try discriminate; []).
    destruct_match.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *.
      exfalso.
      eapply H. econstructor. auto.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *.
      assert (forall b', ~ In (b', l) cl).
      { unfold not; intros. eapply H. apply in_cons. eassumption. }
      eapply IHcl in Heqs; [|assumption].
      unfold sat_measure_cl. cbn -[PSet.cardinal].
      unfold sat_measure_cl in Heqs.
      replace (fold_right PSet.add PSet.empty (map snd cl))
        with (lit_set_cl cl); auto.
      rewrite Heqs. auto.
Qed.

Lemma in_map_snd_forall :
  forall A B (cl: list (A * B)) l,
    ~ In l (map snd cl) ->
    (forall b', ~ In (b', l) cl).
Proof.
  unfold not; intros; apply H.
  replace l with (snd (b', l)) by auto.
  now apply in_map.
Qed.

Lemma sat_measure_setClause_In_neq :
  forall cl cl' l v b A,
    In v (map snd cl) ->
    setClause cl (b, l) = inleft (exist _ cl' A) ->
    v <> l ->
    In v (map snd cl').
Proof.
    induction cl; intros.
  - inv H0. auto.
  - cbn in H0. repeat (destruct_match; try discriminate; []).
    destruct_match.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *. eapply IHcl; eauto.
      inv H; auto. contradiction.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *.
      destruct (peq v v0); subst.
      { now constructor. }
      cbn. right. eapply IHcl; eauto. inv H; auto.
      contradiction.
Qed.

Lemma sat_measure_setClause_In_rev :
  forall cl cl' l v b A,
    In v (map snd cl') ->
    setClause cl (b, l) = inleft (exist _ cl' A) ->
    In v (map snd cl).
Proof.
    induction cl; intros.
  - inv H0. auto.
  - cbn in H0. repeat (destruct_match; try discriminate; []).
    destruct_match.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *.
      cbn; exploit IHcl; eauto.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *.
      destruct (peq v v0); subst.
      { now constructor. }
      cbn. right. eapply IHcl in Heqs; eauto. cbn in H.
      inv H; auto. contradiction.
Qed.

Lemma sat_measure_setClause_In_neq2 :
  forall cl cl' l b A,
    setClause cl (b, l) = inleft (exist _ cl' A) ->
    ~ In l (map snd cl').
Proof.
    induction cl; intros.
  - inv H. auto.
  - cbn in H. repeat (destruct_match; try discriminate; []).
    destruct_match.
    + repeat (destruct_match; try discriminate; []).
      inv H. cbn [snd fst] in *. eapply IHcl; eauto.
    + repeat (destruct_match; try discriminate; []).
      inv H. cbn [snd fst] in *.
      cbn. unfold not; intros. inv H. contradiction.
      eapply IHcl; eauto.
Qed.

Lemma sat_measure_setClause_In :
  forall cl cl' l b A,
    In l (map snd cl) ->
    setClause cl (b, l) = inleft (exist _ cl' A) ->
    (sat_measure_cl cl' < sat_measure_cl cl)%nat.
Proof.
  induction cl; intros.
  - crush.
  - cbn in H0. repeat (destruct_match; try discriminate; []).
    destruct_match.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *. clear Heqs2. clear Heqs1.
      inv H; cbn [snd fst] in *.
      * destruct (in_dec peq v (map snd cl)).
        -- exploit IHcl; eauto; intros. unfold sat_measure_cl in *.
           cbn -[PSet.cardinal]. apply lit_set_cl_in_set in i0.
           rewrite PSetProp.P.add_cardinal_1; auto.
        -- apply sat_measure_setClause in Heqs; [|now apply in_map_snd_forall].
           unfold sat_measure_cl in *. cbn -[PSet.cardinal].
           setoid_rewrite Heqs.
           apply lit_set_cl_not_in_set in n0.
           rewrite PSetProp.P.add_cardinal_2; auto.
           now rewrite <- Heqs.
      * exploit IHcl; eauto; intros. unfold sat_measure_cl in *.
        cbn. rewrite PSetProp.P.add_cardinal_1; auto.
        now apply lit_set_cl_in_set.
    + repeat (destruct_match; try discriminate; []). inv H0.
      cbn [snd fst] in *. cbn in H. inv H; [contradiction|].
      exploit IHcl; eauto; intros.
      unfold sat_measure_cl in *. cbn.
      destruct (in_dec peq v (map snd cl)); destruct (in_dec peq v (map snd x)).
      * apply lit_set_cl_in_set in i0. apply lit_set_cl_in_set in i1.
        repeat rewrite PSetProp.P.add_cardinal_1 by auto. auto.
      * exploit sat_measure_setClause_In_neq. eapply i0. eauto. auto. intros.
        contradiction.
      * apply lit_set_cl_in_set in i0. apply lit_set_cl_not_in_set in n0.
        rewrite PSetProp.P.add_cardinal_1 by auto.
        rewrite PSetProp.P.add_cardinal_2 by auto. unfold lit_set_cl in *; lia.
      * apply lit_set_cl_not_in_set in n0. apply lit_set_cl_not_in_set in n1.
        repeat rewrite PSetProp.P.add_cardinal_2 by auto.
        unfold lit_set_cl in *; lia.
Qed.

(* Lemma sat_measure_setFormula :
  forall cl cl' l b b' A,
    In (b', l) cl ->
    setClause cl (b, l) = inleft (exist _ cl' A) ->
    (sat_measure_cl cl' < sat_measure_cl cl)%nat.
Proof.
  induction cl; intros.
  - crush.
  - cbn in H0. repeat (destruct_match; try discriminate; []).
    destruct_match.
    + repeat (destruct_match; try discriminate; []).
      inv H0. cbn [snd fst] in *.*)

Lemma InFm_dec:
  forall l fm, { InFm l fm } + { ~ InFm l fm }.
Proof.
  intros. induction fm.
  right. unfold InFm. unfold not. intros. inv H. inv H0. inv H. inv H0.
  destruct (in_dec peq l (map snd a)).
  - assert (exists b, In a (a :: fm) /\ In (b, l) a).
    { apply list_in_map_inv in i. inv i. inv H. destruct x. econstructor. split. constructor; auto.
      eauto.
    }
    left. unfold InFm. exists a. eauto.
  - inv IHfm.
    + left. unfold InFm in H. destruct H as (cl & b & H1 & H2).
      unfold InFm. exists cl. exists b. constructor; auto. apply in_cons. auto.
    + right. unfold not; intros.
      destruct H0 as (cl & b & H1 & H2). inv H1.
      * apply n. replace l with (snd (b, l)) by auto.
        now apply in_map.
      * apply H. unfold InFm; firstorder.
Qed.

Lemma InFm_cons :
  forall l cl fm,
    InFm l (cl :: fm) ->
    (exists b, In (b, l) cl) \/ (InFm l fm).
Proof.
  intros. destruct H as (cl' & b' & H1 & H2).
  inv H1; firstorder.
Qed.

Lemma InFm_cons2 :
  forall l cl b fm,
    In (b, l) cl \/ (InFm l fm) ->
    InFm l (cl :: fm).
Proof. intros. inv H; firstorder. Qed.

Lemma lit_set_in_set :
  forall fm v,
    InFm v fm ->
    PSet.In v (lit_set fm).
Proof.
  induction fm; intros.
  - destruct H as (cl & b & H1 & H2); inv H1.
  - apply InFm_cons in H. inv H.
    + inv H0. cbn. apply PSetProp.P.FM.union_2. apply lit_set_cl_in_set.
      replace v with (snd (x, v)) by auto. now apply in_map.
    + cbn. apply PSetProp.P.FM.union_3. eauto.
Qed.

Lemma lit_set_in_set2 :
  forall fm v,
    PSet.In v (lit_set fm) ->
    InFm v fm.
Proof.
  induction fm; intros.
  - cbn in H. apply PSetProp.P.FM.empty_iff in H; contradiction.
  - cbn in H. apply PSetProp.P.Dec.F.union_1 in H. inv H.
    + apply lit_set_cl_in_set2 in H0. apply list_in_map_inv in H0.
      destruct H0 as [[b v'] [EQ H0]]. inv EQ. cbn.
      exists a. exists b. split; auto. now constructor.
    + apply InFm_cons2 with (b := true); right. eauto.
Qed.

Lemma lit_set_cl_eq :
  forall cl v b cl' A,
    In v (map snd cl) ->
    setClause cl (b, v) = inleft (exist _ cl' A) ->
    PSet.Equal (lit_set_cl cl) (PSet.add v (lit_set_cl cl')).
Proof.
  constructor; intros.
  - destruct (peq a v); subst.
    + apply PSetProp.P.FM.add_1; auto.
    + apply PSetProp.P.FM.add_2.
      apply lit_set_cl_in_set2 in H1. apply lit_set_cl_in_set.
      eapply sat_measure_setClause_In_neq; eauto.
  - apply PSet.add_spec in H1. inv H1.
    + apply lit_set_cl_in_set; auto.
    + apply lit_set_cl_in_set. apply lit_set_cl_in_set2 in H2.
      eapply sat_measure_setClause_In_rev; eauto.
Qed.

Lemma lit_set_cl_neq :
  forall cl v b cl' A,
    ~ In v (map snd cl) ->
    setClause cl (b, v) = inleft (exist _ cl' A) ->
    PSet.Equal (lit_set_cl cl) (lit_set_cl cl').
Proof.
  constructor; intros.
  - erewrite <- sat_measure_setClause; eauto.
    intros. unfold not; intros. apply H.
    replace v with (snd (b', v)) by auto; apply in_map; auto.
  - erewrite sat_measure_setClause; eauto.
    intros. unfold not; intros. apply H.
    replace v with (snd (b', v)) by auto; apply in_map; auto.
Qed.

Lemma sat_measure_setFormula1 :
  forall fm fm' l b A,
    setFormula fm (b, l) = inleft (exist _ fm' A) ->
    ~ InFm l fm'.
Proof.
  induction fm.
  - intros. inv H. unfold not. intros. destruct H as (cl & b0 & H1 & H2). inv H1.
  - intros. unfold sat_measure, lit_set.
    cbn in H. repeat (destruct_match; try discriminate; []).
    destruct_match; repeat (destruct_match; try discriminate; []); inv H.
    + eapply IHfm in Heqs.
      assert (~ In l (map snd x0))
        by (eapply sat_measure_setClause_In_neq2; eauto).
      unfold not; intros.
      apply InFm_cons in H0. inv H0; auto. inv H1.
      apply H. replace l with (snd (x1, l)) by auto. apply in_map; auto.
    + eapply IHfm in Heqs. auto.
Qed.

Lemma sat_measure_setFormula2 :
  forall fm fm' l v b A,
    InFm v fm' ->
    setFormula fm (b, l) = inleft (exist _ fm' A) ->
    InFm v fm.
Proof.
  induction fm.
  - intros. simplify. inv H0. destruct H as (cl & b0 & Y1 & Y2). inv Y1.
  - intros. unfold sat_measure, lit_set.
    cbn in H0. repeat (destruct_match; try discriminate; []).
    destruct_match; repeat (destruct_match; try discriminate; []); inv H0.
    + apply InFm_cons in H. inv H.
      * destruct H0 as (b0 & H0).
        apply in_map with (f := snd) in H0. cbn in H0.
        exploit sat_measure_setClause_In_rev; eauto; intros.
        apply list_in_map_inv in H. destruct H as (c & H1 & H2). destruct c. inv H1.
        cbn. exists a. exists b1. intuition auto with *.
      * exploit IHfm; eauto; intros. eapply InFm_cons2; tauto.
    + exploit IHfm; eauto; intros. eapply InFm_cons2; tauto.
  Unshelve.
  all: exact true.
Qed.

Lemma sat_measure_setFormula3 :
  forall fm fm' l b A,
    setFormula fm (b, l) = inleft (exist _ fm' A) ->
    PSet.Subset (lit_set fm') (lit_set fm).
Proof.
  unfold PSet.Subset; intros.
  apply lit_set_in_set.
  apply lit_set_in_set2 in H0.
  eapply sat_measure_setFormula2; eauto.
Qed.

Lemma sat_measure_setFormula :
  forall fm fm' l b A,
    InFm l fm ->
    setFormula fm (b, l) = inleft (exist _ fm' A) ->
    (sat_measure fm' < sat_measure fm)%nat.
Proof.
  intros. unfold sat_measure.
  apply PSetProp.P.subset_cardinal_lt with (x:=l).
  eapply sat_measure_setFormula3; eauto.
  now apply lit_set_in_set.
  unfold not; intros.
  eapply sat_measure_setFormula1. eauto.
  now apply lit_set_in_set2 in H1.
Qed.

Lemma sat_measure_propagate_unit :
  forall fm' fm H,
    unitPropagate fm = Some (inleft (existT _ fm' H)) ->
    (sat_measure fm' < sat_measure fm)%nat.
Proof.
  unfold unitPropagate; intros. cbn in *.
  destruct fm; intros. crush.
  repeat (destruct_match; try discriminate; []). inv H0.
  destruct x.
  eapply sat_measure_setFormula; eauto.
  cbn in i. clear Heqs. clear H3. inv i.
  eexists. exists b. split. constructor. auto. now constructor.
  exists ((b, v) :: nil). exists b. split.
  apply in_cons. auto. now constructor.
Qed.

Program Fixpoint satSolve (fm: formula) { measure (sat_measure fm) }:
  {al : alist | satFormula fm (interp_alist al)} + {forall a, ~satFormula fm a} :=
  match isNil fm with
  | left fmIsNil => inleft _ (exist _ nil _)
  | right fmIsNotNil =>
    match hasNoNil fm with
    | left hasNilfm => inright _ _
    | right hasNoNilfm =>
      match unitPropagate fm with
      | Some (inleft (existT _ fm' (exist _ l _))) =>
        match satSolve fm' with
        | inleft (exist _ al _) => inleft _ (exist _ (l :: al) _)
        | inright _ => inright _ _
        end
      | Some (inright _) => inright _ _
      | None =>
        let l := chooseSplit fm in
        match setFormula fm l with
        | inleft (exist _ fm' _) =>
          match satSolve fm' with
          | inleft (exist _ al _) => inleft _ (exist _ (l :: al) _)
          | inright _ =>
            match setFormula fm (negate l) with
            | inleft (exist _ fm' _) =>
              match satSolve fm' with
              | inleft (exist _ al _) => inleft _ (exist _ (negate l :: al) _)
              | inright _ => inright _ _
              end
            | inright _ => inright _ _
            end
          end
        | inright _ =>
          match setFormula fm (negate l) with
          | inleft (exist _ fm' _) =>
            match satSolve fm' with
            | inleft (exist _ al _) => inleft _ (exist _ (negate l :: al) _)
            | inright _ => inright _ _
            end
          | inright _ => inright _ _
          end
        end
      end
    end
  end.
Next Obligation.
  apply satFormulaHasEmpty; assumption. Defined.
Next Obligation.
  eapply sat_measure_propagate_unit; eauto. Defined.
Next Obligation.
  apply i; auto. Defined.
Next Obligation.
  unfold not; intros; eapply wildcard'; apply i; eauto. Defined.
Next Obligation.
  intros. symmetry in Heq_anonymous.
  destruct (chooseSplit fm) eqn:?.
  apply sat_measure_setFormula in Heq_anonymous; auto. unfold isNil in *.
  destruct fm; try discriminate.
  assert (c <> nil).
  { unfold not; intros. apply hasNoNilfm. constructor; auto. }
  destruct c; try discriminate.
  replace p with (snd (b, p)) by auto. rewrite <- Heqp.
  apply InFm_chooseSplit. Defined.
Next Obligation.
  apply wildcard'0; auto. Defined.
Next Obligation.
  eapply sat_measure_setFormula; eauto.
  destruct fm; try discriminate. destruct c; try discriminate.
  apply InFm_chooseSplit. Defined.
Next Obligation.
  apply wildcard'2; auto. Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a);
  [assert (satFormula fm (upd a (chooseSplit fm)))
  | assert (satFormula fm (upd a (negate (chooseSplit fm))))]; auto.
  { eapply wildcard'1. apply wildcard'0; eauto. }
  { eapply wildcard'. apply wildcard'2; eauto. }
Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a);
  [assert (satFormula fm (upd a (chooseSplit fm)))
  | assert (satFormula fm (upd a (negate (chooseSplit fm))))]; auto.
  { eapply wildcard'1. eapply wildcard'0. eauto. }
  { eapply wildcard'; eauto. }
Defined.
Next Obligation.
  eapply sat_measure_setFormula; eauto.
  destruct fm; try discriminate. destruct c; try discriminate.
  apply InFm_chooseSplit. Defined.
Next Obligation.
  apply wildcard'1; auto. Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a);
  [assert (satFormula fm (upd a (chooseSplit fm)))
  | assert (satFormula fm (upd a (negate (chooseSplit fm))))]; auto.
  { eapply wildcard'0; eauto. }
  { eapply wildcard'; apply wildcard'1; eauto. }
Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a).
  { eapply wildcard'0; eauto. }
  { eapply wildcard'; eauto. }
Defined.

Definition satSolveSimple (fm : formula) :=
  match satSolve fm with
  | inleft (exist _ a _) => Some a
  | inright _ => None
  end.

(* Eval compute in satSolveSimple nil. *)
