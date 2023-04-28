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

(** * Verified SAT Solver

This development was heavily inspired by the example of a Sat solver given in:
http://www.cs.berkeley.edu/~adamc/itp/.

First, some basic definitions, such as variables, literals, clauses and
formulas.  In this development [positive] is used instead of [nat] because it
integrates better into CompCert itself. *)

Definition var := positive.
Definition lit := (bool * var)%type.
Definition clause := list lit.
Definition formula := list clause.

(** The most general version of an assignment is a function mapping variables to
booleans.  This provides a possible value for all variables that could exist. *)

Definition asgn := var -> bool.

Definition sat_lit (l : lit) (a : asgn) :=
  a (snd l) = fst l.

Fixpoint sat_clause (cl : clause) (a : asgn) {struct cl} : Prop :=
  match cl with
  | nil => False
  | l :: cl' => sat_lit l a \/ sat_clause cl' a
  end.

(** An assignment satisfies a formula if it satisfies all of its clauses. *)
Fixpoint sat_formula (fm: formula) (a: asgn) {struct fm} : Prop :=
  match fm with
  | nil => True
  | cl :: fm' => sat_clause cl a /\ sat_formula fm' a
  end.

(** * Subroutines *)

(** You'll probably want to compare booleans for equality at some point. *)
Definition bool_eq_dec : forall (x y : bool), {x = y} + {x <> y}.
  decide equality.
Defined.

Definition boolpositive_eq_dec : forall (x y : (bool * positive)), {x = y} + {x <> y}.
  pose proof bool_eq_dec.
  pose proof peq.
  decide equality.
Defined.

(** A literal and its negation can't be true simultaneously. *)
Lemma contradictory_assignment : forall s l cl a,
    s <> fst l
    -> sat_lit l a
    -> sat_lit (s, snd l) a
    -> sat_clause cl a.
Proof.
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

Lemma sat_lit_upd_eq : forall l a,
    sat_lit l (upd a l).
  unfold sat_lit, upd; simpl; intros.
  destruct (peq (snd l) (snd l)); tauto.
Qed.

#[local] Hint Resolve sat_lit_upd_eq : core.

Lemma sat_lit_upd_neq : forall v l s a,
    v <> snd l
    -> sat_lit (s, v) (upd a l)
    -> sat_lit (s, v) a.
  unfold sat_lit, upd; simpl; intros.
  destruct (peq v (snd l)); tauto.
Qed.

#[local] Hint Resolve sat_lit_upd_neq : core.

Lemma sat_lit_upd_neq2 : forall v l s a,
    v <> snd l
    -> sat_lit (s, v) a
    -> sat_lit (s, v) (upd a l).
  unfold sat_lit, upd; simpl; intros.
  destruct (peq v (snd l)); tauto.
Qed.

#[local] Hint Resolve sat_lit_upd_neq2 : core.

Lemma sat_lit_contra : forall s l a cl,
    s <> fst l
    -> sat_lit (s, snd l) (upd a l)
    -> sat_clause cl a.
  unfold sat_lit, upd; simpl; intros.
  destruct (peq (snd l) (snd l)); intuition auto with *.
Qed.

#[local] Hint Resolve sat_lit_contra : core.

Ltac magic_solver := simpl; intros; subst; intuition eauto; firstorder;
                     match goal with
                     | [ H1 : sat_lit ?l ?a, H2 : sat_clause ?cl ?a |- _ ] =>
                       assert (sat_clause cl (upd a l)); firstorder
                     end.

(** Strongly-specified function to update a clause to reflect the effect of
  making a particular literal true.  *)
Definition set_clause : forall (cl : clause) (l : lit),
    {cl' : clause |
      forall a, sat_clause cl (upd a l) <-> sat_clause cl' a}
    + {forall a, sat_lit l a -> sat_clause cl a}.
  refine (fix set_clause (cl: clause) (l: lit) {struct cl} :=
            match cl with
            | nil => inleft (exist _ nil _)
            | x :: xs =>
              match set_clause xs l with
              | inright p => inright _
              | inleft (exist _ cl' H) =>
                match peq (snd x) (snd l), bool_eq_dec (fst x) (fst l) with
                | left p_eq, left bool_eq => inright _
                | left eq, right ne => inleft (exist _ cl' _)
                | right neq, _ => inleft (exist _ (x :: cl') _)
                end
              end
            end); clear set_clause; try magic_solver.
  - intros; simpl; left; apply injective_projections in bool_eq; subst; auto.
  - split; intros. simpl in H0. inversion H0. eapply sat_lit_contra; eauto.
    destruct x; simpl in *; subst. auto.
    apply H. eauto.
    simpl. right. apply H; eauto.
  - split; intros; simpl in *. inversion H0. destruct x; simpl in *; subst.
    left. eauto.
    right. apply H. eauto.
    inversion H0. left. apply sat_lit_upd_neq2. auto. auto.
    right. apply H. auto.
Defined.

(** For testing purposes, we define a weakly-specified function as a thin
  wrapper around [set_clause].
 *)
Definition set_clause_simple (cl : clause) (l : lit) :=
  match set_clause cl l with
  | inleft (exist _ cl' _) => Some cl'
  | inright _ => None
  end.

(*Eval compute in set_clause_simple ((false, 1%nat) :: nil) (true, 1%nat).*)
(*Eval compute in set_clause_simple nil (true, 0).
Eval compute in set_clause_simple ((true, 0) :: nil) (true, 0).
Eval compute in set_clause_simple ((true, 0) :: nil) (false, 0).
Eval compute in set_clause_simple ((true, 0) :: nil) (true, 1).
Eval compute in set_clause_simple ((true, 0) :: nil) (false, 1).
Eval compute in set_clause_simple ((true, 0) :: (true, 1) :: nil) (true, 1).
Eval compute in set_clause_simple ((true, 0) :: (true, 1) :: nil) (false, 1).
Eval compute in set_clause_simple ((true, 0) :: (false, 1) :: nil) (true, 1).
Eval compute in set_clause_simple ((true, 0) :: (false, 1) :: nil) (false, 1).*)

(** It's useful to have this strongly-specified nilness check. *)
Definition isNil : forall (A : Set) (ls : list A), {ls = nil} + {ls <> nil}.
  destruct ls; [left|right]; [auto|]; unfold not; intros; inversion H.
Defined.
Arguments isNil [A].

(** Some more lemmas that I found helpful.... *)

Lemma sat_lit_idem_lit : forall l a l',
    sat_lit l a
    -> sat_lit l' a
    -> sat_lit l' (upd a l).
  unfold sat_lit, upd; simpl; intros.
  destruct (peq (snd l') (snd l)); congruence.
Qed.

#[local] Hint Resolve sat_lit_idem_lit : core.

Lemma sat_lit_idem_clause : forall l a cl,
    sat_lit l a
    -> sat_clause cl a
    -> sat_clause cl (upd a l).
  induction cl; simpl; intuition.
Qed.

#[local] Hint Resolve sat_lit_idem_clause : core.

Lemma sat_lit_idem_formula : forall l a fm,
    sat_lit l a
    -> sat_formula fm a
    -> sat_formula fm (upd a l).
  induction fm; simpl; intuition.
Qed.

#[local] Hint Resolve sat_lit_idem_formula : core.

(** Function that updates an entire formula to reflect setting a literal to true.  *)
Definition set_formula : forall (fm : formula) (l : lit),
    {fm' : formula |
      forall a, sat_formula fm (upd a l) <-> sat_formula fm' a}
    + {forall a, sat_lit l a -> ~sat_formula fm a}.
  refine (fix set_formula (fm: formula) (l: lit) {struct fm} :=
            match fm with
            | nil => inleft (exist _ nil _)
            | cl' :: fm' =>
              match set_formula fm' l with
              | inright p => inright _
              | inleft (exist _ fm'' H) =>
                match set_clause cl' l with
                | inright H' => inleft (exist _ fm'' _)
                | inleft (exist _ cl'' _) =>
                  if isNil cl''
                  then inright _
                  else inleft (exist _ (cl'' :: fm'') _)
                end
              end
            end); clear set_formula; magic_solver.
Defined.

Definition set_formula_simple (fm : formula) (l : lit) :=
  match set_formula fm l with
  | inleft (exist _ fm' _) => Some fm'
  | inright _ => None
  end.

(* Eval compute in set_formula_simple (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil) (true, 1%nat). *)
(* Eval compute in set_formula_simple nil (true, 0). *)
(* Eval compute in set_formula_simple (((true, 0) :: nil) :: nil) (true, 0). *)
(* Eval compute in set_formula_simple (((false, 0) :: nil) :: nil) (true, 0). *)
(* Eval compute in set_formula_simple (((false, 1) :: nil) :: nil) (true, 0). *)
(* Eval compute in set_formula_simple (((false, 1) :: (true, 0) :: nil) :: nil) (true, 0). *)
(* Eval compute in set_formula_simple (((false, 1) :: (false, 0) :: nil) :: nil) (true, 0). *)

#[local] Hint Extern 1 False => discriminate : core.

Local Hint Extern 1 False =>
match goal with
| [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
end : core.

(** Code that either finds a unit clause in a formula or declares that there are none.  *)
Definition find_unit_clause : forall (fm: formula),
    {l : lit | In (l :: nil) fm}
    + {forall l, ~In (l :: nil) fm}.
  refine (fix find_unit_clause (fm: formula) {struct fm} :=
            match fm with
            | nil => inright _
            | (l :: nil) :: fm' => inleft (exist _ l _)
            | _ :: fm' =>
              match find_unit_clause fm' with
              | inleft (exist _ l _) => inleft (exist _ l _)
              | inright H => inright _
              end
            end
         ); clear find_unit_clause; magic_solver.
Defined.

(** The literal in a unit clause must always be true in a satisfying assignment.  *)
Lemma unit_clause_true : forall l a fm,
    In (l :: nil) fm
    -> sat_formula fm a
    -> sat_lit l a.
  induction fm; intuition auto with *.
  inversion H.
  inversion H; subst; simpl in H0; intuition.
  apply IHfm; eauto. inv H0. eauto.
Qed.

#[local] Hint Resolve unit_clause_true : core.

(** Unit propagation.  The return type of [unit_propagate] signifies that three
results are possible:

  - [None]: There are no unit clauses.
  - [Some (inleft _)]: There is a unit clause, and here is a formula reflecting
    setting its literal to true.
  - [Some (inright _)]: There is a unit clause, and propagating it reveals that
    the formula is unsatisfiable.
 *)
Definition unit_propagate :
  forall (fm : formula), option (sigT (fun fm' : formula =>
                                         {l : lit |
                                           (forall a, sat_formula fm a -> sat_lit l a)
                                           /\ forall a, sat_formula fm (upd a l) <-> sat_formula fm' a})
                                 + {forall a, ~sat_formula fm a}).
  refine (fix unit_propagate (fm: formula) {struct fm} :=
            match find_unit_clause fm with
            | inright H => None
            | inleft (exist _ l _) =>
              match set_formula fm l with
              | inright _ => Some (inright _)
              | inleft (exist _ fm' _) =>
                Some (inleft (existT _ fm' (exist _ l _)))
              end
            end
         ); clear unit_propagate; magic_solver.
Defined.


Definition unit_propagate_simple (fm : formula) :=
  match unit_propagate fm with
  | None => None
  | Some (inleft (existT _ fm' (exist _ l _))) => Some (Some (fm', l))
  | Some (inright _) => Some None
  end.

(*Eval compute in unit_propagate_simple (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil).
Eval compute in unit_propagate_simple nil.
Eval compute in unit_propagate_simple (((true, 0) :: nil) :: nil).
Eval compute in unit_propagate_simple (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in unit_propagate_simple (((true, 0) :: nil) :: ((false, 1) :: nil) :: nil).
Eval compute in unit_propagate_simple (((true, 0) :: nil) :: ((false, 0) :: (false, 1) :: nil) :: nil).
Eval compute in unit_propagate_simple (((false, 0) :: (false, 1) :: nil) :: ((true, 0) :: nil) :: nil).*)


(** * The SAT Solver *)

(** This section defines a DPLL SAT solver in terms of the subroutines.  *)

(** An arbitrary heuristic to choose the next variable to split on *)
Definition choose_split (fm : formula) :=
  match fm with
  | ((l :: _) :: _) => l
  | _ => (true, 1)
  end.

Definition negate (l : lit) := (negb (fst l), snd l).

#[local] Hint Unfold sat_formula : core.

Lemma sat_lit_dec : forall l a,
    {sat_lit l a} + {sat_lit (negate l) a}.
  destruct l.
  unfold sat_lit; simpl; intro.
  destruct b; destruct (a v); simpl; auto.
Qed.

(** We'll represent assignments as lists of literals instead of functions. *)
Definition alist := list lit.

Fixpoint interp_alist (al : alist) : asgn :=
  match al with
  | nil => fun _ => true
  | l :: al' => upd (interp_alist al') l
  end.

(*Eval compute in boundedSat_simple 100 nil.
Eval compute in boundedSat_simple 100 (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil).
Eval compute in boundedSat_simple 100 (((true, 0) :: nil) :: nil).
Eval compute in boundedSat_simple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in boundedSat_simple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSat_simple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil).
Eval compute in boundedSat_simple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSat_simple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil).*)

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
  forall (cl: clause) l, In l cl -> exists H, set_clause cl l = inright H.
Proof.
  induction cl; intros; simpl in *; try contradiction.
  destruct (set_clause cl l) eqn:?; [|econstructor; eauto].
  destruct s. inversion H; subst. clear H.
  destruct (peq (snd l) (snd l)); [| contradiction].
  destruct (bool_eq_dec (fst l) (fst l)); [| contradiction].
  econstructor. eauto. apply IHcl in H0.
  inversion H0. rewrite H1 in Heqs. discriminate.
Qed.

Lemma sat_measure_set_clause' :
  forall cl cl' l A,
    set_clause cl l = inleft (exist _ cl' A) ->
    ~ In (snd l) (map snd cl').
Proof.
  induction cl; intros.
  { simpl in *. inv H. unfold not in *. intros. inv H. }
  simpl in H.
  repeat (destruct_match; crush; []). destruct_match.
  repeat (destruct_match; crush; []). inv H. eapply IHcl; eauto.
  inv H. unfold not. intros. inv H. contradiction. eapply IHcl; eauto.
Qed.

Lemma sat_measure_set_clause'' :
  forall cl cl' l A,
    set_clause cl l = inleft (exist _ cl' A) ->
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

Lemma sat_formulaHasEmpty :
  forall fm,
    In nil fm ->
    forall a, ~ sat_formula fm a.
Proof.
  induction fm; crush.
  unfold not; intros. inv H0. inv H; auto.
  eapply IHfm; eauto.
Qed.

Lemma InFm_choose_split :
  forall l b c,
    InFm (snd (choose_split ((l :: b) :: c))) ((l :: b) :: c).
Proof.
  simpl; intros. destruct l; cbn.
  exists ((b0, v) :: b). exists b0.
  split; constructor; auto.
Qed.

Lemma InFm_negated_choose_split :
  forall l b c,
    InFm (snd (negate (choose_split ((l :: b) :: c)))) ((l :: b) :: c).
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

Lemma sat_measure_set_clause :
  forall cl cl' l b A,
    (forall b', ~ In (b', l) cl) ->
    set_clause cl (b, l) = inleft (exist _ cl' A) ->
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

Lemma sat_measure_set_clause_In_neq :
  forall cl cl' l v b A,
    In v (map snd cl) ->
    set_clause cl (b, l) = inleft (exist _ cl' A) ->
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

Lemma sat_measure_set_clause_In_rev :
  forall cl cl' l v b A,
    In v (map snd cl') ->
    set_clause cl (b, l) = inleft (exist _ cl' A) ->
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

Lemma sat_measure_set_clause_In_neq2 :
  forall cl cl' l b A,
    set_clause cl (b, l) = inleft (exist _ cl' A) ->
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

Lemma sat_measure_set_clause_In :
  forall cl cl' l b A,
    In l (map snd cl) ->
    set_clause cl (b, l) = inleft (exist _ cl' A) ->
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
        -- apply sat_measure_set_clause in Heqs; [|now apply in_map_snd_forall].
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
      * exploit sat_measure_set_clause_In_neq. eapply i0. eauto. auto. intros.
        contradiction.
      * apply lit_set_cl_in_set in i0. apply lit_set_cl_not_in_set in n0.
        rewrite PSetProp.P.add_cardinal_1 by auto.
        rewrite PSetProp.P.add_cardinal_2 by auto. unfold lit_set_cl in *; lia.
      * apply lit_set_cl_not_in_set in n0. apply lit_set_cl_not_in_set in n1.
        repeat rewrite PSetProp.P.add_cardinal_2 by auto.
        unfold lit_set_cl in *; lia.
Qed.

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
    set_clause cl (b, v) = inleft (exist _ cl' A) ->
    PSet.Equal (lit_set_cl cl) (PSet.add v (lit_set_cl cl')).
Proof.
  constructor; intros.
  - destruct (peq a v); subst.
    + apply PSetProp.P.FM.add_1; auto.
    + apply PSetProp.P.FM.add_2.
      apply lit_set_cl_in_set2 in H1. apply lit_set_cl_in_set.
      eapply sat_measure_set_clause_In_neq; eauto.
  - apply PSet.add_spec in H1. inv H1.
    + apply lit_set_cl_in_set; auto.
    + apply lit_set_cl_in_set. apply lit_set_cl_in_set2 in H2.
      eapply sat_measure_set_clause_In_rev; eauto.
Qed.

Lemma lit_set_cl_neq :
  forall cl v b cl' A,
    ~ In v (map snd cl) ->
    set_clause cl (b, v) = inleft (exist _ cl' A) ->
    PSet.Equal (lit_set_cl cl) (lit_set_cl cl').
Proof.
  constructor; intros.
  - erewrite <- sat_measure_set_clause; eauto.
    intros. unfold not; intros. apply H.
    replace v with (snd (b', v)) by auto; apply in_map; auto.
  - erewrite sat_measure_set_clause; eauto.
    intros. unfold not; intros. apply H.
    replace v with (snd (b', v)) by auto; apply in_map; auto.
Qed.

Lemma sat_measure_set_formula1 :
  forall fm fm' l b A,
    set_formula fm (b, l) = inleft (exist _ fm' A) ->
    ~ InFm l fm'.
Proof.
  induction fm.
  - intros. inv H. unfold not. intros. destruct H as (cl & b0 & H1 & H2). inv H1.
  - intros. unfold sat_measure, lit_set.
    cbn in H. repeat (destruct_match; try discriminate; []).
    destruct_match; repeat (destruct_match; try discriminate; []); inv H.
    + eapply IHfm in Heqs.
      assert (~ In l (map snd x0))
        by (eapply sat_measure_set_clause_In_neq2; eauto).
      unfold not; intros.
      apply InFm_cons in H0. inv H0; auto. inv H1.
      apply H. replace l with (snd (x1, l)) by auto. apply in_map; auto.
    + eapply IHfm in Heqs. auto.
Qed.

Lemma sat_measure_set_formula2 :
  forall fm fm' l v b A,
    InFm v fm' ->
    set_formula fm (b, l) = inleft (exist _ fm' A) ->
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
        exploit sat_measure_set_clause_In_rev; eauto; intros.
        apply list_in_map_inv in H. destruct H as (c & H1 & H2). destruct c. inv H1.
        cbn. exists a. exists b1. intuition auto with *.
      * exploit IHfm; eauto; intros. eapply InFm_cons2; tauto.
    + exploit IHfm; eauto; intros. eapply InFm_cons2; tauto.
  Unshelve.
  all: exact true.
Qed.

Lemma sat_measure_set_formula3 :
  forall fm fm' l b A,
    set_formula fm (b, l) = inleft (exist _ fm' A) ->
    PSet.Subset (lit_set fm') (lit_set fm).
Proof.
  unfold PSet.Subset; intros.
  apply lit_set_in_set.
  apply lit_set_in_set2 in H0.
  eapply sat_measure_set_formula2; eauto.
Qed.

Lemma sat_measure_set_formula :
  forall fm fm' l b A,
    InFm l fm ->
    set_formula fm (b, l) = inleft (exist _ fm' A) ->
    (sat_measure fm' < sat_measure fm)%nat.
Proof.
  intros. unfold sat_measure.
  apply PSetProp.P.subset_cardinal_lt with (x:=l).
  eapply sat_measure_set_formula3; eauto.
  now apply lit_set_in_set.
  unfold not; intros.
  eapply sat_measure_set_formula1. eauto.
  now apply lit_set_in_set2 in H1.
Qed.

Lemma sat_measure_propagate_unit :
  forall fm' fm H,
    unit_propagate fm = Some (inleft (existT _ fm' H)) ->
    (sat_measure fm' < sat_measure fm)%nat.
Proof.
  unfold unit_propagate; intros. cbn in *.
  destruct fm; intros. crush.
  repeat (destruct_match; try discriminate; []). inv H0.
  destruct x.
  eapply sat_measure_set_formula; eauto.
  cbn in i. clear Heqs. clear H3. inv i.
  eexists. exists b. split. constructor. auto. now constructor.
  exists ((b, v) :: nil). exists b. split.
  apply in_cons. auto. now constructor.
Qed.

Program Fixpoint sat_solve (fm: formula) { measure (sat_measure fm) }:
  {al : alist | sat_formula fm (interp_alist al)} + {forall a, ~sat_formula fm a} :=
  match isNil fm with
  | left fmIsNil => inleft _ (exist _ nil _)
  | right fmIsNotNil =>
    match hasNoNil fm with
    | left hasNilfm => inright _ _
    | right hasNoNilfm =>
      match unit_propagate fm with
      | Some (inleft (existT _ fm' (exist _ l _))) =>
        match sat_solve fm' with
        | inleft (exist _ al _) => inleft _ (exist _ (l :: al) _)
        | inright _ => inright _ _
        end
      | Some (inright _) => inright _ _
      | None =>
        let l := choose_split fm in
        match set_formula fm l with
        | inleft (exist _ fm' _) =>
          match sat_solve fm' with
          | inleft (exist _ al _) => inleft _ (exist _ (l :: al) _)
          | inright _ =>
            match set_formula fm (negate l) with
            | inleft (exist _ fm' _) =>
              match sat_solve fm' with
              | inleft (exist _ al _) => inleft _ (exist _ (negate l :: al) _)
              | inright _ => inright _ _
              end
            | inright _ => inright _ _
            end
          end
        | inright _ =>
          match set_formula fm (negate l) with
          | inleft (exist _ fm' _) =>
            match sat_solve fm' with
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
  apply sat_formulaHasEmpty; assumption. Defined.
Next Obligation.
  eapply sat_measure_propagate_unit; eauto. Defined.
Next Obligation.
  apply i; auto. Defined.
Next Obligation.
  unfold not; intros; eapply wildcard'; apply i; eauto. Defined.
Next Obligation.
  intros. symmetry in Heq_anonymous.
  destruct (choose_split fm) eqn:?.
  apply sat_measure_set_formula in Heq_anonymous; auto. unfold isNil in *.
  destruct fm; try discriminate.
  assert (c <> nil).
  { unfold not; intros. apply hasNoNilfm. constructor; auto. }
  destruct c; try discriminate.
  replace p with (snd (b, p)) by auto. rewrite <- Heqp.
  apply InFm_choose_split. Defined.
Next Obligation.
  apply wildcard'0; auto. Defined.
Next Obligation.
  eapply sat_measure_set_formula; eauto.
  destruct fm; try discriminate. destruct c; try discriminate.
  apply InFm_choose_split. Defined.
Next Obligation.
  apply wildcard'2; auto. Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (sat_lit_dec (choose_split fm) a);
  [assert (sat_formula fm (upd a (choose_split fm)))
  | assert (sat_formula fm (upd a (negate (choose_split fm))))]; auto.
  { eapply wildcard'1. apply wildcard'0; eauto. }
  { eapply wildcard'. apply wildcard'2; eauto. }
Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (sat_lit_dec (choose_split fm) a);
  [assert (sat_formula fm (upd a (choose_split fm)))
  | assert (sat_formula fm (upd a (negate (choose_split fm))))]; auto.
  { eapply wildcard'1. eapply wildcard'0. eauto. }
  { eapply wildcard'; eauto. }
Defined.
Next Obligation.
  eapply sat_measure_set_formula; eauto.
  destruct fm; try discriminate. destruct c; try discriminate.
  apply InFm_choose_split. Defined.
Next Obligation.
  apply wildcard'1; auto. Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (sat_lit_dec (choose_split fm) a);
  [assert (sat_formula fm (upd a (choose_split fm)))
  | assert (sat_formula fm (upd a (negate (choose_split fm))))]; auto.
  { eapply wildcard'0; eauto. }
  { eapply wildcard'; apply wildcard'1; eauto. }
Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (sat_lit_dec (choose_split fm) a).
  { eapply wildcard'0; eauto. }
  { eapply wildcard'; eauto. }
Defined.

Definition sat_solve_simple (fm : formula) :=
  match sat_solve fm with
  | inleft (exist _ a _) => Some a
  | inright _ => None
  end.
