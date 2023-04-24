(**
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

Require Import Arith Bool List.
Require Import Coq.funind.Recdef.
Require Coq.MSets.MSetList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Program.Wf.
Require Import Vericertlib.

Module Nat_OT := Update_OT Nat_as_OT.
Module NSet := MSetList.Make Nat_OT.

#[local] Open Scope nat.

(** * Problem Definition *)

Definition var := nat.
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
    if eq_nat_dec v (snd l)
    then fst l
    else a v.

(** Some lemmas about [upd] *)

Lemma satLit_upd_eq : forall l a,
    satLit l (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); tauto.
Qed.

#[local] Hint Resolve satLit_upd_eq : core.

Lemma satLit_upd_neq : forall v l s a,
    v <> snd l
    -> satLit (s, v) (upd a l)
    -> satLit (s, v) a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

#[local] Hint Resolve satLit_upd_neq : core.

Lemma satLit_upd_neq2 : forall v l s a,
    v <> snd l
    -> satLit (s, v) a
    -> satLit (s, v) (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

#[local] Hint Resolve satLit_upd_neq2 : core.

Lemma satLit_contra : forall s l a cl,
    s <> fst l
    -> satLit (s, snd l) (upd a l)
    -> satClause cl a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); intuition.
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
                match eq_nat_dec (snd x) (snd l), bool_eq_dec (fst x) (fst l) with
                | left nat_eq, left bool_eq => inright _
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
  destruct (eq_nat_dec (snd l') (snd l)); congruence.
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
  induction fm; intuition.
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
  | _ => (true, 0)
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

(** Here's the final definition!

  This implementation isn't #<i>#quite#</i># what you would expect, since it
  takes an extra parameter expressing a search tree depth.  Writing the function
  without that parameter would be trickier when it came to proving termination.
  In practice, you can just seed the bound with one plus the number of variables
  in the input, but the function's return type still indicates a possibility for
  a "time-out" by returning [None].
 *)
Definition boundedSat: forall (bound : nat) (fm : formula),
    option ({al : alist | satFormula fm (interp_alist al)}
            + {forall a, ~satFormula fm a}).
  refine (fix boundedSat (bound : nat) (fm : formula) {struct bound}
          : option ({al : alist | satFormula fm (interp_alist al)}
                    + {forall a, ~satFormula fm a}) :=
            match bound with
            | O => None
            | S bound' =>
              if isNil fm
              then Some (inleft _ (exist _ nil _))
              else match unitPropagate fm with
                   | Some (inleft (existT _ fm' (exist _ l _))) =>
                     match boundedSat bound' fm' with
                     | None => None
                     | Some (inleft (exist _ al _)) => Some (inleft _ (exist _ (l :: al) _))
                     | Some (inright _) => Some (inright _ _)
                     end
                   | Some (inright _) => Some (inright _ _)
                   | None =>
                     let l := chooseSplit fm in
                     match setFormula fm l with
                     | inleft (exist _ fm' _) =>
                       match boundedSat bound' fm' with
                       | None => None
                       | Some (inleft (exist _ al _)) => Some (inleft _ (exist _ (l :: al) _))
                       | Some (inright _) =>
                         match setFormula fm (negate l) with
                         | inleft (exist _ fm' _) =>
                           match boundedSat bound' fm' with
                           | None => None
                           | Some (inleft (exist _ al _)) => Some (inleft _ (exist _ (negate l :: al) _))
                           | Some (inright _) => Some (inright _ _)
                           end
                         | inright _ => Some (inright _ _)
                         end
                       end
                     | inright _ =>
                       match setFormula fm (negate l) with
                       | inleft (exist _ fm' _) =>
                         match boundedSat bound' fm' with
                         | None => None
                         | Some (inleft (exist _ al _)) => Some (inleft _ (exist _ (negate l :: al) _))
                         | Some (inright _) => Some (inright _ _)
                         end
                       | inright _ => Some (inright _ _)
                       end
                     end
                   end
            end); simpl; intros; subst; intuition; try generalize dependent (interp_alist al).
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  assert (satFormula fm (upd a0 l)); firstorder.
  assert (satFormula fm (upd a0 l)); firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l)) | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l)) | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l)) | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l)) | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a l)); firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a l)); firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a (negate l))); firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a (negate l))); firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l)) | assert (satFormula fm (upd a (negate l)))]; firstorder.
Defined.

Definition boundedSatSimple (bound : nat) (fm : formula) :=
  match boundedSat bound fm with
  | None => None
  | Some (inleft (exist _ a _)) => Some (Some a)
  | Some (inright _) => Some None
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
  fold_right NSet.add NSet.empty (map snd cl).

Definition lit_set (fm: formula) :=
  fold_right NSet.union NSet.empty (map lit_set_cl fm).

(* Compute NSet.cardinal (lit_set (((true, 1)::(true, 1)::(true, 1)::nil)::nil)). *)

Definition sat_measure (fm: formula) := NSet.cardinal (lit_set fm).

Lemma elim_clause :
  forall (cl: clause) l, In l cl -> exists H, setClause cl l = inright H.
Proof.
  induction cl; intros; simpl in *; try contradiction.
  destruct (setClause cl l) eqn:?; [|econstructor; eauto].
  destruct s. inversion H; subst. clear H.
  destruct (Nat.eq_dec (snd l) (snd l)); [| contradiction].
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

Lemma sat_measure_setClause2'' :
  forall cl cl' l A,
    setClause cl l = inleft (exist _ cl' A) ->
    forall l',
      l' <> snd l ->
      In l' (map snd cl') ->
      In l' (map snd cl).
Proof.
  induction cl; intros.
  { cbn in *. inv H. cbn in *. auto. }
  exploit IHcl; eauto.
  Admitted.

Lemma sat_measure_setClause :
  forall cl cl' l A,
    In (snd l) (map snd cl) ->
    setClause cl l = inleft (exist _ cl' A) ->
    NSet.cardinal (lit_set_cl cl') < NSet.cardinal (lit_set_cl cl).
Proof.
  intros. pose proof H0. apply sat_measure_setClause' in H0.
  pose proof (sat_measure_setClause'' _ _ _ _ H1).
Admitted.

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

Lemma sat_measure_setFormula :
  forall fm fm' l b A,
    InFm l fm ->
    setFormula fm (b, l) = inleft (exist _ fm' A) ->
    sat_measure fm' < sat_measure fm.
Proof. Admitted.

Lemma sat_measure_propagate_unit :
  forall fm' fm H,
    unitPropagate fm = Some (inleft (existT _ fm' H)) ->
    sat_measure fm' < sat_measure fm.
Proof.
  induction fm; crush.
  repeat (destruct_match; crush; []).
  destruct_match.
  repeat (destruct_match; crush; []).
  inv Heqs1.
  unfold sat_measure.
  Admitted.

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
  Admitted.
Next Obligation.
  apply wildcard'0; auto. Defined.
Next Obligation.
  eapply sat_measure_setFormula. admit. symmetry. eauto. Admitted.
Next Obligation.
  apply wildcard'2; auto. Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a);
  [assert (satFormula fm (upd a (chooseSplit fm)))
  | assert (satFormula fm (upd a (negate (chooseSplit fm))))]; firstorder.
  { eapply wildcard'1. apply wildcard'0; eauto. }
  { eapply wildcard'. apply wildcard'2; eauto. }
Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a);
  [assert (satFormula fm (upd a (chooseSplit fm)))
  | assert (satFormula fm (upd a (negate (chooseSplit fm))))]; firstorder.
  { eapply wildcard'1. eapply wildcard'0. eauto. }
  { eapply wildcard'; eauto. }
Defined.
Next Obligation.
  Admitted.
Next Obligation.
  apply wildcard'1; auto. Defined.
Next Obligation.
  unfold not in *; intros.
  destruct (satLit_dec (chooseSplit fm) a);
  [assert (satFormula fm (upd a (chooseSplit fm)))
  | assert (satFormula fm (upd a (negate (chooseSplit fm))))]; firstorder.
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
