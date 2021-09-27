(** Homework Assignment 6#<br>#
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

(** Submit your solution file for this assignment as an attachment
  #<a href="mailto:adamc@cs.berkeley.edu?subject=ICTP HW6">#by e-mail#</a># with
  the subject "ICTP HW6" by the start of class on October 12.
  You should write your solutions entirely on your own, which includes not
  consulting any solutions to these problems that may be posted on the web.

  #<a href="HW6.v">#Template source file#</a>#
  *)

Require Import Arith Bool List.

(** This assignment involves building a certified boolean satisfiability solver
  based on the DPLL algorithm.  Your certified procedure will take as input a
  boolean formula in conjunctive normal form (CNF) and either return a
  satisfying assignment to the variables or a value signifying that the input
  formula is unsatisfiable.  Moreover, the procedure will be implemented with a
  rich specification, so you'll know that the answer it gives is correct.  By
  the end of the assignment, you'll have extracted OCaml code that can be used
  to solve some of the more modest classes of problems in the SATLIB archive.

  If you need to page in the relevant background material, try the Wikipedia
  pages on
  #<a href="http://en.wikipedia.org/wiki/Boolean_satisfiability_problem">#SAT#</a>#
  and
  #<a href="http://en.wikipedia.org/wiki/DPLL_algorithm">#the DPLL
  algorithm#</a>#.  The implementation we'll develop here omits the pure literal
  heuristic mentioned on the Wikipedia page but is otherwise identical.
  *)


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

(** This is the only section of this assignment where you need to provide your
  own solutions.  You will be implementing four crucial subroutines used by
  DPLL.

  I've provided a number of useful definitions and lemmas which you should feel
  free to take advantage of in your definitions.  A few tips to keep in mind
  while writing these strongly specified functions:
  - You have a case-by-case choice of a "programming" approach, based around the
    [refine] tactic; or a "proving" approach, where the "code" parts of your
    definitions are constructed step by step with tactics.  The former is often
    harder to get started with, but it tends to be more maintainable.
  - When you use [refine] with a [fix] expression, it's usually a good idea to
    use the [clear] tactic to remove the recursive function name from the
    context immediately afterward.  This is because Coq won't check that you
    call this function with strictly smaller arguments until the whole proof is
    done, and it's a real downer to be told you had an invalid recursion
    somewhere after you finally "finish" a proof.  Instead, make all recursive
    calls explicit in the [refine] argument and clear the function name
    afterward.
  - You'll probably end up with a lot of proof obligations to discharge, and you
    definitely won't want to prove most of them manually.  These tactics will
    probably be your best friends here: [intuition], [firstorder], [eauto],
    [simpl], [subst], ....  You will probably want to follow your [refine] tactics
    with semicolons and strings of semicolon-separated tactics.  These strings
    should probably start out with basic simplifiers like [intros], [simpl], and
    [subst].
  - A word of warning about the [firstorder] tactic: When it works, it works
    really well!  However, this tactic has a way of running forever on
    complicated enough goals.  Be ready to cancel its use (e.g., press the
    "Stop" button in Proof General) if it takes more than a few seconds.  If
    you do things the way I have, be prepared to mix and match all sorts of
    different combinations of the automating tactics to get a proof script that
    solves the problem quickly enough.
  - The dependent type families that we use with rich specifications are all
    defined in #<a href="http://coq.inria.fr/library/Coq.Init.Specif.html">#the
    Specif module#</a># of the Coq standard library.  One potential gotcha when
    using them comes from the fact that they are defined inductively with
    parameters; that is, some arguments to these type families are defined
    before the colon in the [Inductive] command.  Compared to general arguments
    stemming from function types after that colon, usage of parameters is
    restricted; they aren't allowed to vary in recursive occurrences of the
    type being defined, for instance.  Because of this, parameters are ignored
    for the purposes of pattern-matching, while they must be passed when
    actually constructing new values.  For instance, one would pattern-match a
    value of a [sig] type with a pattern like [exist x pf], while one would
    construct a new value of the same type like [exist _ x pf].  The parameter
    [P] is passed in the second case, and we use an underscore when the Coq
    type-checker ought to be able to infer its value.  When this inference isn't
    possible, you may need to specify manually the predicate defining the [sig]
    type you want.

  You can also consult the sizeable example at the end of this file, which ties
  together the pieces you are supposed to write.
  *)

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

Local Hint Resolve contradictory_assignment : core.

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

Local Hint Resolve satLit_upd_eq : core.

Lemma satLit_upd_neq : forall v l s a,
  v <> snd l
  -> satLit (s, v) (upd a l)
  -> satLit (s, v) a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

Local Hint Resolve satLit_upd_neq : core.

Lemma satLit_upd_neq2 : forall v l s a,
  v <> snd l
  -> satLit (s, v) a
  -> satLit (s, v) (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

Local Hint Resolve satLit_upd_neq2 : core.

Lemma satLit_contra : forall s l a cl,
  s <> fst l
  -> satLit (s, snd l) (upd a l)
  -> satClause cl a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); intuition.
  assert False; intuition.
Qed.

Local Hint Resolve satLit_contra : core.

(** Here's the tactic that I used to discharge #<i>#all#</i># proof obligations
  in my implementations of the four functions you will define.
  It comes with no warranty, as different implementations may lead to
  obligations that it can't solve, or obligations that it takes 42 years to
  solve.
  However, if you think enough like me, each of the four definitions you fill in
  should read like:
refine some_expression_with_holes; clear function_name; magic_solver.
 leaving out the [clear] invocation for non-recursive function definitions.
  *)
Ltac magic_solver := simpl; intros; subst; intuition eauto; firstorder;
  match goal with
    | [ H1 : satLit ?l ?a, H2 : satClause ?cl ?a |- _ ] =>
      assert (satClause cl (upd a l)); firstorder
  end.

(** OK, here's your first challenge.  Write this strongly-specified function to
  update a clause to reflect the effect of making a particular literal true.
  *)
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

(** When your [setClause] implementation is done, you should be able to
  uncomment these test cases and verify that each one yields the correct answer.
  Be sure that your [setClause] definition ends in [Defined] and not [Qed], as
  the former exposes the definition for use in computational reduction, while
  the latter doesn't.
  *)

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
Definition isNil : forall (A : Set) (ls : list A), {ls = nil} + {True}.
  destruct ls; [left|right]; eauto.
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

Local Hint Resolve satLit_idem_lit : core.

Lemma satLit_idem_clause : forall l a cl,
  satLit l a
  -> satClause cl a
  -> satClause cl (upd a l).
  induction cl; simpl; intuition.
Qed.

Local Hint Resolve satLit_idem_clause : core.

Lemma satLit_idem_formula : forall l a fm,
  satLit l a
  -> satFormula fm a
  -> satFormula fm (upd a l).
  induction fm; simpl; intuition.
Qed.

Local Hint Resolve satLit_idem_formula : core.

(** Challenge 2: Write this function that updates an entire formula to reflect
  setting a literal to true.
  *)
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
            end); clear setFormula; try solve [magic_solver].
Defined.

(** Here's some code for testing your implementation. *)

Definition setFormulaSimple (fm : formula) (l : lit) :=
  match setFormula fm l with
    | inleft (exist _ fm' _) => Some fm'
    | inright _ => None
  end.

(*Eval compute in setFormulaSimple (((true, 1%nat) :: nil) :: ((false, 1%nat) :: nil) :: nil) (true, 1%nat).
Eval compute in setFormulaSimple nil (true, 0).
Eval compute in setFormulaSimple (((true, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: (true, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: (false, 0) :: nil) :: nil) (true, 0).*)

Local Hint Extern 1 False => discriminate : core.

Local Hint Extern 1 False =>
  match goal with
    | [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
  end : core.

(** Challenge 3: Write this code that either finds a unit clause in a formula
  or declares that there are none.
  *)
Definition findUnitClause : forall (fm: formula),
  {l : lit | In (l :: nil) fm}
  + {forall l, ~In (l :: nil) fm}.
  refine (fix findUnitClause (fm: formula) {struct fm} :=
            match fm with
            | nil => inright _
            | (l :: nil) :: fm' => inleft (exist _ l _)
            | cl :: fm' =>
              match findUnitClause fm' with
              | inleft (exist _ l _) => inleft (exist _ l _)
              | inright H => inright _
              end
            end
         ); clear findUnitClause; magic_solver.
Defined.

(** The literal in a unit clause must always be true in a satisfying
  assignment.
  *)
Lemma unitClauseTrue : forall l a fm,
  In (l :: nil) fm
  -> satFormula fm a
  -> satLit l a.
  induction fm; intuition.
  inversion H.
  inversion H; subst; simpl in H0; intuition.
Qed.

Local Hint Resolve unitClauseTrue : core.

(** Final challenge: Implement unit propagation.  The return type of
  [unitPropagate] signifies that three results are possible:
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

(** This section defines a DPLL SAT solver in terms of the subroutines you've
  written.
  *)

(** An arbitrary heuristic to choose the next variable to split on *)
Definition chooseSplit (fm : formula) :=
  match fm with
    | ((l :: _) :: _) => l
    | _ => (true, 0)
  end.

Definition negate (l : lit) := (negb (fst l), snd l).

Local Hint Unfold satFormula : core.

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

(** Here's the final definition!  This is not the way you should write proof
  scripts. ;-)

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
