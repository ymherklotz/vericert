(** This file contain the proof of the RTLdfs transformation. We show
both that the transformation ensures that generated functions are
satisfying the predicate [wf_dfs_function] and that the transformation
preserves the semantics. *)

Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import Smallstep.
Require Import DeadBlocks.
Require Import Kildall.
Require Import Conventions.
Require Import Integers.
Require Import Floats.
Require Import Utils.
Require Import Events.
Require Import Gible.
Require Import GibleSeq.
Require Import Relation_Operators.
Require Import Vericertlib.

Unset Allow StrictProp.

(** * The [cfg] predicate *)
Variant cfg (code:code) (i j:node) : Prop :=
  | CFG : forall ins
    (HCFG_ins: code!i = Some ins)
    (HCFG_in : In j (all_successors ins)),
    cfg code i j.

Inductive cfg_star (code:code) (i:node) : node -> Prop :=
| cfg_star0 : cfg_star code i i
| cfg_star1 : forall j k, cfg_star code i j -> cfg code j k -> cfg_star code i k.

Notation "R **" := (@clos_refl_trans _ R) (at level 30).

Lemma Rstar_refl : forall A R (i:A), R** i i.
Proof. constructor 2. Qed.

Lemma Rstar_R : forall A (R:A->A->Prop) (i j:A), R i j -> R** i j.
Proof. constructor 1; auto. Qed.

Lemma Rstar_trans : forall A (R:A->A->Prop) (i j k:A),
  R** i j -> R** j k -> R** i k.
Proof. intros A R i j k; constructor 3 with j; auto. Qed.

Global Hint Resolve Rstar_trans Rstar_refl Rstar_R: core.

Lemma star_eq : forall A (R1 R2:A->A->Prop),
  (forall i j, R1 i j -> R2 i j) ->
  forall i j, R1** i j -> R2** i j.
Proof.
  induction 2.
  econstructor 1; eauto.
  econstructor 2; eauto.
  econstructor 3; eauto.
Qed.

Lemma cfg_star_same_code: forall code1 code2 i,
  (forall k, cfg_star code1 i k -> code1!k = code2!k) ->
  forall j, cfg_star code1 i j -> cfg_star code2 i j.
Proof.
  induction 2.
  constructor 1.
  constructor 2 with j; auto.
  inv H1.
  rewrite H in *; auto.
  econstructor; eauto.
Qed.

Lemma cfg_star_same : forall code i j,
  cfg_star code i j <-> (cfg code)** i j.
Proof.
  split.
  induction 1.
  constructor 2.
  constructor 3 with j; auto.
  assert (forall i j, (cfg code0**) i j -> forall k, cfg_star code0 k i -> cfg_star code0 k j).
    clear i j; induction 1; auto.
    intros.
    constructor 2 with x; auto.
  intros; apply H with i; auto.
  constructor 1.
Qed.

(** * Utility lemmas *)
Section dfs.
Variable entry:node.
Variable code:code.

Lemma not_seen_sons_aux0 : forall l0 l1 l2 seen_set seen_set',
  fold_left
  (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
    let (new, seen) := ns in
      match seen ! j with
        | Some _ => ns
        | None => (j :: new, PTree.set j tt seen)
      end) l0 (l1, seen_set) = (l2, seen_set') ->
  forall x, In x l1 -> In x l2.
Proof.
  induction l0; simpl; intros.
  inv H; auto.
  destruct (seen_set!a); inv H; eauto with datatypes.
Qed.

Lemma not_seen_sons_prop1 : forall i j seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  cfg code i j -> In j l \/ seen_set ! j = Some tt.
Proof.
  unfold not_seen_sons; intros.
  inv H0.
  rewrite HCFG_ins in *.
  assert (
   forall l0 l1 l2 seen_set seen_set',
   fold_left
     (fun (ns : prod (list node) (PTree.t unit)) (j0 : positive) =>
      let (new, seen) := ns in
      match seen ! j0 with
      | Some _ => ns
      | None => (j0 :: new, PTree.set j0 tt seen)
      end) l0 (l1, seen_set) = (l2, seen_set') ->
   In j l0 -> In j l2 \/ seen_set ! j = Some tt).
  induction l0; simpl; intros.
  intuition.
  destruct (peq a j).
  subst.
  case_eq (seen_set0!j); intros.
  destruct u; auto.
  rewrite H2 in *.
  left; eapply not_seen_sons_aux0; eauto with datatypes.
  destruct H1.
  intuition.
  destruct (seen_set0!a); eauto.
  elim IHl0 with (1:=H0); auto.
  rewrite PTree.gso; auto.
  eauto.
Qed.

Lemma not_seen_sons_prop8 : forall i j seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  In j l -> cfg code i j.
Proof.
  unfold not_seen_sons; intros.
  assert (
   forall l0 l1 l2 seen_set seen_set',
   fold_left
     (fun (ns : prod (list node) (PTree.t unit)) (j0 : positive) =>
      let (new, seen) := ns in
      match seen ! j0 with
      | Some _ => ns
      | None => (j0 :: new, PTree.set j0 tt seen)
      end) l0 (l1, seen_set) = (l2, seen_set') ->
   In j l2 -> In j l0 \/ In j l1).
  induction l0; simpl; intros.
  inv H1; auto.
  case_eq (seen_set0!a); intros; rewrite H3 in *.
  elim IHl0 with (1:=H1); auto.
  elim IHl0 with (1:=H1); auto.
  simpl; destruct 1; auto.
  case_eq (code!i); intros; rewrite H2 in H.
  apply H1 in H; auto; clear H1.
  destruct H as [H|H]; try (elim H; fail).
  econstructor; eauto.
  inv H; elim H0.
Qed.

Lemma not_seen_sons_prop2 : forall i j seen_set,
  In j (fst (not_seen_sons code i seen_set)) ->
  seen_set ! j = None.
Proof.
  unfold not_seen_sons; intros.
  case_eq (code!i); [intros ins Hi|intros Hi]; rewrite Hi in *.
  assert (forall l l0 seen_set,
    In j
        (fst
           (fold_left
              (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
               let (new, seen) := ns in
               match seen ! j with
               | Some _ => ns
               | None => (j :: new, PTree.set j tt seen)
               end) l (l0, seen_set))) ->
        In j l0\/ seen_set ! j = None).
  induction l; simpl; auto.
  intros.
  case_eq (seen_set0 ! a); intros; rewrite H1 in *; eauto.
  elim IHl with (1:=H0); auto.
  simpl; destruct 1; subst; auto.
  rewrite PTree.gsspec; destruct peq; auto.
  intros; congruence.
  elim H0 with (1:=H); auto.
  simpl; intuition.
  simpl in H; intuition.
Qed.

Lemma not_seen_sons_prop5 : forall i seen_set,
  list_norepet (fst (not_seen_sons code i seen_set)).
Proof.
  unfold not_seen_sons; intros.
  destruct (code ! i); simpl; try constructor.
  assert (forall l l0 seen_set l1 seen_set',
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    (forall x, In x l0 -> seen_set!x = Some tt) ->
    list_norepet l0 ->
    (forall x, In x l1 -> seen_set'!x = Some tt) /\ list_norepet l1).
  induction l; simpl; intros.
  inv H ;auto.
  case_eq (seen_set0!a); intros; rewrite H2 in *; auto.
  elim IHl with (1:=H); auto.
  elim IHl with (1:=H); auto.
  simpl; destruct 1; auto.
  subst; rewrite PTree.gss; auto.
  rewrite PTree.gsspec; destruct peq; auto.
  constructor; auto.
  intro; rewrite (H0 a) in H2; auto; congruence.
  generalize (H (all_successors t) nil seen_set).
  destruct (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) (all_successors t) (nil, seen_set)); intuition.
  eelim H0; eauto.
  simpl; intuition.
  constructor.
Qed.

Lemma not_seen_sons_prop3_aux : forall l i l0 seen_set l1 seen_set',
    seen_set!i = Some tt ->
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    seen_set'!i = Some tt.
Proof.
 induction l; simpl; intros.
 inv H0; auto.
 destruct (seen_set!a).
 rewrite (IHl _ _ _ _ _ H H0); auto.
 assert ((PTree.set a tt seen_set)! i = Some tt).
 rewrite PTree.gsspec; destruct peq; auto.
 rewrite (IHl _ _ _ _ _ H1 H0); auto.
Qed.

Lemma not_seen_sons_prop3 : forall i seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  forall i, seen_set!i = Some tt -> seen_set'!i = Some tt.
Proof.
  unfold not_seen_sons; intros.
  destruct (code!i); inv H; auto.
  apply not_seen_sons_prop3_aux with (2:=H2); auto.
Qed.


Lemma not_seen_sons_prop4 : forall i seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  forall i, In i l -> seen_set'!i = Some tt.
Proof.
  unfold not_seen_sons; intros.
  destruct (code!i); inv H; auto.
  assert (forall l i l0 seen_set l1 seen_set',
    In i l1 ->
    (forall i, In i l0 -> seen_set !i = Some tt) ->
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    seen_set'!i = Some tt).
  induction l0; simpl; intros.
  inv H3; auto.
  case_eq (seen_set0 ! a); intros; rewrite H4 in *; inv H3.
  apply IHl0 with (3:= H6); auto.
  apply IHl0 with (3:= H6); auto.
  simpl; destruct 1; subst.
  rewrite PTree.gss; auto.
  rewrite PTree.gsspec; destruct peq; auto.
  apply H with (3:=H2); auto.
  simpl; intuition.
  elim H0.
Qed.

Lemma not_seen_sons_prop6 : forall i seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  forall i, seen_set'!i = Some tt -> seen_set!i = Some tt \/ In i l.
Proof.
  unfold not_seen_sons; intros.
  destruct (code!i); inv H; auto.
  assert (forall l i l0 seen_set l1 seen_set',
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    seen_set'!i = Some tt ->
    seen_set !i = Some tt \/ In i l1).
  induction l0; simpl; intros.
  inv H; auto.
  case_eq (seen_set0 ! a); intros; rewrite H3 in *; inv H.
  apply IHl0 with (1:= H5); auto.
  elim IHl0 with (1:= H5) (i:=i1); auto; intros.
  rewrite PTree.gsspec in H; destruct peq; auto.
  subst.
  right.
  eapply not_seen_sons_aux0; eauto with datatypes.
  apply H with (1:=H2); auto.
Qed.

Lemma iter_hh7 :  forall seen_list stack
  (HH7: forall i j, In i seen_list -> cfg code i j -> In j seen_list \/ In j stack),
  forall i j, (cfg code)** i j -> In i seen_list -> In j seen_list \/
    exists k, (cfg code)** i k /\ (cfg code)** k j /\ In k stack.
Proof.
  induction 2; intros; auto.
  edestruct HH7; eauto.
  right; exists y; repeat split; auto.
  edestruct IHclos_refl_trans1; eauto.
  edestruct IHclos_refl_trans2; eauto.
  destruct H3 as [k [T1 [T2 T3]]].
  right; exists k; repeat split; eauto.
  destruct H2 as [k [T1 [T2 T3]]].
  right; exists k; repeat split; eauto.
Qed.

Lemma acc_succ_prop : forall workl seen_set seen_list stack seen code'
  (HH1: In entry seen_list)
  (HH2: list_norepet stack)
  (HH3: forall i, In i stack -> seen_set ! i = Some  tt)
  (HH4: forall i, In i seen_list -> seen_set ! i = Some  tt)
  (HH5: forall i, In i seen_list -> In i stack -> False)
  (HH6: forall i, seen_set ! i = Some tt -> In i seen_list \/ In i stack)
  (HH7: forall i j, In i seen_list -> cfg code i j -> In j seen_list \/ In j stack)
  (HH8: forall i, In i seen_list -> (cfg code)** entry i)
  (HH11: forall i, In i stack -> (cfg code)** entry i)
  (HH9: acc_succ code workl (OK (seen_set,seen_list,stack)) = OK (seen, code'))
  (HH10: list_norepet seen_list),
  (forall j, (cfg code)** entry j -> In j seen /\ code ! j = code' !j)
  /\ (forall j ins, code'!j = Some ins -> In j seen)
  /\ list_norepet seen
  /\ (forall j, In j seen -> code!j = code'!j)
  /\ (forall i j, In i seen -> cfg code i j -> In j seen)
  /\ (forall j, In j seen -> (cfg code)** entry j).
Proof.
  induction workl; simpl; intros until 11.
  destruct stack; inv HH9.
  assert (forall j : node, (cfg code **) entry j -> In j seen); intros.
  elim (iter_hh7 seen nil HH7 entry j); auto.
  destruct 1; intuition.
  split; auto.
  intros.
  rewrite PTree.gcombine; auto.
  rewrite HH4; auto.
  split; intros.
  rewrite PTree.gcombine in H0; auto.
  unfold remove_dead in *.
  case_eq (seen_set!j); intros; rewrite H1 in *; try congruence.
  elim HH6 with j; intros; auto.
  destruct u; auto.
  split; auto.
  split; auto.
  intros.
  rewrite PTree.gcombine; simpl; auto.
  rewrite HH4; auto.
  split.
  intros; exploit HH7; eauto; destruct 1; simpl; auto.
  assumption.

  destruct stack; inv HH9.
  assert (forall j : node, (cfg code **) entry j -> In j seen); intros.
  elim (iter_hh7 seen nil HH7 entry j); auto.
  destruct 1; intuition.
  split; auto.
  intros.
  rewrite PTree.gcombine; auto.
  rewrite HH4; auto.
  split; intros.
  rewrite PTree.gcombine in H0; unfold remove_dead in *.
  case_eq (seen_set!j); intros; rewrite H1 in *; try congruence.
  elim HH6 with j; intros; auto.
  destruct u; auto.
  auto.
  split; auto.
  split; auto.
  intros; rewrite PTree.gcombine; auto.
  rewrite HH4; auto.
  split.
  intros; exploit HH7; eauto; destruct 1; auto.
  assumption.

  case_eq (not_seen_sons code p (PTree.set p tt seen_set)); intros new seen_set' Hn.
  rewrite Hn in *.

  apply IHworkl with (10:=H0); auto with datatypes; clear H0.

  apply list_norepet_append; auto.
  generalize (not_seen_sons_prop5 p (PTree.set p tt seen_set)); rewrite Hn; auto.
  inv HH2; auto.
  unfold list_disjoint; red; intros; subst.
  assert (seen_set!y=None).
  generalize (not_seen_sons_prop2 p y (PTree.set p tt seen_set)); rewrite Hn; simpl; intros.
  apply H1 in H.
  rewrite PTree.gsspec in H; destruct peq; try congruence.
  rewrite HH3 in H1; auto with datatypes; congruence.

  simpl; intros i Hi.
  rewrite in_app in Hi; destruct Hi; auto.
  eapply not_seen_sons_prop4; eauto.
  eapply not_seen_sons_prop3; eauto.
  rewrite PTree.gsspec; destruct peq; auto with datatypes.

simpl; intros i Hi.
  destruct Hi; subst.
  eapply not_seen_sons_prop3; eauto.
  rewrite PTree.gss; auto.
  eapply not_seen_sons_prop3; eauto.
  rewrite PTree.gsspec; destruct peq; auto.

simpl; intros i Hi1 Hi2.
  rewrite in_app in Hi2.
  destruct Hi2.
  generalize (not_seen_sons_prop2 p i (PTree.set p tt seen_set)); rewrite Hn; simpl; intros.
  apply H0 in H; clear H0.
  rewrite PTree.gsspec in H; destruct peq; try congruence.
  destruct Hi1; subst; try congruence.
  rewrite HH4 in H; congruence.
  destruct Hi1; subst.
  inv HH2; intuition.
  elim HH5 with i; auto with datatypes.

intros i Hi.
  elim not_seen_sons_prop6 with (1:=Hn) (2:=Hi); intros.
  rewrite PTree.gsspec in H; destruct peq; auto.
  left; left; auto.
  elim HH6 with i; auto with datatypes.
  simpl; destruct 1; auto.
  right; rewrite in_app; auto.
  right; rewrite in_app; auto.

intros i j Hi1 Hi2.
  simpl in Hi1; destruct Hi1; subst.
  elim not_seen_sons_prop1 with i j (PTree.set i tt seen_set) seen_set' new; auto; intros.
  right; eauto with datatypes.
  rewrite PTree.gsspec in H; destruct peq; auto.
  left; left; auto.
  elim HH6 with j; auto with datatypes.
  simpl; destruct 1; auto with datatypes.
  elim HH7 with i j; auto with datatypes.
  simpl; destruct 1; auto with datatypes.

simpl; intros i Hi.
  destruct Hi; auto with datatypes.
  subst; auto with datatypes.

simpl; intros i Hi.
  rewrite in_app in Hi.
  destruct Hi; auto with datatypes.
  exploit not_seen_sons_prop8; eauto with datatypes.

  constructor; auto.
  intro HI; elim HH5 with p; auto with arith datatypes.
Qed.

End dfs.

(** * Proof of the well-formedness of generated functions *)
Lemma dfs_prop_aux : forall tf seen code',
  dfs tf = OK (seen, code') ->
  (forall j, (cfg (fn_code tf))** (fn_entrypoint tf) j ->
    In j seen /\  (fn_code tf) ! j = code' ! j)
  /\ (forall j ins, code'!j = Some ins -> In j seen)
  /\ list_norepet seen
  /\ (forall j, In j seen -> (fn_code tf)!j = code'!j)
  /\ (forall i j, In i seen -> cfg (fn_code tf) i j -> In j seen)
  /\ (forall i, In i seen -> (cfg (fn_code tf))** (fn_entrypoint tf) i).
Proof.
  unfold dfs; intros tf seen.
  destruct (map (@fst node SeqBB.t) (PTree.elements (fn_code tf))); simpl.
  intros; congruence.
  case_eq (not_seen_sons (fn_code tf) (fn_entrypoint tf)
           (PTree.set (fn_entrypoint tf) tt (PTree.empty unit)));
  intros new seen_set TT.
  intros code' T; monadInv T.
  assert (
 (forall j : node,
    (cfg (fn_code tf) **) (fn_entrypoint tf) j ->
    In j x /\ (fn_code tf) ! j = code' ! j) /\
   (forall (j : positive) (ins : SeqBB.t),
    code' ! j = Some ins -> In j x) /\ list_norepet x /\
   (forall j, In j x -> (fn_code tf)!j = code'!j) /\
   (forall i j, In i x -> cfg (fn_code tf) i j -> In j x) /\
   (forall j : positive, In j x -> (cfg (fn_code tf) **) (fn_entrypoint tf) j)
   ).
  apply acc_succ_prop with (entry:=(fn_entrypoint tf)) (10:=EQ); auto with datatypes.

  apply list_norepet_append; auto with datatypes.
  generalize (not_seen_sons_prop5 (fn_code tf) (fn_entrypoint tf)
         (PTree.set (fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl; auto.
  constructor.
  intro; simpl; intuition.

  intros.
  rewrite in_app in H; destruct H.
  generalize (not_seen_sons_prop4 (fn_code tf) (fn_entrypoint tf)
         (PTree.set (fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl; eauto.
  elim H.

  simpl; intuition.
  subst.
  generalize (not_seen_sons_prop3 (fn_code tf) (fn_entrypoint tf)
         (PTree.set (fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl; intros.
  eapply H; eauto.
  rewrite PTree.gss; auto.

  simpl; intuition; subst.
  rewrite in_app in H0; destruct H0.
  generalize (not_seen_sons_prop2 (fn_code tf) (fn_entrypoint tf)
    (fn_entrypoint tf)
    (PTree.set (fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl.
  rewrite PTree.gss; intros.
  apply H0 in H; congruence.
  elim H.

  intros.
  elim not_seen_sons_prop6 with (1:=TT) (i0:=i); auto with datatypes.
  rewrite PTree.gsspec; destruct peq; subst; intros; auto with datatypes.
  rewrite PTree.gempty in H0; congruence.

  simpl; intuition.
  elim not_seen_sons_prop1 with (j:=j) (1:=TT); auto with datatypes.
  rewrite PTree.gsspec; destruct peq; subst; intros; auto with datatypes.
  rewrite PTree.gempty in H; congruence.
  rewrite H1; auto.

  simpl; destruct 1; subst.
  constructor 2.
  elim H.

  intros i; rewrite in_app; destruct 1.
  exploit not_seen_sons_prop8; eauto.
  elim H.

  repeat constructor.
  intro H; elim H.

  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct H3 as [H3 H5].
  repeat split; intros.
  rewrite <- rev_alt; rewrite <- In_rev; eauto.
  elim H with j; auto.
  elim H with j; auto.
  rewrite <- rev_alt; rewrite <- In_rev; eauto.
  rewrite <- rev_alt; auto.
  apply list_norepet_rev; auto.
  rewrite <- rev_alt in H4; rewrite <- In_rev in H4; eauto.
  rewrite <- rev_alt in *; rewrite <- In_rev in *; eauto.
  rewrite <- rev_alt in *; rewrite <- In_rev in *; eauto.
Qed.

  (** Lemmas derived from the main lemma.*)
Lemma transf_function_fn_entrypoint : forall f tf,
  transf_function f = OK tf ->
  fn_entrypoint tf = fn_entrypoint f.
Proof.
  intros.
  unfold transf_function in H.
  destruct (dfs f); simpl in H; try congruence.
  destruct p; inv H.
  reflexivity.
Qed.

Lemma transf_function_ppoints1 : forall f tf,
  transf_function f = OK tf ->
  (forall j, (cfg (fn_code f))** (fn_entrypoint f) j ->
             (fn_code f) ! j = (fn_code tf) ! j).
Proof.
  intros.
  monadInv H.
  exploit dfs_prop_aux ; eauto.
  intuition.
  eelim H1; eauto.
Qed.

Lemma transf_function_ppoints1' : forall f tf,
  transf_function f = OK tf ->
  (forall j, (cfg (fn_code f))** (fn_entrypoint f) j ->
    (cfg (fn_code tf))** (fn_entrypoint tf) j).
Proof.
  intros.
  rewrite <- cfg_star_same.
  assert (fn_entrypoint tf = fn_entrypoint f)
    by (eapply transf_function_fn_entrypoint; eauto).
  apply cfg_star_same_code with (fn_code f).
  - intros.
    rewrite cfg_star_same in *.
    clear H0.
    rewrite H1 in H2.
    exploit transf_function_ppoints1; eauto.
  - intuition.
    rewrite cfg_star_same; rewrite H1; auto.
Qed.

(* Lemma transf_function_ppoints2 : forall f tf, *)
(*     transf_function f = OK tf -> *)
(*     (forall j ins, (fn_code tf)!j = Some ins -> In j (fn_dfs tf)). *)
(* Proof. *)
(*   intros. *)
(*   monadInv H ; simpl in *. *)
(*   exploit dfs_prop_aux ; eauto; intuition eauto. *)
(* Qed. *)


(* Lemma transf_function_ppoints3 : forall f tf, *)
(*   transf_function f = OK tf -> *)
(*   list_norepet (fn_dfs tf). *)
(* Proof. *)
(*   intros. *)
(*   monadInv H. *)
(*   eapply dfs_prop_aux ; eauto. *)
(* Qed. *)

(* Lemma transf_function_ppoints6 : forall f tf, *)
(*   transf_function f = OK tf -> *)
(*   (forall i, In i (fn_dfs tf) -> (cfg (RTLdfs.fn_code tf))** (RTLdfs.fn_entrypoint tf) i). *)
(* Proof. *)
(*   intros. *)
(*   eapply transf_function_ppoints1'; eauto. *)
(*   monadInv H. *)
(*   eapply dfs_prop_aux ; eauto. *)
(* Qed. *)

(* Lemma transf_function_wf_dfs : forall f tf, *)
(*    transf_function f = OK tf -> *)
(*    wf_dfs_function tf. *)
(* Proof. *)
(*   constructor. *)
(*   eapply transf_function_ppoints2 ; eauto. *)
(*   eapply transf_function_ppoints6 ; eauto. *)
(*   eapply transf_function_ppoints3 ; eauto. *)
(* Qed. *)

(** All generated functions satisfy the [wf_dfs] predicate. *)
Require Import Linking.

Definition match_prog (p: program) (tp: program) :=
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. apply match_transform_partial_program; auto.
Qed.

(* Lemma match_prog_wf_dfs : forall p tp, *)
(*   match_prog p tp -> *)
(*   wf_dfs_program tp. *)
(* Proof. *)
(*   intros. *)
(*   red. intros. *)
(*   inv H. intuition. *)
(*   revert H1 H0. clear. *)
(*   generalize (prog_defs tp). *)
(*   induction 1; intros. *)
(*   - inv H0. *)
(*   - inv H0. *)
(*     + clear H1 IHlist_forall2. *)
(*       inv H. inv H1. *)
(*       destruct f1 ; simpl in * ; try constructor; auto. *)
(*       * monadInv H4. *)
(*         exploit transf_function_wf_dfs; eauto. *)
(*         intros. *)
(*         econstructor; eauto. *)
(*       * monadInv H4. *)
(*         constructor. *)
(*     + eapply IHlist_forall2; eauto. *)
(* Qed. *)

(** * Semantics preservation *)
Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF_PROG: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro.
  eapply Genv.find_symbol_transf_partial; eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  eapply Genv.find_funct_transf_partial; eauto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof.
  eapply Genv.find_funct_ptr_transf_partial ; eauto.
Qed.

Lemma instr_at:
  forall f tf pc ins,
  transf_function f = OK tf ->
  (cfg (fn_code f) **) (fn_entrypoint f) pc ->
  (fn_code f)!pc = Some ins ->
  (fn_code tf)!pc = Some ins.
Proof.
  intros. inv H.
  monadInv  H3; simpl.
  inv EQ.
  elim dfs_prop_aux with f x x0; auto; intros.
  elim H with pc; auto.
  congruence.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros f tf. destruct f; simpl; intros.
  monadInv H; auto.
  monadInv EQ; auto.
  inv H. simpl; auto.
Qed.

Lemma find_function_preserved_same : forall r rs f f',
  find_function ge (inl ident r) rs = Some f ->
  find_function tge (inl ident r) rs = Some f' ->
  funsig f = funsig f'.
Proof.
  intros. simpl in *.
  exploit (functions_translated rs#r) ; eauto.
  intros.
  destruct H1 as [tf [Htf Oktf]].
  symmetry.
  eapply sig_fundef_translated; eauto.
  rewrite Htf in H0. inv H0; auto.
Qed.

Lemma spec_ros_r_find_function:
  forall rs f r,
  find_function ge (inl _ r) rs = Some f ->
  exists tf,
     find_function tge (inl _ r) rs = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros.
  eapply functions_translated; eauto.
Qed.

Lemma spec_ros_id_find_function:
  forall rs f id,
  find_function ge (inr _ id) rs = Some f ->
  exists tf,
     find_function tge (inr _ id) rs = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros.
  simpl in *.
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil
| match_stackframes_cons:
  forall res f sp pc ps rs s tf ts
    (STACK : (match_stackframes s ts))
    (SPEC: (transf_function f = OK tf))
    (HCFG: (cfg (fn_code f) **) (fn_entrypoint f) pc),
    match_stackframes
    ((Stackframe res f sp pc ps rs) :: s)
    ((Stackframe res tf sp pc ps rs) :: ts)
    .
Hint Constructors match_stackframes: core.

Variant match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s ts sp pc rs m f tf ps
        (SPEC: transf_function f = OK tf)
        (HCFG: (cfg (fn_code f) ** ) (fn_entrypoint f) pc)
        (STACK: match_stackframes s ts ),
        match_states (State s f sp pc rs ps m) (State ts tf sp pc rs ps m)
  | match_states_call:
      forall s ts f tf args m
        (SPEC: transf_fundef f = OK tf)
        (STACK: match_stackframes s ts ),
        match_states (Callstate s f args m) (Callstate ts tf args m)
  | match_states_return:
      forall s ts v m
        (STACK: match_stackframes s ts ),
        match_states (Returnstate s v m) (Returnstate ts v m).
Hint Constructors match_states: core.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
    exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  assert (MEM: (Genv.init_mem tprog) = Some m0)
    by (eapply (Genv.init_mem_transf_partial TRANSF_PROG); eauto).
  exists (Callstate nil tf nil m0); split.
  - econstructor; eauto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
      symmetry; eapply match_program_main; eauto.
    + rewrite <- H3. apply sig_fundef_translated; auto.
  - eapply match_states_call  ; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  inv STACK.
  constructor.
Qed.

Lemma stacksize_preserved: forall f tf,
  transf_function f = OK tf ->
  fn_stacksize f = fn_stacksize tf.
Proof.
  intros.
  monadInv H. auto.
Qed.

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof.
  eapply Genv.senv_transf_partial; eauto.
Qed.

Create HintDb valagree.
Hint Resolve find_function_preserved_same: valagree.
Hint Resolve symbols_preserved : valagree.
Hint Resolve eval_addressing_preserved : valagree.
Hint Resolve eval_operation_preserved : valagree.
Hint Resolve sig_fundef_translated : valagree.
Hint Resolve senv_preserved : valagree.
Hint Resolve stacksize_preserved: valagree.

Lemma step_instr :
  forall sp s1 s2 a,
    step_instr ge sp s1 a s2 ->
    step_instr tge sp s1 a s2.
Proof.
  inversion 1; subst; econstructor; eauto with valagree.
  - erewrite eval_operation_preserved; eauto with valagree.
  - erewrite eval_addressing_preserved; eauto with valagree.
  - erewrite eval_addressing_preserved; eauto with valagree.
Qed.

Lemma seqbb_eq :
  forall bb sp i1 i2 cf,
    SeqBB.step ge sp (Iexec i1) bb (Iterm i2 cf) ->
    SeqBB.step tge sp (Iexec i1) bb (Iterm i2 cf).
Proof.
  induction bb; crush; inv H.
  - econstructor; eauto. apply step_instr; eassumption.
    destruct state'. eapply IHbb; eauto.
  - constructor; apply step_instr; auto.
Qed.

Ltac try_succ f pc pc' :=
  try (eapply Rstar_trans ; eauto) ; constructor ;
    (eapply (CFG (fn_code f) pc pc'); eauto;  simpl; auto).

Lemma step_cf_eq :
  forall stk stk' f tf sp pc rs pr m cf s t bb p,
    step_cf_instr ge (State stk f sp pc rs pr m) cf t s ->
    match_stackframes stk stk' ->
    transf_function f = OK tf ->
    (cfg (fn_code f) ** ) (fn_entrypoint f) pc ->
    (fn_code f)!pc = Some bb ->
    In (RBexit p cf) bb ->
    exists s', step_cf_instr tge (State stk' tf sp pc rs pr m) cf t s'
               /\ match_states s s'.
Proof.
  inversion 1; subst; simplify.

  (*icall*)
  destruct ros.
  exploit spec_ros_r_find_function ; eauto.
  intros. destruct H5 as [tf' [Hfind OKtf']].

  eexists ; split ; eauto. constructor; eauto with valagree.
  constructor; eauto. constructor; eauto. try_succ f pc pc'; eauto.
  eapply in_cf_all_successors; eauto; cbn [successors_instr]; intuition.

  exploit spec_ros_id_find_function ; eauto.
  intros. destruct H5 as [tf' [Hfind OKtf']].

  eexists ; split ; eauto. constructor; eauto with valagree.
  constructor; eauto. constructor; eauto. try_succ f pc pc'; eauto.
  eapply in_cf_all_successors; eauto; cbn [successors_instr]; intuition.

  (*itailcall*)
  destruct ros.
  exploit spec_ros_r_find_function ; eauto.
  intros. destruct H5 as [tf' [Hfind OKtf']].

  exploit find_function_preserved_same ; eauto.
  intros.
  exists (Callstate stk' tf' rs##args m');  split ; eauto.
  constructor; eauto with valagree.
  replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree.

  exploit spec_ros_id_find_function ; eauto.
  intros. destruct H5 as [tf' [Hfind OKtf']].

  exists (Callstate stk' tf' rs##args m');  split ; eauto.
  constructor ; eauto with valagree.
  replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree.

  (* ibuiltin *)
  exploit instr_at; eauto; intros.
  exists (State stk' tf sp pc' (regmap_setres res vres rs) pr m') ; split ; eauto.
  econstructor ; eauto.
  eapply eval_builtin_args_preserved with (2:= H10); eauto with valagree.
  eapply external_call_symbols_preserved; eauto with valagree.

  constructor; auto. try_succ f pc pc'.
  eapply in_cf_all_successors; eauto; cbn [successors_instr]; intuition.

  (* ifso *)
  destruct b.
  exists (State stk' tf sp ifso rs pr m); split ; eauto.
  eapply exec_RBcond ; eauto.
  constructor; auto.
  try_succ f pc ifso.
  eapply in_cf_all_successors; eauto; cbn [successors_instr]; intuition.

  (*ifnot*)
  exists (State stk' tf sp ifnot rs pr m); split ; eauto.
  eapply exec_RBcond ; eauto.
  constructor; auto.
  try_succ f pc ifnot.
  eapply in_cf_all_successors; eauto; cbn [successors_instr]; intuition.

  (* ijump *)
  exists (State stk' tf sp pc' rs pr m); split ; eauto.
  eapply exec_RBjumptable ; eauto.
  constructor; auto.
  try_succ f pc pc'.
  eapply in_cf_all_successors; eauto. eapply list_nth_z_in; eauto.

  (* ireturn *)
  exists (Returnstate stk' (regmap_optget or Vundef rs) m'); split ; eauto.
  eapply exec_RBreturn ; eauto.
  rewrite <- H10 ; eauto with valagree.
  rewrite stacksize_preserved with f tf ; eauto.

  (*igoto*)
  exists (State stk' tf sp pc' rs pr m); split; eauto.
  eapply exec_RBgoto; eauto.
  constructor; auto.
  try_succ f pc pc'.
  eapply in_cf_all_successors; eauto; cbn [successors_instr]; intuition.
Qed.

Lemma transl_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; auto.

  exploit instr_at; eauto; intros.
  exploit step_cf_in; eauto; simplify.
  exploit step_cf_eq; eauto; simplify.
  exists x0.
  split. econstructor; eauto.
  apply seqbb_eq; auto. auto.

  (* internal *)
  simpl in SPEC. monadInv SPEC. simpl in STACK.
  exists (State ts x
                (Vptr stk Ptrofs.zero)
                x.(fn_entrypoint)
                    (init_regs args x.(fn_params))
                    (PMap.init false)
                    m').
  split.
  eapply exec_function_internal; eauto.
  rewrite stacksize_preserved with f x in H ; auto.
  replace (fn_entrypoint f) with (fn_entrypoint x).
  replace (fn_params f) with (fn_params x).

  econstructor ; eauto.
  replace (fn_entrypoint x) with (fn_entrypoint f).
  eapply Rstar_refl ; eauto.
  monadInv EQ. auto.
  monadInv EQ. auto.
  monadInv EQ. auto.

  (* external *)
  inv SPEC.
  exists (Returnstate ts res m'). split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  econstructor ; eauto.

  (* return state *)
  inv STACK.
  exists (State ts0 tf sp pc (rs# res <- vres) pr m);
    split; ( try constructor ; eauto).
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_step.
  eapply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct.
Qed.

End PRESERVATION.
