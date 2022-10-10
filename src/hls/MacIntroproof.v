(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
   Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

================
RTLBlockgenproof
================

.. coq:: none
|*)

Require Import compcert.common.AST.
(*Require Import compcert.common.Errors.*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Maps.
Require Import compcert.backend.Registers.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Events.
(*Require Import compcert.common.Memory.*)
Require Import compcert.common.Values.

Require Import vericert.common.Vericertlib.
Require Import vericert.common.DecEq.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.MacIntro.

#[local] Open Scope positive.

#[local] Notation "'mki'" := (mk_instr_state) (at level 1).

Definition is_none {A} (eq : forall x y : A, { x = y } + { x <> y }) :=
  fun y => option_eq eq y None.


Definition match_rs (vregs : PTree.t bool) (rs rs' : Regmap.t val) :=
  forall r, (exists b, vregs ! r = Some b) -> rs#r = rs'#r.

Definition le_analysis t t' :=
  forall r b, t ! r = Some b -> exists b', t' ! r = Some (b' && b).

Lemma le_analysis_order : Relation_Definitions.order _ le_analysis.
Proof.
  split.
  - now eexists; rewrite andb_true_l.
  - now intros ?* Hxy Hyz ?? [? [? H]%Hyz]%Hxy; rewrite andb_assoc in H; eauto.
  - intros x y Hxy Hyx; apply PTree.extensionality; intro.
    destruct x ! _ as [b | ] eqn: Hx.
    + destruct (Hxy _ _ Hx) as [? Hy]; destruct (Hyx _ _ Hy) as [? Hx'].
      rewrite Hx' in Hx; inversion Hx as [H]; rewrite Hy, H; clear Hx Hy Hx'.
      destruct b; crush.
    + destruct y ! _ as [b | ] eqn: Hy; [ | easy].
      now destruct (Hyx _ _ Hy) as [? Hx']; rewrite Hx' in Hx.
Qed.

Variant match_stackframe : stackframe -> stackframe -> Prop :=
| Match_stackframe : forall res f sp pc rs p,
  match_stackframe (Stackframe res f sp pc rs p)
    (Stackframe res (transf_function f) sp pc rs p).

Variant match_states : state -> state -> Prop :=
| match_state : forall stk stk' f sp pc rs rs' p m,
  match_rs (read_once (transf_function f)) rs rs' ->
  Forall2 match_stackframe stk stk' ->
  match_states (State stk f sp pc rs p m)
    (State stk' (transf_function f) sp pc rs' p m)
| match_callstate : forall cs cs' f args m,
  Forall2 match_stackframe cs cs' ->
  match_states (Callstate cs f args m) (Callstate cs' (transf_fundef f) args m)
| match_returnstate : forall cs cs' v m,
  Forall2 match_stackframe cs cs' ->
  match_states (Returnstate cs v m) (Returnstate cs' v m).


Lemma mark_once_register_rw {r t} :
  mark_once_register t r
  = PTree.set r (match t ! r with Some _ => false | None => true end) t.
Proof.
  apply PTree.extensionality; intro r'.
  now unfold mark_once_register; destruct t ! r as [[] | ] eqn: Heq;
    [ | rewrite PTree.gsspec; destruct peq as [-> | ] | ].
Qed.

Definition merge_results oa ob :=
  match oa, ob with
  | None, x | x, None => x
  | Some _, Some _ => Some false
  end.

Lemma merge_results_comm oa ob : merge_results oa ob = merge_results ob oa.
Proof. now destruct oa, ob. Qed.

Lemma merge_results_assoc oa ob oc :
  merge_results oa (merge_results ob oc) = merge_results (merge_results oa ob) oc.
Proof. now destruct oa, ob, oc. Qed.

#[local] Definition fl1mor := fold_left mark_once_register.

#[local]
Lemma fl1mor_rw {l r t} :
  (fl1mor l t) ! r = merge_results (t ! r) ((fl1mor l (PTree.empty _)) ! r).
Proof.
  revert t; induction l as [ | * Hrec]; intro;
    [now rewrite PTree.gempty; destruct _ ! _ | simpl].
  rewrite !(Hrec (_ _ _)), !mark_once_register_rw, !PTree.gsspec, !PTree.gempty.
  destruct peq as [<- | ]; simpl; [repeat destruct_match | ]; try easy; [].
  now rewrite merge_results_comm; simpl; destruct_match.
Qed.

#[local]
Definition fl2mor := fold_left (fun t i => fl1mor (input_registers i) t).

#[local]
Lemma fl2mor_rw {l r t} :
  (fl2mor l t) ! r = merge_results (t ! r) ((fl2mor l (PTree.empty _)) ! r).
Proof.
  revert t; induction l as [ | * Hrec]; intro;
    [now rewrite PTree.gempty; destruct _ ! _ | simpl].
  now rewrite !(Hrec (_ _ _)), fl1mor_rw, merge_results_assoc.
Qed.

#[local] Definition fl3mor := fold_left (fun a b => fl2mor b a).

#[local]
Lemma fl3mor_rw {l r t} :
  (fl3mor l t) ! r = merge_results (t ! r) ((fl3mor l (PTree.empty _)) ! r).
Proof.
  revert t; induction l as [ | * Hrec]; intro;
    [now rewrite PTree.gempty; destruct _ ! _ | simpl].
  now rewrite !(Hrec (_ _ _)), fl2mor_rw, merge_results_assoc.
Qed.

Lemma read_once_bb_rw {bb r t n} :
  (read_once_bb t n bb) ! r
  = merge_results (t ! r) ((read_once_bb (PTree.empty _) n bb) ! r).
Proof.
  unfold read_once_bb, ParBB.foldl; fold fl1mor fl2mor fl3mor.
  revert t; induction bb as [ | * Hrec]; intro;
    [now rewrite PTree.gempty; destruct _ ! _ | simpl].
  now rewrite !(Hrec (_ _ _)), fl3mor_rw, merge_results_assoc.
Qed.

Corollary mark_once_register_determ {l r t t'} :
  t ! r = t' ! r -> (fl1mor l t) ! r = (fl1mor l t') ! r.
Proof. now rewrite fl1mor_rw, (fl1mor_rw (t := t')); intros <-. Qed.

Corollary mark_once_register_false {l r t} :
  t ! r = Some false -> (fl1mor l t) ! r = Some false.
Proof. now rewrite fl1mor_rw; intros ->; simpl; destruct_match. Qed.

Corollary mark_once_instr_determ {l r t t'} :
  t ! r = t' ! r -> (fl2mor l t) ! r = (fl2mor l t') ! r.
Proof. now rewrite fl2mor_rw, (fl2mor_rw (t := t')); intros <-. Qed.

Corollary mark_once_instr_false {l r t} :
  t ! r = Some false -> (fl2mor l t) ! r = Some false.
Proof. now rewrite fl2mor_rw; intros ->; simpl; destruct_match. Qed.

Corollary mark_once_deepbb_determ {l r t t'} :
  t ! r = t' ! r -> (fl3mor l t) ! r = (fl3mor l t') ! r.
Proof. now rewrite fl3mor_rw, (fl3mor_rw (t := t')); intros <-. Qed.

Corollary mark_once_deepbb_false {l r t} :
  t ! r = Some false -> (fl3mor l t) ! r = Some false.
Proof. now rewrite fl3mor_rw; intros ->; simpl; destruct_match. Qed.

Corollary mark_once_bb_determ {bb r t t' n} :
  t ! r = t' ! r -> (read_once_bb t n bb) ! r = (read_once_bb t' n bb) ! r.
Proof. now rewrite read_once_bb_rw, (read_once_bb_rw (t := t')); intros <-. Qed.

Corollary read_once_bb_false {bb r t n} :
  t ! r = Some false -> (read_once_bb t n bb) ! r = Some false.
Proof. now rewrite read_once_bb_rw; intros ->; simpl; destruct_match. Qed.

Lemma mark_once_register_mono {l t} : le_analysis t (fl1mor l t).
Proof.
  revert t; induction l as [ | * Hrec]; [apply le_analysis_order | simpl].
  intro; eapply le_analysis_order, Hrec.
  intros ??; rewrite mark_once_register_rw, PTree.gsspec.
  now destruct peq as [<- | ]; intros ->; eexists;
    [rewrite andb_false_l | rewrite andb_true_l].
Qed.

Lemma mark_once_register_mono_tl {l r t} :
  le_analysis (fl1mor l t) (fl1mor (r::l) t).
Proof.
  intros r' b; simpl.
  rewrite fl1mor_rw, (fl1mor_rw (t := _ _ _)), mark_once_register_rw, PTree.gsspec.
  now destruct peq as [-> | Hneq];
    [repeat (destruct_match; simpl); intro H; inv H | intros ->];
    eexists; f_equal; eauto using andb_true_l, andb_false_l, andb_comm.
Qed.

Lemma mark_once_instr_mono {l t} : le_analysis t (fl2mor l t).
Proof.
  revert t; induction l as [ | * Hrec]; [apply le_analysis_order | simpl].
  intro; eapply le_analysis_order, Hrec.
  exact mark_once_register_mono.
Qed.

Lemma mark_once_instr_mono_tl {l i t} :
  le_analysis (fl2mor l t) (fl2mor (i::l) t).
Proof.
  intros r' b; simpl.
  rewrite fl2mor_rw, (fl2mor_rw (t := _ _ _)), fl1mor_rw, merge_results_comm.
  intro Hrw; rewrite merge_results_comm, merge_results_assoc, Hrw; simpl.
  now destruct_match; eexists; [rewrite andb_false_l | rewrite andb_true_l].
Qed.

Lemma mark_once_deepbb_mono {l t} : le_analysis t (fl3mor l t).
Proof.
  revert t; induction l as [ | * Hrec]; [apply le_analysis_order | simpl].
  intro; eapply le_analysis_order, Hrec.
  exact mark_once_instr_mono.
Qed.

Lemma mark_once_deepbb_mono_tl {l bb2 t} :
  le_analysis (fl3mor l t) (fl3mor (bb2::l) t).
Proof.
  intros r' b; simpl.
  rewrite fl3mor_rw, (fl3mor_rw (t := _ _ _)), fl2mor_rw, merge_results_comm.
  intro Hrw; rewrite merge_results_comm, merge_results_assoc, Hrw; simpl.
  now destruct_match; eexists; [rewrite andb_false_l | rewrite andb_true_l].
Qed.

Lemma read_once_bb_mono {bb t n} : le_analysis t (read_once_bb t n bb).
Proof.
  revert t; induction bb as [ | * Hrec]; [apply le_analysis_order | simpl].
  intro; eapply le_analysis_order, Hrec.
  exact mark_once_deepbb_mono.
Qed.

Lemma read_once_bb_mono_tl {bb bb2 t n} :
  le_analysis (read_once_bb t n bb) (read_once_bb t n (bb2::bb)).
Proof.
  intros r' b; simpl; rewrite read_once_bb_rw, (read_once_bb_rw (t := _ _ _)).
  fold fl1mor fl2mor fl3mor; rewrite fl3mor_rw, merge_results_comm.
  intro Hrw; rewrite merge_results_comm, merge_results_assoc, Hrw; simpl.
  now destruct_match; eexists; [rewrite andb_false_l | rewrite andb_true_l].
Qed.


Lemma mark_once_register_notin {l r t} : ~ In r l -> (fl1mor l t) ! r = t ! r.
Proof.
  revert t; induction l as [ | r' ? Hrec]; [easy | simpl].
  intros ? [?%not_eq_sym Hnin]%Decidable.not_or.
  now rewrite (Hrec _ Hnin), mark_once_register_rw, PTree.gso.
Qed.

Lemma mark_once_register_none_bwd {l r t} :
  (fl1mor l t) ! r = None -> t ! r = None /\ ~ In r l.
Proof.
  revert t; induction l as [ | r' l Hrec]; [easy | simpl].
  intros ? [H ]%Hrec.
  enough (t ! r = None /\ r' <> r /\ ~ In r l)
    by now split; [ | apply Classical_Prop.and_not_or].
  revert H; rewrite mark_once_register_rw, PTree.gsspec.
  now destruct peq as [ | ?%not_eq_sym].
Qed.

Lemma mark_once_register_none_fwd {l r t} :
  t ! r = None -> (exists b, (fl1mor l t) ! r = Some b) <-> In r l.
Proof.
  intro Ht; split; revgoals.
  { now destruct ((_ _ _) ! r) eqn: Heq;
    [eexists | destruct (mark_once_register_none_bwd Heq)]. }
  revert t Ht; induction l as [ | r' ? Hrec]; simpl; [now intros ? -> [] | ].
  destruct (peq r r') as [<- | Hneq]; [now left | ].
  intros ?? H; right; revert H; apply Hrec.
  now rewrite mark_once_register_rw, PTree.gso.
Qed.

Lemma mark_once_register_true_bwd {l r t} :
  (fl1mor l t) ! r = Some true -> t ! r = None <-> In r l.
Proof.
  revert t; induction l as [ | r' l Hrec]; simpl; [now intros ? -> | ].
  intros ? Heq; destruct (in_dec peq r l) as [Hin | Hnin].
  - split; [now right | ]; intros _; revert Hin.
    rewrite <-(Hrec _ Heq), mark_once_register_rw, PTree.gsspec.
    now destruct peq.
  - rewrite (mark_once_register_notin Hnin), mark_once_register_rw in Heq; split.
    + revert Heq; rewrite PTree.gsspec.
      now destruct peq as [<- | ]; [left | intros ->].
    + now intros [-> | []%Hnin]; rewrite PTree.gss in Heq; destruct t ! r.
Qed.

Lemma mark_once_register_true_fwd {l r t} :
  t ! r = Some true -> (fl1mor l t) ! r = Some false <-> In r l.
Proof.
  revert t; induction l as [ | r' ? Hrec]; simpl; [now intros ? -> | ].
  intros ? Heq; destruct (peq r r') as [<- | Hneq].
  - split; [now left | ]; intros _; unfold mark_once_register.
    now rewrite Heq, mark_once_register_false by now rewrite PTree.gss.
  - rewrite Hrec; [ | now rewrite mark_once_register_rw, PTree.gso].
    now split; [right | intros [[]%(not_eq_sym Hneq) | ]].
Qed.

Corollary mark_once_register_true {l r t} :
  (fl1mor l t) ! r = Some true -> t ! r = Some true -> ~ In r l.
Proof.
  intros H%(mark_once_register_true_bwd (l := l))%not_iff_compat%proj1.
  now intro Ht; rewrite Ht in H; apply H.
Qed.

Lemma mark_once_register_some {l r b t} :
  t ! r = Some b ->
  (fl1mor l t) ! r = Some (b
    && is_none bool_dec ((fl1mor l (PTree.empty _)) ! r)).
Proof.
  intro Ht; destruct is_none as [Hnone | Hsome]; simpl.
  { destruct (mark_once_register_none_bwd Hnone)
      as [_ ->%mark_once_register_notin].
    now rewrite andb_true_r. }
  rewrite andb_false_r; destruct b.
  - rewrite (mark_once_register_true_fwd Ht),
      <-(mark_once_register_none_fwd (PTree.gempty _ _)).
    now destruct _ ! r eqn: H in Hsome; eauto.
  - exact (mark_once_register_false Ht).
Qed.

Lemma mark_once_instr_notin {l r t} :
  ~ (exists i, In i l /\ In r (input_registers i)) -> (fl2mor l t) ! r = t ! r.
Proof.
  revert t; induction l as [ | i ? Hrec]; [easy | simpl].
  intros ? Hex; rewrite Hrec; [ | now intros [? []]; eauto].
  now apply mark_once_register_notin; intro; eauto.
Qed.

Lemma mark_once_instr_none_bwd {l r t} :
  (fl2mor l t) ! r = None ->
    t ! r = None /\ ~ exists i, In i l /\ In r (input_registers i).
Proof.
  revert t; induction l as [ | * Hrec]; [now split; [ | intros [? []]] | ].
  intros ? [[-> ]%mark_once_register_none_bwd H']%Hrec.
  now split; [ | intros [? [[<- | ]]]]; eauto.
Qed.

Lemma mark_once_instr_none_fwd {l r t} :
  t ! r = None ->
  (exists b, (fl2mor l t) ! r = Some b) <->
    exists i, In i l /\ In r (input_registers i).
Proof.
  intro Ht; split; revgoals.
  { now destruct ((_ _ _) ! r) eqn: Heq;
    [eexists | destruct (mark_once_instr_none_bwd Heq)]. }
  revert t Ht; induction l as [ | i ? Hrec]; simpl; [now intros ? -> [] | ].
  intros ? Ht H; set (t' := _ _ t) in H; destruct t' ! r eqn: Heq.
  - now eexists; split; [ | apply (mark_once_register_none_fwd Ht)]; eauto.
  - now destruct (Hrec _ Heq H) as [? []]; eauto.
Qed.

Ltac unset id := unfold id in *; clear id.

#[local]
Lemma mark_once_instr_true_bwd_aux {l r i t} :
  ((fl2mor (i::l) t) ! r = Some true -> In r (input_registers i) ->
    (fl1mor (input_registers i) t) ! r = Some true
    /\ ~ exists i, In i l /\ In r (input_registers i))
  /\ ((fl2mor l t) ! r = Some true -> In i l -> In r (input_registers i) ->
    t ! r = None).
Proof.
  assert (forall l i t, (fl2mor (i::l) t) ! r = Some true ->
    In r (input_registers i) ->
    (fl1mor (input_registers i) t) ! r = Some true /\ t ! r = None) as Hrec.
  { simpl; intros ?? t' Hf; set (t'' := _ _ t').
    now destruct t'' ! r as [[ | ] | ] eqn: Heq;
      [split; [ | apply (mark_once_register_true_bwd Heq)]
      | rewrite (mark_once_instr_false Heq) in Hf
      | destruct (mark_once_register_none_bwd Heq)]. }
  enough (forall l i t, (fl2mor l t) ! r = Some true ->
    In i l -> In r (input_registers i) ->
    t ! r = None) as Hrw.
  { split; [ | exact (Hrw _ _ _)].
    intros Hf Hr; destruct (Hrec _ _ _ Hf Hr) as [Ht' Ht].
    simplify; [easy | ].
    now intros [i' [Hin Hr']]; rewrite (Hrw _ _ _ Hf Hin Hr') in Ht'. }
  intro l'; induction l' as [ | * Hrec']; [easy | ].
  intros * Hf [-> | Hin]; [now intros []%(Hrec _ _ _ Hf) | ].
  now intros Hrw%(Hrec' _ _ Hf Hin); destruct (mark_once_register_none_bwd Hrw).
Qed.

Lemma mark_once_instr_true_bwd {l r t} :
  (fl2mor l t) ! r = Some true ->
  t ! r = None <-> exists i, In i l /\ In r (input_registers i).
Proof.
  intro H; split.
  - now intro Ht; apply (mark_once_instr_none_fwd Ht); eauto.
  - now intros [? []]; eauto using (proj2 mark_once_instr_true_bwd_aux).
Qed.

Lemma mark_once_instr_true_fwd {l r t} :
  t ! r = Some true ->
  (fl2mor l t) ! r = Some false <->
    exists i, In i l /\ In r (input_registers i).
Proof.
  revert t; induction l as [ | i ? Hrec]; simpl;
    [now intros ? ->; split; [ | intros []] | ].
  intros ? Ht; set (t' := _ _ t); destruct t' ! r as [b | ] eqn: Heq;
    [ | now rewrite (proj1 (mark_once_register_none_bwd Heq)) in Ht].
  destruct b; split.
  - now intro H; destruct (proj1 (Hrec _ Heq) H) as [? []]; eauto.
  - intros [? [[<- | ] Hr]]; [ | now apply Hrec; eauto].
    now contradict Hr; exact (mark_once_register_true Heq Ht).
  - now eauto using (proj1 (mark_once_register_true_fwd Ht) Heq).
  - now rewrite mark_once_instr_false.
Qed.

Corollary mark_once_instr_true {l r t} :
  (fl2mor l t) ! r = Some true -> t ! r = Some true ->
  ~ exists i, In i l /\ In r (input_registers i).
Proof.
  intros H%(mark_once_instr_true_bwd (l := l))%not_iff_compat%proj1.
  now intro Ht; rewrite Ht in H; apply H.
Qed.

Lemma mark_once_deepbb_notin {l r t} :
  ~ (exists bb2 i, In bb2 l /\ In i bb2 /\ In r (input_registers i)) ->
  (fl3mor l t) ! r = t ! r.
Proof.
  revert t; induction l as [ | * Hrec]; [easy | simpl].
  intros ? Hex; rewrite Hrec.
  - apply mark_once_instr_notin; intros [? []].
    now apply Hex; eexists; eauto.
  - now intros [? [? []]]; apply Hex; eauto.
Qed.

Lemma mark_once_deepbb_none_bwd {l r t} :
  (fl3mor l t) ! r = None ->
  t ! r = None
  /\ ~ exists bb2 i, In bb2 l /\ In i bb2 /\ In r (input_registers i).
Proof.
  revert t; induction l as [ | * Hrec]; [now split; [ | intros [? []]] | ].
  intros ? [[-> ?]%mark_once_instr_none_bwd H']%Hrec.
  now split; [ | intros [? [? [[<- | ]]]]]; eauto.
Qed.

Lemma mark_once_deepbb_none_fwd {l r t} :
  t ! r = None ->
  (exists b, (fl3mor l t) ! r = Some b) <->
    exists bb2 i, In bb2 l /\ In i bb2 /\ In r (input_registers i).
Proof.
  intro Ht; split; revgoals.
  { now destruct ((_ _ _) ! r) eqn: Heq;
    [eexists | destruct (mark_once_deepbb_none_bwd Heq)]. }
  revert t Ht; induction l as [ | bb2 ? Hrec]; simpl; [now intros ? -> [] | ].
  intros ? Ht H; set (t' := _ _ t) in H; destruct (t' ! r) eqn: Heq.
  - now destruct (proj1 (mark_once_instr_none_fwd (l := bb2) Ht)); eauto.
  - now destruct (Hrec _ Heq H) as [? [? []]]; eauto.
Qed.

#[local]
Lemma mark_once_deepbb_true_bwd_aux {l r bb2 i t} :
  ((fl3mor ((i::bb2)::l) t) ! r = Some true -> In r (input_registers i) ->
    (fl2mor (i::bb2) t) ! r = Some true
    /\ ~ exists dbb i, In dbb (bb2::l) /\ In i dbb /\ In r (input_registers i))
  /\ ((fl3mor l t) ! r = Some true ->
    In bb2 l -> In i bb2 -> In r (input_registers i) ->
    t ! r = None).
Proof.
  assert (forall l bb2 i t, (fl3mor ((i::bb2)::l) t) ! r = Some true ->
    In r (input_registers i) ->
    (fl2mor (i::bb2) t) ! r = Some true
    /\ t ! r = None) as Hrec.
  { simpl; intros ? bb2' i' t' Hf ?; set (t'' := _ _ (_ _ t')).
    destruct (t'' ! r) as [[ | ] | ] eqn: Heq.
    - split; [easy | ].
      now apply (mark_once_instr_true_bwd (l := i'::bb2') Heq); simpl; eauto.
    - now rewrite (mark_once_deepbb_false Heq) in Hf.
    - destruct (mark_once_instr_none_bwd (l:= i'::bb2') Heq) as [? []].
      now simpl; eauto. }
  cut (forall l bb2 i t, ((fl3mor) l t) ! r = Some true ->
    In bb2 l -> In i bb2 -> In r (input_registers i) ->
    t ! r = None).
  - intro Hrw; split; [ | exact (Hrw _ _ _ _)].
    assert (forall l bb2 t,
      (forall t, t ! r = Some true -> (fl3mor l t) ! r = Some true ->
        ~ exists dbb i, In dbb l /\ In i dbb /\ In r (input_registers i)) ->
      t ! r = Some true -> (fl3mor (bb2::l) t) ! r = Some true ->
      ~ exists dbb i, In dbb (bb2::l) /\ In i dbb /\ In r (input_registers i))
      as Hrec1.
    { intros * H Ht Hf [? [? [H0 [H1 ]]]].
      now rewrite (Hrw _ _ _ _ Hf H0 H1) in Ht. }
    intros Hf Hr; destruct (Hrec _ _ _ _ Hf Hr) as [Ht' Ht].
    simplify; [easy | eapply Hrec1]; [ | | exact Hf].
    + clear Hf; induction l as [ | * Hrec2]; [now intros ??? [? []] | ].
      intro; exact (Hrec1 _ _ _ Hrec2).
    + destruct (proj2 (mark_once_register_none_fwd Ht) Hr) as [[] ]; [easy | ].
      now rewrite mark_once_instr_false in Ht'.
  - intro l0; induction l0 as [ | l1 ? Hrec1]; [easy | ].
    induction l1 as [ | * Hrec2]; [now intros * ? [<- | ]; [ | apply Hrec1]| ].
    intros * Hf [<- | Hin].
    + intros [-> | Hin']; [now intros []%(Hrec _ _ _ _ Hf) | ].
      intro Hr; specialize (Hrec2 _ _ _ Hf (or_introl (eq_refl _)) Hin' Hr).
      now destruct (mark_once_register_none_bwd Hrec2).
    + intros H1 H2%(Hrec1 _ _ _ Hf Hin H1).
      now destruct (mark_once_instr_none_bwd H2).
Qed.

Lemma mark_once_deepbb_true_bwd {l r t} :
  (fl3mor l t) ! r = Some true ->
  t ! r = None <->
    exists bb2 i, In bb2 l /\ In i bb2 /\ In r (input_registers i).
Proof.
  intro H; split.
  - now intro Ht; apply (mark_once_deepbb_none_fwd Ht); eauto.
  - now intros [? [? [? []]]]; eauto using (proj2 mark_once_deepbb_true_bwd_aux).
Qed.

Lemma mark_once_deepbb_true_fwd {l r t} :
  t ! r = Some true ->
  (fl3mor l t) ! r = Some false <->
    exists bb2 i, In bb2 l /\ In i bb2 /\ In r (input_registers i).
Proof.
  revert t; induction l as [ | bb2 ? Hrec]; simpl;
    [now intros ? ->; split; [ | intros [? []]] | ].
  intros ? Ht; set (t' := _ _ t); destruct t' ! r as [b | ] eqn: Heq;
    [ | now rewrite (proj1 (mark_once_instr_none_bwd Heq)) in Ht].
  destruct b; split.
  - now intro H; destruct (proj1 (Hrec _ Heq) H) as [? [? []]]; eauto.
  - intros [? [? [[<- | ] Hr]]]; [ | now apply Hrec; eauto].
    now contradict Hr; eauto using (mark_once_instr_true Heq Ht).
  - now destruct (proj1 (mark_once_instr_true_fwd Ht) Heq); eauto.
  - now rewrite mark_once_deepbb_false.
Qed.

Corollary mark_once_deepbb_true {l r t} :
  (fl3mor l t) ! r = Some true -> t ! r = Some true ->
  ~ exists bb2 i, In bb2 l /\ In i bb2 /\ In r (input_registers i).
Proof.
  intros H%(mark_once_deepbb_true_bwd (l := l))%not_iff_compat%proj1.
  now intro Ht; rewrite Ht in H; apply H.
Qed.

Lemma read_once_bb_notin {bb r t n} :
  ~ (exists bb1 bb2 i,
    In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i)) ->
  (read_once_bb t n bb) ! r = t ! r.
Proof.
  revert t; induction bb as [ | * Hrec]; [easy | simpl].
  intros ? Hex; rewrite Hrec.
  - apply mark_once_deepbb_notin; intros [? []].
    now apply Hex; eexists; eauto.
  - now intros [? [? [? []]]]; apply Hex; eexists; eauto.
Qed.

Lemma read_once_bb_none_bwd {bb r t n} :
  (read_once_bb t n bb) ! r = None ->
  t ! r = None
  /\ ~ exists bb1 bb2 i,
    In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  revert t; induction bb as [ | * Hrec]; [now split; [ | intros [? [? []]]] | ].
  intros ? [[-> ?]%mark_once_deepbb_none_bwd H']%Hrec.
  now split; [ | intros [? [? [? [[<- | ]]]]]; [ | apply H']]; eauto.
Qed.

Lemma read_once_bb_none_fwd {bb r t n} :
  t ! r = None ->
  (exists b, (read_once_bb t n bb) ! r = Some b) <->
  exists bb1 bb2 i,
    In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  intro Ht; split; revgoals.
  { now destruct ((_ _ _) ! r) eqn: Heq;
    [eexists | destruct (read_once_bb_none_bwd Heq)]. }
  revert t Ht; induction bb as [ | bb1 ? Hrec]; simpl; [now intros ? -> [] | ].
  intros ? Ht H; set (t' := _ _ t) in H; destruct (t' ! r) eqn: Heq.
  - now destruct (proj1 (mark_once_deepbb_none_fwd (l := bb1) Ht)) as [? [? ]];
      [ | eexists _, _, _]; eauto.
  - now destruct (Hrec _ Heq H) as [? [? [? []]]]; eexists; eauto.
Qed.

#[local]
Lemma read_once_bb_true_bwd_aux {bb r bb1 bb2 i t n} :
  ((read_once_bb t n (((i::bb2)::bb1)::bb)) ! r = Some true ->
    In r (input_registers i) ->
    (fl3mor ((i::bb2)::bb1) t) ! r = Some true
    /\ ~ exists sbb dbb i,
      In sbb ((bb2::bb1)::bb)
      /\ In dbb sbb /\ In i dbb /\ In r (input_registers i))
  /\ ((read_once_bb t n bb) ! r = Some true ->
    In bb1 bb -> In bb2 bb1 -> In i bb2 -> In r (input_registers i) ->
    t ! r = None).
Proof.
  assert (forall bb bb1 bb2 i t,
    (read_once_bb t n (((i::bb2)::bb1)::bb)) ! r = Some true ->
    In r (input_registers i) ->
    (fl3mor ((i::bb2)::bb1) t) ! r = Some true
    /\ t ! r = None) as Hrec.
  { simpl; intros ? bb1' bb2' i' t' Hf ?; set (t'' := _ _ (_ _ (_ _ t'))).
    destruct (t'' ! r) as [[ | ] | ] eqn: Heq.
    - split; [easy | ].
      apply (mark_once_deepbb_true_bwd (l := (i'::bb2')::bb1') Heq).
      now eexists _, _; split; [now left | ]; split; [left | ].
    - now rewrite (read_once_bb_false Heq) in Hf.
    - destruct (mark_once_deepbb_none_bwd (l:= (i'::bb2')::bb1') Heq) as [? []].
      now eexists _, _; split; [now left | ]; split; [left | ]. }
  cut (forall bb bb1 bb2 i t, (read_once_bb t n bb) ! r = Some true ->
    In bb1 bb -> In bb2 bb1 -> In i bb2 -> In r (input_registers i) ->
    t ! r = None).
  - intro Hrw; split; [ | exact (Hrw _ _ _ _ _)].
    assert (forall n bb bb1 t,
      (forall t, t ! r = Some true -> (read_once_bb t n bb) ! r = Some true ->
        ~ exists sbb dbb i,
          In sbb bb /\ In dbb sbb /\ In i dbb /\ In r (input_registers i)) ->
      t ! r = Some true ->
      (read_once_bb t n (bb1::bb)) ! r = Some true ->
      ~ exists sbb dbb i,
        In sbb (bb1::bb) /\ In dbb sbb /\ In i dbb /\ In r (input_registers i))
      as Hrec1.
    { intros * H Ht Hf [? [? [? [H0 [H1 [H2 ]]]]]].
      now rewrite (Hrw _ _ _ _ _ Hf H0 H1 H2) in Ht. }
    intros Hf Hr; destruct (Hrec _ _ _ _ _ Hf Hr) as [Ht' Ht].
    simplify; [easy | eapply Hrec1]; [ | | exact Hf].
    + clear Hf; induction bb as [ | * Hrec2]; [now intros ??? [? [? []]] | ].
      intro; exact (Hrec1 _ _ _ _ Hrec2).
    + pose proof (H := proj1 (proj1 mark_once_deepbb_true_bwd_aux Ht' Hr)).
      exact (proj1 (proj1 mark_once_instr_true_bwd_aux H Hr)).
  - intro bb'; induction bb' as [ | bb1' ? Hrec1]; [easy | ].
    induction bb1' as [ | bb2' ? Hrec2];
      [now intros *? [<- | ]; [ | apply Hrec1]| ].
    induction bb2' as [ | * Hrec3].
    { intros *? [<- | ]; [ | now apply Hrec2; [ | right]].
      now intros [<- | ]; [ | apply (Hrec2 bb1'); [ | left | ]]. }
    intros * H [<- | Hin].
    + intros [<- | Hin].
      * intros [<- | Hin]; [now intros []%(Hrec _ _ _ _ _ H) | ].
        specialize (Hrec3 _ _ _ _ H (or_introl (eq_refl _)) (or_introl (eq_refl _)) Hin).
        now intros H'%Hrec3; destruct (mark_once_register_none_bwd H').
      * intros Hin' Hr.
        specialize (Hrec2 _ _ _ _ H (or_introl (eq_refl _)) Hin Hin' Hr).
        now destruct (mark_once_instr_none_bwd Hrec2).
    + intros H1 H2 H3%(Hrec1 _ _ _ _ H Hin H1 H2).
      now destruct (mark_once_deepbb_none_bwd H3).
Qed.

Lemma read_once_bb_true_bwd {bb r t n} :
  (read_once_bb t n bb) ! r = Some true ->
  t ! r = None <->
    exists bb1 bb2 i,
      In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  intro H; split.
  - now intro Ht; eapply (read_once_bb_none_fwd Ht); eauto.
  - intros [? [? [? [? [? []]]]]].
    now eauto using (proj2 read_once_bb_true_bwd_aux).
Qed.

Lemma read_once_bb_true_fwd {bb r t n} :
  t ! r = Some true ->
  (read_once_bb t n bb) ! r = Some false <->
    exists bb1 bb2 i,
      In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  revert t; induction bb as [ | bb1 ? Hrec]; simpl;
    [now intros ? ->; split; [ | intros [? [? []]]] | ].
  intros ? Ht; set (t' := _ _ t); destruct t' ! r as [b | ] eqn: Heq;
    [ | now rewrite (proj1 (mark_once_deepbb_none_bwd Heq)) in Ht].
  destruct b; split.
  - intro H; destruct (proj1 (Hrec _ Heq) H) as [? [? [? []]]].
    now eexists _, _, _; eauto.
  - intros [? [? [? [[<- | ] Hr]]]]; [ | now apply Hrec; eauto].
    now contradict Hr; eauto using (mark_once_deepbb_true Heq Ht).
  - destruct (proj1 (mark_once_deepbb_true_fwd Ht) Heq) as [? []].
    now eexists _, _; eauto.
  - now rewrite read_once_bb_false.
Qed.

Corollary read_once_bb_true {bb r t n} :
  (read_once_bb t n bb) ! r = Some true -> t ! r = Some true ->
  ~ exists bb1 bb2 i,
    In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  intros H%(read_once_bb_true_bwd (bb := bb))%not_iff_compat%proj1.
  now intro Ht; rewrite Ht in H; apply H.
Qed.

Lemma read_once_notin {f r} :
  (read_once f) ! r = None <->
  ~ exists pc bb bb1 bb2 i, (fn_code f) ! pc = Some bb
    /\ In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  unfold read_once; apply PTree_Properties.fold_ind.
  { rewrite PTree.gempty; intros ? Hrw.
    now split; [intros _ [? [? [? [? [? H]]]]]; rewrite Hrw in H | ]. }
  intros ?? pc0 ? Hrw _ Hrec; split.
  - intros [Hne%Hrec He]%read_once_bb_none_bwd [pc1 [? [? [? [? H]]]]].
    destruct (peq pc1 pc0) as [-> | Hneq];
      [rewrite Hrw in H; destruct H as [[=<-] ]; apply He; eauto | apply Hne].
    now eexists; rewrite (PTree.gro _ Hneq); eauto.
  - intro H; rewrite read_once_bb_notin;
      [ | now intros [? [? [? ]]]; apply H; eexists _, _; eauto].
    apply Hrec; intros [? [? [? [? [? [Hrm ]]]]]]; apply H.
    eexists _, _, _, _, _; split; [revert Hrm | eassumption].
    now rewrite PTree.grspec; destruct PTree.elt_eq; [ | intros ->].
Qed.

Lemma read_once_some {f r} :
  (exists b, (read_once f) ! r = Some b) <->
  exists pc bb bb1 bb2 i, (fn_code f) ! pc = Some bb
    /\ In bb1 bb /\ In bb2 bb1 /\ In i bb2 /\ In r (input_registers i).
Proof.
  unfold read_once; apply PTree_Properties.fold_ind.
  { rewrite PTree.gempty; intros ? Hrw.
    now split; [intros [?] | intros [? [? [? [? [? H]]]]]; rewrite Hrw in H]. }
  intros ? t pc ? Hrw _ Hrec; split; destruct t ! r as [b | ] eqn: Ht.
  - exploit (proj1 Hrec); [now eexists | intros [? [? [? [? [? [H ]]]]]]].
    now revert H; rewrite PTree.grspec; destruct peq; [ | eexists _, _; eauto].
  - rewrite (read_once_bb_none_fwd Ht); simplify.
    now eexists _, _, _, _, _; eauto.
  - now destruct (_ _ _ _) ! r eqn: Heq; [eauto
      | destruct (read_once_bb_none_bwd Heq) as [Ht' ]; rewrite Ht in Ht'].
  - rewrite (read_once_bb_none_fwd Ht).
    intros [pc' [? [? [? [? [Hm ]]]]]].
    destruct (peq pc' pc) as [-> | Hneq];
      [now rewrite Hrw in Hm; inv Hm; eexists _, _, _; eauto | ].
    exploit (proj2 Hrec); [ | now intros []].
    now eexists _, _; rewrite (PTree.gro _ Hneq); eauto.
Qed.

Lemma mapget_rs {vregs args rs rs'} :
  match_rs vregs rs rs' -> le_analysis (fl1mor args (PTree.empty _)) vregs ->
  rs ## args = rs' ## args.
Proof.
  intro Hrs; induction args as [ | r l Hrec]; [easy | ].
  intro Hle; simpl; rewrite Hrec
    by now eapply le_analysis_order, Hle; exact mark_once_register_mono_tl.
  f_equal; apply Hrs.
  destruct (proj2 (@mark_once_register_none_fwd (r::l) r _ (PTree.gempty _ _)))
    as [? Hfl]; [now left | ].
  now destruct (Hle _ _ Hfl) as [? ->]; eexists.
Qed.

Section WITH_GENV.
  Context A B (ge : Genv.t A B) (sp : val).
  Context (vregs : PTree.t bool).

  Lemma step_instr_rs i rs rs' trs ps ps' m m' :
    le_analysis (fl1mor (input_registers i) (PTree.empty _)) vregs ->
    match_rs vregs rs trs ->
    step_instr ge sp (Iexec (mki rs ps m)) i (Iexec (mki rs' ps' m')) ->
    exists trs', match_rs vregs rs' trs'
      /\ step_instr ge sp (Iexec (mki trs ps m)) i (Iexec (mki trs' ps' m')).
  Proof.
    intros Hle Hrs Hs; inv Hs; simpl in Hle.
    - now eexists; split; [ | apply exec_RBnop].
    - eexists; split; [ | apply exec_RBop; [rewrite <-(mapget_rs Hrs Hle) | ]];
        try eassumption.
      now intro; rewrite !Regmap.gsspec; intros ->%Hrs.
    - eexists; split; [ | eapply exec_RBload; [rewrite <-(mapget_rs Hrs Hle) | | ]];
        try eassumption.
      now intro; rewrite !Regmap.gsspec; intros ->%Hrs.
    - pose proof (Hle' := Relation_Definitions.ord_trans _ _ le_analysis_order _ _ _ mark_once_register_mono_tl Hle).
      eexists; split; [ | eapply exec_RBstore; [rewrite <-(mapget_rs Hrs Hle') | | ]];
        try eassumption.
      pose proof (Hle'' := Relation_Definitions.ord_trans _ _ le_analysis_order _ _ _ mark_once_register_mono Hle).
      pose proof (Hrw := mapget_rs (args := src::nil) Hrs Hle'').
      now inv Hrw.
    - eexists; split; [ | apply exec_RBsetpred; [rewrite <-(mapget_rs Hrs Hle) | ]];
        eassumption.
    - eexists; split; [ | apply exec_RB_falsy]; eassumption.
  Qed.

  Lemma step_instr_list_rs l :
    le_analysis (fl2mor l (PTree.empty _)) vregs ->
    forall rs rs' trs ps ps' m m',
    match_rs vregs rs trs ->
    ParBB.step_instr_list ge sp (Iexec (mki rs ps m)) l (Iexec (mki rs' ps' m')) ->
    exists trs', match_rs vregs rs' trs'
      /\ ParBB.step_instr_list ge sp (Iexec (mki trs ps m)) l (Iexec (mki trs' ps' m')).
  Proof.
    intro Hle; induction l as [ | * Hrec]; intros * Hrs Hs; inv Hs; simpl in Hle.
    { eexists; split; [eassumption | econstructor]. }
    destruct (step_list_inter_exec H5) as [[] ]; subst.
    pose proof (Hle' := Relation_Definitions.ord_trans _ _ le_analysis_order _ _ _ mark_once_instr_mono Hle).
    pose proof (Hle'' := Relation_Definitions.ord_trans _ _ le_analysis_order _ _ _ mark_once_instr_mono_tl Hle).
    destruct (step_instr_rs _ _ _ _ _ _ _ _ Hle' Hrs H3) as [? [Hrs' ]].
    destruct (Hrec Hle'' _ _ _ _ _ _ _ Hrs' H5) as [? []].
    eexists; split; [ | econstructor]; eassumption.
  Qed.

  Lemma step_instr_seq_rs l :
    le_analysis (fl3mor l (PTree.empty _)) vregs ->
    forall rs rs' trs ps ps' m m',
    match_rs vregs rs trs ->
    ParBB.step_instr_seq ge sp (Iexec (mki rs ps m)) l (Iexec (mki rs' ps' m')) ->
    exists trs', match_rs vregs rs' trs'
      /\ ParBB.step_instr_seq ge sp (Iexec (mki trs ps m)) l (Iexec (mki trs' ps' m')).
  Proof.
    intro Hle; induction l as [ | * Hrec]; intros * Hrs Hs; inv Hs; simpl in Hle.
    { eexists; split; [eassumption | econstructor]. }
    destruct (step_list_inter_exec H5) as [[] ]; subst.
    pose proof (Hle' := Relation_Definitions.ord_trans _ _ le_analysis_order _ _ _ mark_once_deepbb_mono Hle).
    pose proof (Hle'' := Relation_Definitions.ord_trans _ _ le_analysis_order _ _ _ mark_once_deepbb_mono_tl Hle).
    destruct (step_instr_list_rs _ Hle' _ _ _ _ _ _ _ Hrs H3) as [? [Hrs' ]].
    destruct (Hrec Hle'' _ _ _ _ _ _ _ Hrs' H5) as [? []].
    eexists; split; [ | econstructor]; eassumption.
  Qed.

  (* TODO: Iexec to Iterm and Iterm to Iterm? *)

End WITH_GENV.

Variant is_multiplier_instr : instr -> Prop :=
| Is_multiplier: forall p op rl r, is_multiplier op = true ->
  is_multiplier_instr (RBop p op rl r).

Lemma is_multiplier_instr_dec i :
  { is_multiplier_instr i } + { ~ is_multiplier_instr i }.
Proof.
  destruct i as [ | ? op | | | | ]; swap 1 2.
  { now destruct (is_multiplier op) eqn: Heq;
      [left | right; intro H; inv H; rewrite Heq in *]. }
  all: now right.
Qed.

Variant is_adder_instr : instr -> Prop :=
| Is_adder: forall p op rl r, is_adder op = true ->
  is_adder_instr (RBop p op rl r).

Lemma is_adder_instr_dec i :
  { is_adder_instr i } + { ~ is_adder_instr i }.
Proof.
  destruct i as [ | ? op | | | | ]; swap 1 2.
  { now destruct (is_adder op) eqn: Heq;
      [left | right; intro H; inv H; rewrite Heq in *]. }
  all: now right.
Qed.

Lemma intro_mac_nonmult i {vregs l} :
  ~ is_multiplier_instr i ->
  intro_mac_instr_list vregs (i::l) = i::intro_mac_instr_list vregs l.
Proof.
  intro H; unfold intro_mac_instr_list; simpl;
    set (acc := _ _ _ l); destruct acc; rewrite (surjective_pairing _); simpl.
  repeat (destruct_match; simplify; try easy).
  now contradict H.
Qed.

Lemma intro_mac_mult_nonadd i j {vregs l} :
  ~ is_adder_instr j ->
  intro_mac_instr_list vregs (i::j::l) = i::intro_mac_instr_list vregs (j::l).
Proof.
  intros H; unfold intro_mac_instr_list.
  assert (exists x, fold_right (intro_mac_instr vregs) (None, nil) (j::l)
    = (None, x)) as [? Heq].
  { simpl; set (acc := _ _ _ l); destruct acc; simpl; destruct j; eauto; [].
    now destruct is_adder eqn: Heq; [contradict H | eauto]. }
  revert Heq; simpl; intros ->; simpl.
  now destruct i; [ | destruct is_adder | | | | ].
Qed.

Definition match_prog (p: program) (tp: program) :=
  Linking.match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Section CORRECTNESS.

  Context (prog tprog : program).

  Let ge : genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

  Context (TRANSL : match_prog prog tprog).

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof using TRANSL. intros; eapply (Genv.senv_transf TRANSL). Qed.

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef f).
  Proof (Genv.find_funct_ptr_transf TRANSL).

  Lemma sig_transf_function:
    forall (f tf: fundef),
      funsig (transf_fundef f) = funsig f.
  Proof using.
    unfold transf_fundef. unfold AST.transf_fundef; intros. destruct f.
    unfold transf_function. auto. auto.
  Qed.

  (* TODO HERE *)

  Lemma test l vregs :
    le_analysis (fl2mor l (PTree.empty bool)) vregs ->
    forall sp rs ps m rs' ps' m',
    ParBB.step_instr_list ge sp (Iexec (mki rs ps m)) l (Iexec (mki rs' ps' m')) ->
    (forall r, vregs ! r = Some true ->
      (fl2mor l (PTree.empty _)) ! r = Some true
      \/ (fl2mor l (PTree.empty _)) ! r = None) ->
    forall trs, match_rs vregs rs trs ->
    exists trs', match_rs vregs rs' trs'
    /\ ParBB.step_instr_list ge sp (Iexec (mki trs ps m))
      (intro_mac_instr_list vregs l) (Iexec (mki trs' ps' m')).
  Proof.
    intro Hle.
    induction l as [ | i l Hrec]; simpl.
    { now intros * Hs; inv Hs; eexists; split; [ | constructor]. }
    intros * Hs; inv Hs; destruct (step_list_inter_exec H5) as [[rs0 ] ]; subst.
    specialize (Hrec _ _ _ _ _ _ _ H5); intro Hvregs; prove_assumption Hrec.
    { intros r [H | [_ ->%mark_once_instr_notin]%mark_once_instr_none_bwd]%Hvregs;
        [ | now right; apply PTree.gempty].
      destruct (in_dec peq r (input_registers i)) as [Hin | Hnin].
      - destruct (proj1 mark_once_instr_true_bwd_aux H Hin) as [_ Hnin].
        now rewrite (mark_once_instr_notin Hnin), PTree.gempty; right.
      - left; rewrite <-H; apply mark_once_instr_determ.
        now rewrite mark_once_register_notin. }
    intros ? Hm.
    step_instr_rs _ _ _ _ _ _ _ _ _ _ _ _ _ Hle
    destruct (is_multiplier_instr_dec i) as [Hm | Hnm]; revgoals.
    { rewrite (toto _ Hnm). intros ? ?%(Hrec _).
    (* cases: is i a multiply, then induction on l, is the new head an adder MORE LIKE HERE *)
    destruct i. simpl in Hrw. rewrite Hrw. specialize (Hrec rs0). revert Hrec.
    simpl. unfold match_rs at 1. rewrite PTree_Properties.for_all_correct.
    intro Hrec. prove_assumption Hrec. now intros; apply proj_sumbool_is_true.
    destruct Hrec as [? []]. inv H0.
    admit.
  Qed.

  (*Lemma functions_translated:
    forall (v: Values.val) (f: GibleSeq.fundef),
      Genv.find_funct ge v = Some f ->
      Genv.find_funct tge v = Some (transf_fundef f).
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto. simplify. eauto.
  Qed.

  Lemma find_function_translated:
    forall ros rs f,
      find_function ge ros rs = Some f ->
      find_function tge ros rs = Some (transf_fundef f).
  Proof using TRANSL.
    Ltac ffts := match goal with
                 | [ H: forall _, Val.lessdef _ _, r: Registers.reg |- _ ] =>
                     specialize (H r); inv H
                 | [ H: Vundef = ?r, H1: Genv.find_funct _ ?r = Some _ |- _ ] =>
                     rewrite <- H in H1
                 | [ H: Genv.find_funct _ Vundef = Some _ |- _] => solve [inv H]
                 | _ => solve [exploit functions_translated; eauto]
                 end.
    destruct ros; simplify; try rewrite <- H;
      [| rewrite symbols_preserved; destruct_match;
         try (apply function_ptr_translated); crush ];
      intros;
      repeat ffts.
  Qed.*)

  Lemma transf_initial_states :
    forall s1,
      initial_state prog s1 ->
      exists s2, initial_state tprog s2 /\ match_states s1 s2.
  Proof using TRANSL.
    induction 1.
    exploit function_ptr_translated; eauto; intros.
    do 2 econstructor; simplify. econstructor.
    apply (Genv.init_mem_transf TRANSL); eauto.
    replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
    symmetry; eapply Linking.match_program_main; eauto. eauto.
    erewrite sig_transf_function; eauto. constructor. auto.
  Qed.

  Lemma transf_final_states :
    forall s1 s2 r,
      match_states s1 s2 -> final_state s1 r -> final_state s2 r.
  Proof using.
    inversion 2; crush. subst. inv H. inv H5. econstructor.
  Qed.

  (*Lemma eval_op_eq:
    forall (sp0 : Values.val) (op : Op.operation) (vl : list Values.val) m,
      Op.eval_operation ge sp0 op vl m = Op.eval_operation tge sp0 op vl m.
  Proof using TRANSL.
    intros.
    destruct op; auto; unfold Op.eval_operation, Genv.symbol_address, Op.eval_addressing32;
    [| destruct a; unfold Genv.symbol_address ];
    try rewrite symbols_preserved; auto.
  Qed.

  Lemma eval_addressing_eq:
    forall sp addr vl,
      Op.eval_addressing ge sp addr vl = Op.eval_addressing tge sp addr vl.
  Proof using TRANSL.
    intros.
    destruct addr;
      unfold Op.eval_addressing, Op.eval_addressing32;
      unfold Genv.symbol_address;
      try rewrite symbols_preserved; auto.
  Qed.

  Lemma step_instr_ge :
    forall sp i a i',
      step_instr ge sp i a i' ->
      step_instr tge sp i a i'.
  Proof using TRANSL.
    inversion 1; subst; simplify; clear H; econstructor; eauto;
      try (rewrite <- eval_op_eq; auto); rewrite <- eval_addressing_eq; auto.
  Qed.*)

  (*#[local] Hint Resolve eval_builtin_args_preserved : core.*)
  (*#[local] Hint Resolve symbols_preserved : core.*)
  #[local] Hint Resolve external_call_symbols_preserved : core.
  #[local] Hint Resolve senv_preserved : core.
  (*#[local] Hint Resolve find_function_translated : core.*)
  (*#[local] Hint Resolve sig_transf_function : core.*)

  (*Lemma step_cf_instr_ge :
    forall st cf t st' tst,
      step_cf_instr ge st cf t st' ->
      match_states st tst ->
      exists tst', step_cf_instr tge tst cf t tst' /\ match_states st' tst'.
  Proof using TRANSL.
    inversion 1; subst; simplify; clear H;
      match goal with H: context[match_states] |- _ => inv H end;
      repeat (econstructor; eauto).
  Qed.

  Lemma step_list2_ge :
    forall sp l i i',
      step_list2 (step_instr ge) sp i l i' ->
      step_list2 (step_instr tge) sp i l i'.
  Proof using TRANSL.
    induction l; simplify; inv H.
    - constructor.
    - econstructor. apply step_instr_ge; eauto.
      eauto.
  Qed.

  Lemma step_list_ge :
    forall sp l i i',
      step_list (step_instr ge) sp i l i' ->
      step_list (step_instr tge) sp i l i'.
  Proof using TRANSL.
    induction l; simplify; inv H.
    - eauto using exec_RBcons, step_instr_ge.
    - eauto using exec_RBterm, step_instr_ge.
  Qed.

  Lemma elim_cond_s_wf_predicate :
    forall a p p0 l v,
      elim_cond_s p a = (p0, l) ->
      wf_predicate v p ->
      wf_predicate v p0.
  Proof using.
    destruct a; simplify; try match goal with H: (_, _) = (_, _) |- _ => inv H end; auto.
    destruct c; simplify; try match goal with H: (_, _) = (_, _) |- _ => inv H end; auto.
    unfold wf_predicate in *; lia.
  Qed.

  Lemma replace_section_wf_predicate :
    forall bb v p t0 p0,
      replace_section elim_cond_s p bb = (p0, t0) ->
      wf_predicate v p ->
      wf_predicate v p0.
  Proof using.
    induction bb; crush; repeat (destruct_match; crush).
    inv H.
    exploit IHbb; eauto; simplify.
    eapply elim_cond_s_wf_predicate in Heqp2; eauto.
  Qed.

  Lemma elim_cond_s_spec2 :
    forall rs m rs' m' ps tps ps' p a p0 l cf stk f sp pc t st tstk,
      step_instr ge sp (Iexec (mki rs ps m)) a (Iterm (mki rs' ps' m') cf) ->
      step_cf_instr ge (State stk f sp pc rs' ps' m') cf t st ->
      Forall (fun p => p <= (max_pred_function f)) (pred_uses a) ->
      match_ps (max_pred_function f) ps tps ->
      wf_predicate (max_pred_function f) p ->
      elim_cond_s p a = (p0, l) ->
      Forall2 match_stackframe stk tstk ->
      exists tps' cf' st',
        SeqBB.step tge sp (Iexec (mki rs tps m)) l (Iterm (mki rs' tps' m') cf')
        /\ match_ps (max_pred_function f) ps' tps'
        /\ step_cf_instr tge (State tstk (transf_function f) sp pc rs' tps' m') cf' t st'
        /\ match_states st st'.
  Proof using TRANSL.
    inversion 1; subst; simplify.
    destruct cf;
      try (inv H5; exploit step_cf_instr_ge; eauto; [econstructor|]; eauto; simplify;
           do 3 econstructor; simplify; eauto;
           constructor; constructor; eapply truthy_match_ps; eauto;
           intros; match goal with H: _ = Some _ |- _ => inv H end; auto).
    inv H0; destruct b.
    + inv H5; do 3 econstructor; simplify.
      econstructor. econstructor; eauto.
      eapply truthy_match_ps; eauto; intros; match goal with H: _ = Some _ |- _ => inv H end; auto.
      constructor.
      econstructor. simplify. destruct p1.
      constructor. inv H4. eapply eval_predf_in_ps; eauto.
      constructor. unfold eval_predf; simplify. rewrite Pos2Nat.id.
      apply PMap.gss.
      apply match_ps_set_gt; auto.
      constructor; auto.
      constructor; auto.
      apply match_ps_set_gt; auto.
    + inv H5; do 3 econstructor; simplify.
      econstructor. econstructor; eauto.
      eapply truthy_match_ps; eauto; intros; match goal with H: _ = Some _ |- _ => inv H end; auto.
      econstructor. eapply exec_RB_falsy. simplify. destruct p1.
      constructor. inv H4. eapply eval_predf_in_ps2; eauto.
      constructor. unfold eval_predf; simplify. rewrite Pos2Nat.id. apply PMap.gss.
      constructor. econstructor. inv H4. constructor. unfold eval_predf; simplify.
      rewrite Pos2Nat.id. rewrite PMap.gss. auto.
      constructor. eapply eval_predf_in_ps; eauto.
      apply match_ps_set_gt; auto.
      constructor; auto.
      constructor; auto.
      apply match_ps_set_gt; auto.
  Qed.*)

  Lemma intro_mac_fold_spec f pc bb:
    f.(fn_code) ! pc = Some bb ->
    forall sp rs ps m rs' ps' m' trs cf stk t st stk',
    ParBB.step ge sp (Iexec (mki rs ps m)) bb (Iterm (mki rs' ps' m') cf) ->
    step_cf_instr ge (State stk f sp pc rs' ps' m') cf t st ->
    Forall2 match_stackframe stk stk' ->
    match_rs (read_once (transf_function f)) rs trs == true ->
    exists st' trs' cf',
      ParBB.step tge sp (Iexec (mki trs ps m)) (intro_mac_bb (read_once f) bb) (Iterm (mki trs' ps' m') cf')
      /\ match_rs (read_once (transf_function f)) rs' trs' == true
      /\ step_cf_instr tge (State stk' (transf_function f) sp pc trs' ps' m') cf' t st'
      /\ match_states st st'.
  Proof using TRANSL.
    intro Hpc.
    apply (forall_in (fun bb1 => True) bb); [intros * H; inv H | | ].
    - intros bb1 ? Hx Hm * Hs Hcf Hstk Hrs.
      inversion Hs as [?? [] ???? Hsiq Hs'| ?????? Hsiq]; clear Hs; subst.
      2: { inv Hsiq. eexists _, _, _. split. simpl. econstructor. econstructor.
      (* ParBB.step_instr_list ge sp (Iexec (mki rs ps m)) (i::bb2) is ->
        (forall is, ParBB.step_instr_list ge sp is bb2 is')
          ParBB.step_instr_list ge sp (Iexec (mki rs ps m)) (intro_mac_instr_list bb2) is) ->
        ParBB.step_instr_list ge sp (Iexec (mki rs ps m)) (intro_mac_instr_list (i::bb2)) i1 *)
      specialize (fun rs => Hm _ _ _ _ _ _ _ rs _ _ _ _ _ Hs' Hcf Hstk).
      induction bb1 as [ | bb2 ? Hrec]. admit.
      inv Hsiq.
      (* induction bb1. induction bb2. *)
    
     Hrs inv H5. inv H0. destruct i2. simpl. eexists _, _, _. split. econstructor.
    (* Not provable unless additionnal hyp *)
    induction bb. as [ | bb1 bb Hrec]; [now intros * H; inv H | ].
    induction bb1 as [ | bb2 bb1 Hrec1].
    { intros; inv H; [inv H8 | inv H6].
      edestruct Hrec as [? [? []]];
        [eassumption | eassumption | eassumption | eassumption | ].
      now eexists _, _, _; simplify; eauto; econstructor; [constructor | ]. }
    induction bb2 as [ | i bb2 Hrec2].
    { intros; edestruct Hrec1 as [? [? []]];
        [inv H | eassumption | eassumption | eassumption | ].
      { inv H8; inv H6; eapply exec_RBcons; eassumption. }
      { inv H6; inv H7; eapply exec_RBterm; eassumption. }
      eexists _, _, _; simplify;
        [inv H4 | eassumption | eassumption | eassumption].
      - now eapply exec_RBcons, H14; econstructor; [constructor | ].
      - now eapply exec_RBterm, exec_term_RBcons; [constructor | ]. }
    intros sp rs ps m * Hs Hcf Hstk Hps.
    (* TODO: Case on whether i terminates the program or not *)
    
    assert (exists is1 is2 is3, step_instr ge sp (Iexec (mki rs ps m)) i is1
      /\ step_list_inter (step_instr ge) sp is1 bb2 is2
      /\ step_list_inter (ParBB.step_instr_list ge) sp is2 bb1 is3)
      as [is1 [is2 [is3 [Hi [Hbb2 Hbb1]]]]]
      by now inv Hs; [inv H4; inv H3 | inv H2; inv H4]; eexists _, _, _; eauto.
    destruct is1. admit.
    inv Hs. (* step_list_inter_false *)
    inv H4; inv H3; rewrite (step_instr_determ H4 Hi) in H8.
    rewrite (step_list_inter_term H8) in H7.
    now pose proof (step_list_inter_term H7).
    inv H2. inv H4. rewrite (step_instr_determ H3 Hi) in H7.
    rewrite (step_list_inter_term H7) in H6.
    pose proof (Heq := step_list_inter_term H6).
    inv Heq.
    
    inv Hs. inv H4. destruct (step_list_inter_exec H7) as [? ->]. inv H3.
    inv H8. now destruct i; inv Hi; inv H4; inv H5; inv H2; rewrite H1 in H0.

    epose proof (Hrw := toto i); inv Hi; simpl in *; rewrite Hrw.
    eexists _, _, _. split. eapply exec_RBterm, exec_term_RBcons.
    econstructor. econstructor. admit. constructor. exec_term_RBcons_term.
    constructor.
    
    destruct bb1.

    admit.
    
    inv Hi. simpl.
    
    admit.
    
    (*not*) edestruct Hrec2 as [? [? []]];
      [inv H | eassumption | eassumption | | ]; swap 0 2.
    { inv H6; inv H7; inv H10. 
      destruct i0.
       eapply exec_RBterm, exec_term_RBcons, H9.
          econstructor. exact H3.
      admit. }
    { inv H8; inv H6; eapply exec_RBcons, H10; eapply exec_term_RBcons, H9.
      admit. }
    
  Qed.

  (*Definition lt_pred (c: code) (m: positive) :=
    forall pc bb n,
      c ! pc = Some bb ->
      m = max_pred_block m n bb \/ m < max_pred_block 1 n bb.

  Definition lt_pred2 (c: code) (m: positive) :=
    forall pc bb n,
      c ! pc = Some bb ->
      max_pred_block 1 n bb <= m.

  Lemma elim_cond_s_lt :
    forall p a p0 l x,
      elim_cond_s p a = (p0, l) ->
      p0 <= x ->
      p <= x.
  Proof using.
    destruct a; crush; destruct c; crush.
    inv H. lia.
  Qed.

  Lemma replace_section_lt :
    forall t p1 p0 t2 x,
      replace_section elim_cond_s p1 t = (p0, t2) ->
      p0 <= x ->
      p1 <= x.
  Proof using.
    induction t; crush; repeat destruct_match. inv H.
    eapply IHt; eauto.
    eapply elim_cond_s_lt; eauto.
  Qed.

  Lemma pred_not_in :
    forall l pc p t p' t' x,
      ~ In pc (map fst l) ->
      fold_left (fun a p => elim_cond_fold a (fst p) (snd p)) l (p, t) = (p', t') ->
      t ! pc = x -> t' ! pc = x.
  Proof using.
    induction l; crush.
    repeat destruct_match.
    eapply IHl; eauto. rewrite PTree.gso; auto.
  Qed.

  Lemma pred_greater :
    forall l pc x v p' t',
      In (pc, x) l ->
      list_norepet (map fst l) ->
      fold_left (fun a p => elim_cond_fold a (fst p) (snd p)) l v = (p', t') ->
      exists p, t' ! pc = Some (snd (replace_section elim_cond_s p x))
                /\ (fst v) <= p.
  Proof.
    induction l; crush.
    inv H0. destruct a; simplify. inv H. inv H0.
    remember (elim_cond_fold v pc x). destruct p.
    eapply pred_not_in in H1; eauto. symmetry in Heqp.
    unfold elim_cond_fold in Heqp. repeat destruct_match. inv Heqp0. inv Heqp.
    simplify. econstructor. split. rewrite PTree.gss in H1.
    rewrite Heqp1. eauto. lia.
    remember (elim_cond_fold v p t). destruct p0. symmetry in Heqp0.
    unfold elim_cond_fold in Heqp0. repeat destruct_match. inv Heqp0.
    exploit IHl; eauto; simplify.
    econstructor; simplify. eauto.
    eapply replace_section_lt; eauto.
  Qed.*)

  Lemma transf_block_spec f pc x :
    f.(fn_code) ! pc = Some x ->
    (transf_function f).(fn_code) ! pc = Some (intro_mac_bb (read_once f) x).
  Proof using.
    unfold transf_function, ParBB.t; simpl.
    apply PTree_Properties.fold_ind; [now intros ? -> | ].
    intros ?? pc' ?; case (peq pc pc') as [<- | Hneq].
    - intros -> _ _ H; inv H.
      now unfold transf_bb; rewrite PTree.gss.
    - rewrite (PTree.gro _ Hneq); intros Hpc' _ H <-%H.
      now unfold transf_bb; rewrite (PTree.gso _ _ Hneq).
  Qed.

  Lemma transf_step_correct:
    forall s1 t s1',
      step ge s1 t s1' ->
      forall s2,
        match_states s1 s2 ->
        exists s2', step tge s2 t s2' /\ match_states s1' s2'.
  Proof using TRANSL.
    induction 1; intros.
    + inv H2.
      exploit transf_block_spec; eauto.
      simplify.
      exploit intro_mac_fold_spec; eauto.
      simplify. econstructor.
      simplify. econstructor; eauto. auto.
    + inv H0. econstructor.
      simplify. econstructor; eauto. constructor; eauto.
      unfold match_rs; simpl; rewrite PTree_Properties.for_all_correct.
      now intros; apply proj_sumbool_is_true.
    + inv H0. do 3 econstructor; eauto.
    + inv H. inv H4. inv H1. do 3 econstructor; eauto.
      unfold match_rs; simpl; rewrite PTree_Properties.for_all_correct.
      now intros; apply proj_sumbool_is_true.
  Qed.

  Theorem transf_program_correct:
    forward_simulation (semantics prog) (semantics tprog).
  Proof using TRANSL.
    eapply forward_simulation_step.
    + apply senv_preserved.
    + apply transf_initial_states.
    + apply transf_final_states.
    + apply transf_step_correct.
  Qed.

End CORRECTNESS.
