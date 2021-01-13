(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

From compcert Require Import AST Maps.
From vericert Require Import Vericertlib RTLBlock RTLPar Scheduleoracle.

Fixpoint beq {A B : Type} (beqA : A -> B -> bool) (m1 : PTree.t A) (m2 : PTree.t B) {struct m1} : bool :=
  match m1, m2 with
  | PTree.Leaf, _ => PTree.bempty m2
  | _, PTree.Leaf => PTree.bempty m1
  | PTree.Node l1 o1 r1, PTree.Node l2 o2 r2 =>
    match o1, o2 with
    | None, None => true
    | Some y1, Some y2 => beqA y1 y2
    | _, _ => false
    end
    && beq beqA l1 l2 && beq beqA r1 r2
  end.

Lemma beq_correct:
  forall A B beqA m1 m2,
    @beq A B beqA m1 m2 = true <->
    (forall (x: PTree.elt),
        match PTree.get x m1, PTree.get x m2 with
        | None, None => True
        | Some y1, Some y2 => beqA y1 y2 = true
        | _, _ => False
        end).
Proof.
  induction m1; intros.
  - simpl. rewrite PTree.bempty_correct. split; intros.
    rewrite PTree.gleaf. rewrite H. auto.
    generalize (H x). rewrite PTree.gleaf. destruct (PTree.get x m2); tauto.
  - destruct m2.
    + unfold beq. rewrite PTree.bempty_correct. split; intros.
      rewrite H. rewrite PTree.gleaf. auto.
      generalize (H x). rewrite PTree.gleaf. destruct (PTree.get x (PTree.Node m1_1 o m1_2)); tauto.
    + simpl. split; intros.
      * destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0).
        rewrite IHm1_1 in H3. rewrite IHm1_2 in H1.
        destruct x; simpl. apply H1. apply H3.
        destruct o; destruct o0; auto || congruence.
      * apply andb_true_intro. split. apply andb_true_intro. split.
        generalize (H xH); simpl. destruct o; destruct o0; tauto.
        apply IHm1_1. intros; apply (H (xO x)).
        apply IHm1_2. intros; apply (H (xI x)).
Qed.

Parameter schedule : RTLBlock.function -> RTLPar.function.

Definition transl_function (f : RTLBlock.function) : Errors.res RTLPar.function :=
  let tf := schedule f in
  if beq schedule_oracle f.(RTLBlock.fn_code) tf.(fn_code) then
    Errors.OK tf
  else
    Errors.Error (Errors.msg "RTLPargen: Could not prove the blocks equivalent.").

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : RTLBlock.program) : Errors.res RTLPar.program :=
  transform_partial_program transl_fundef p.
