(*
 * CoqUp: Verified high-level synthesis.
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

From compcert Require Import Smallstep Linking Integers.
From coqup Require HTL.
From coqup Require Import Coquplib Veriloggen Verilog ValueInt AssocMap.
Require Import Lia.

Local Open Scope assocmap.

Definition match_prog (prog : HTL.program) (tprog : Verilog.program) :=
  match_program (fun cu f tf => tf = transl_fundef f) eq prog tprog.

Lemma transf_program_match:
  forall prog, match_prog prog (transl_program prog).
Proof.
  intros. eapply match_transform_program_contextual. auto.
Qed.

Inductive match_stacks : list HTL.stackframe -> list stackframe -> Prop :=
| match_stack :
    forall res m pc reg_assoc arr_assoc hstk vstk,
      match_stacks hstk vstk ->
      match_stacks (HTL.Stackframe res m pc reg_assoc arr_assoc :: hstk)
                   (Stackframe res (transl_module m) pc
                                       reg_assoc arr_assoc :: vstk)
| match_stack_nil : match_stacks nil nil.

Inductive match_states : HTL.state -> state -> Prop :=
| match_state :
    forall m st reg_assoc arr_assoc hstk vstk,
      match_stacks hstk vstk ->
      match_states (HTL.State hstk m st reg_assoc arr_assoc)
                   (State vstk (transl_module m) st reg_assoc arr_assoc)
| match_returnstate :
    forall v hstk vstk,
      match_stacks hstk vstk ->
      match_states (HTL.Returnstate hstk v) (Returnstate vstk v)
| match_initial_call :
    forall m,
      match_states (HTL.Callstate nil m nil) (Callstate nil (transl_module m) nil).

Lemma Vlit_inj :
  forall a b, Vlit a = Vlit b -> a = b.
Proof. inversion 1. trivial. Qed.

Lemma posToValue_inj :
  forall a b,
    0 <= Z.pos a <= Int.max_unsigned ->
    0 <= Z.pos b <= Int.max_unsigned ->
    posToValue a = posToValue b ->
    a = b.
Proof.
  intros. rewrite <- Pos2Z.id at 1. rewrite <- Pos2Z.id.
  rewrite <- Int.unsigned_repr at 1; try assumption.
  symmetry.
  rewrite <- Int.unsigned_repr at 1; try assumption.
  unfold posToValue in *. rewrite H1; auto.
Qed.

Lemma valueToPos_inj :
  forall a b,
    0 < Int.unsigned a ->
    0 < Int.unsigned b ->
    valueToPos a = valueToPos b ->
    a = b.
Proof.
  intros. unfold valueToPos in *.
  rewrite <- Int.repr_unsigned at 1.
  rewrite <- Int.repr_unsigned.
  apply Pos2Z.inj_iff in H1.
  rewrite Z2Pos.id in H1; auto.
  rewrite Z2Pos.id in H1; auto.
  rewrite H1. auto.
Qed.

Lemma transl_list_fun_fst :
  forall p1 p2 a b,
    0 <= Z.pos p1 <= Int.max_unsigned ->
    0 <= Z.pos p2 <= Int.max_unsigned ->
    transl_list_fun (p1, a) = transl_list_fun (p2, b) ->
    (p1, a) = (p2, b).
Proof.
  intros. unfold transl_list_fun in H1. apply pair_equal_spec in H1.
  destruct H1. rewrite H2. apply Vlit_inj in H1.
  apply posToValue_inj in H1; try assumption.
  rewrite H1; auto.
Qed.

Lemma transl_in :
  forall l p,
  0 <= Z.pos p <= Int.max_unsigned ->
  (forall p0, In p0 (List.map fst l) -> 0 <= Z.pos p0 <= Int.max_unsigned) ->
  In (Vlit (posToValue p)) (map fst (map transl_list_fun l)) ->
  In p (map fst l).
Proof.
  induction l.
  - simplify. auto.
  - intros. destruct a. simplify. destruct (peq p0 p); auto.
    right. inv H1. apply Vlit_inj in H. apply posToValue_inj in H; auto. contradiction.
    apply IHl; auto.
Qed.

Lemma transl_notin :
  forall l p,
    0 <= Z.pos p <= Int.max_unsigned ->
    (forall p0, In p0 (List.map fst l) -> 0 <= Z.pos p0 <= Int.max_unsigned) ->
    ~ In p (List.map fst l) -> ~ In (Vlit (posToValue p)) (List.map fst (transl_list l)).
Proof.
  induction l; auto. intros. destruct a. unfold not in *. intros.
  simplify.
  destruct (peq p0 p). apply H1. auto. apply H1.
  unfold transl_list in *. inv H2. apply Vlit_inj in H. apply posToValue_inj in H.
  contradiction.
  apply H0; auto. auto.
  right. apply transl_in; auto.
Qed.

Lemma transl_norepet :
  forall l,
    (forall p0, In p0 (List.map fst l) -> 0 <= Z.pos p0 <= Int.max_unsigned) ->
    list_norepet (List.map fst l) -> list_norepet (List.map fst (transl_list l)).
Proof.
  induction l.
  - intros. simpl. apply list_norepet_nil.
  - destruct a. intros. simpl. apply list_norepet_cons.
    inv H0. apply transl_notin. apply H. simplify; auto.
    intros. apply H. destruct (peq p0 p); subst; simplify; auto.
    assumption. apply IHl. intros. apply H. destruct (peq p0 p); subst; simplify; auto.
    simplify. inv H0. assumption.
Qed.

Section CORRECTNESS.

  Variable prog: HTL.program.
  Variable tprog: program.

  Hypothesis TRANSL : match_prog prog tprog.

  Lemma transl_list_correct :
  forall l v ev f asr asa asrn asan asr' asa' asrn' asan',
    (forall p0, In p0 (List.map fst l) -> 0 <= Z.pos p0 <= Int.max_unsigned) ->
    list_norepet (List.map fst l) ->
    asr!ev = Some v ->
    (forall p s,
      In (p, s) l ->
      v = posToValue p ->
      stmnt_runp f
                 {| assoc_blocking := asr; assoc_nonblocking := asrn |}
                 {| assoc_blocking := asa; assoc_nonblocking := asan |}
                 s
                 {| assoc_blocking := asr'; assoc_nonblocking := asrn' |}
                 {| assoc_blocking := asa'; assoc_nonblocking := asan' |} ->
      stmnt_runp f
                 {| assoc_blocking := asr; assoc_nonblocking := asrn |}
                 {| assoc_blocking := asa; assoc_nonblocking := asan |}
                 (Vcase (Vvar ev) (transl_list l) (Some Vskip))
                 {| assoc_blocking := asr'; assoc_nonblocking := asrn' |}
                 {| assoc_blocking := asa'; assoc_nonblocking := asan' |}).
  Proof.
    induction l as [| a l IHl].
    - contradiction.
    - intros v ev f asr asa asrn asan asr' asa' asrn' asan' BOUND NOREP ASSOC p s IN EQ SRUN.
      destruct a as [p' s']. simplify.
      destruct (peq p p'); subst. eapply stmnt_runp_Vcase_match.
      constructor. simplify. unfold AssocMap.find_assocmap, AssocMapExt.get_default.
      rewrite ASSOC. trivial. constructor. auto.
      inversion IN as [INV | INV]. inversion INV as [INV2]; subst. assumption.
      inv NOREP. eapply in_map with (f := fst) in INV. contradiction.

      eapply stmnt_runp_Vcase_nomatch. constructor. simplify.
      unfold AssocMap.find_assocmap, AssocMapExt.get_default. rewrite ASSOC.
      trivial. constructor. unfold not. intros. apply n. apply posToValue_inj.
      apply BOUND. right. inv IN. inv H0; contradiction. eapply in_map with (f := fst) in H0. auto.
      apply BOUND; auto. auto.

      eapply IHl. auto. inv NOREP. auto. eassumption. inv IN. inv H. contradiction. apply H.
      trivial. assumption.
  Qed.

  Lemma mis_stepp_decl :
    forall l asr asa f,
      mis_stepp f asr asa l asr asa.
  Admitted.

  Let ge : HTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

  Theorem transl_step_correct :
    forall (S1 : HTL.state) t S2,
      HTL.step ge S1 t S2 ->
      forall (R1 : state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; intros R1 MSTATE; inv MSTATE.
    - econstructor; split. apply Smallstep.plus_one. econstructor.
      assumption. assumption. eassumption. trivial.
      econstructor. econstructor. eapply stmnt_runp_Vcond_false. econstructor. econstructor.
      simpl. unfold find_assocmap. unfold AssocMapExt.get_default.
      rewrite H. trivial.

      econstructor. simpl. auto. auto.

      eapply transl_list_correct.
      assert (forall p0 : positive, In p0 (map fst (Maps.PTree.elements (HTL.mod_controllogic m)))
                                    -> 0 <= Z.pos p0 <= Int.max_unsigned) by admit; auto.
      apply Maps.PTree.elements_keys_norepet. eassumption.
      2: { apply valueToPos_inj. assert (0 < Int.unsigned ist) by admit; auto.
      admit. rewrite valueToPos_posToValue.  trivial. admit. }
      apply Maps.PTree.elements_correct. eassumption. eassumption.

      econstructor. econstructor.

      eapply transl_list_correct.
      assert (forall p0 : positive, In p0 (map fst (Maps.PTree.elements (HTL.mod_datapath m)))
                                    -> 0 <= Z.pos p0 <= Int.max_unsigned) by admit; auto.
      apply Maps.PTree.elements_keys_norepet. eassumption.
      2: { apply valueToPos_inj. assert (0 < Int.unsigned ist) by admit; auto.
      admit. rewrite valueToPos_posToValue.  trivial. admit. }
      apply Maps.PTree.elements_correct. eassumption. eassumption.

      apply mis_stepp_decl. trivial. trivial. simpl. eassumption. auto.
      constructor; assumption.

    - econstructor; split. apply Smallstep.plus_one. apply step_finish. assumption. eassumption.
      constructor; assumption.
    - econstructor; split. apply Smallstep.plus_one. constructor.

      constructor. constructor.
    - inv H3. econstructor; split. apply Smallstep.plus_one. constructor. trivial.

      apply match_state. assumption.
  Admitted.

  Theorem transf_program_correct:
    forward_simulation (HTL.semantics prog) (Verilog.semantics tprog).
    Admitted.


End CORRECTNESS.

