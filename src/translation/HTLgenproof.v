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

From coqup Require Import HTLgenspec Value AssocMap.
From coqup Require HTL Verilog.
From compcert Require RTL Registers Globalenvs AST.

Import AssocMapNotation.

Inductive match_assocmaps : RTL.regset -> assocmap -> Prop :=
| match_assocmap : forall rs am,
    (forall r, val_value_lessdef (Registers.Regmap.get r rs) am#r) ->
    match_assocmaps rs am.

Definition state_st_wf (m : HTL.module) (s : HTL.state) :=
  forall st assoc,
  s = HTL.State m st assoc ->
  assoc!(m.(HTL.mod_st)) = Some (posToValue 32 st).

Inductive match_states : RTL.state -> HTL.state -> Prop :=
| match_state : forall (rs : RTL.regset) assoc sf f sp rs mem m st
    (MASSOC : match_assocmaps rs assoc)
    (TF : tr_module f m)
    (TC : tr_code f.(RTL.fn_code) st m.(HTL.mod_datapath) m.(HTL.mod_controllogic)
                  m.(HTL.mod_finish) m.(HTL.mod_return) m.(HTL.mod_st))
    (WF : state_st_wf m (HTL.State m st assoc)),
    match_states (RTL.State sf f sp st rs mem)
                 (HTL.State m st assoc)
| match_returnstate : forall v v' stack m,
    val_value_lessdef v v' ->
    match_states (RTL.Returnstate stack v m) (HTL.Returnstate v').

Inductive match_program : RTL.program -> HTL.module -> Prop :=
  match_program_intro :
    forall ge p b m f,
    ge = Globalenvs.Genv.globalenv p ->
    Globalenvs.Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
    tr_module f m ->
    match_program p m.

Lemma regs_lessdef_regs :
  forall rs1 rs2 n v,
    match_assocmaps rs1 rs2 ->
    match_assocmaps rs1 (AssocMap.add n v rs2).
Admitted.

Lemma regs_add_match :
  forall rs am r v v',
    match_assocmaps rs am ->
    val_value_lessdef v v' ->
    match_assocmaps (Registers.Regmap.set r v rs) (AssocMap.add r v' am).
Admitted.

Lemma merge_inj :
  forall am am' r v,
    merge_assocmap (AssocMap.add r v am) am' = AssocMap.add r v (merge_assocmap am am').
Admitted.

Lemma valToValue_lessdef :
  forall v,
    val_value_lessdef v (valToValue v).
Admitted.

Lemma assocmap_merge_add :
  forall k v assoc,
    AssocMap.add k v assoc = merge_assocmap (AssocMap.add k v empty_assocmap) assoc.
Admitted.

(* Need to eventually move posToValue 32 to posToValueAuto, as that has this proof. *)
Lemma assumption_32bit :
  forall v,
    valueToPos (posToValue 32 v) = v.
Admitted.

Lemma regset_assocmap_get :
  forall r rs am v v',
    match_assocmaps rs am ->
    v = Registers.Regmap.get r rs ->
    v' = am#r ->
    val_value_lessdef v v'.
Proof. inversion 1. intros. subst. apply H0. Qed.

Lemma regset_assocmap_wf :
  forall r rs am i,
    match_assocmaps rs am ->
    Values.Vint i <> Registers.Regmap.get r rs ->
    am!r = None.
Admitted.

Lemma regset_assocmap_wf2 :
  forall r rs am i,
    match_assocmaps rs am ->
    Values.Vint i = Registers.Regmap.get r rs ->
    am!r = Some (intToValue i).
Admitted.

Lemma access_merge_assocmap :
  forall nb r v am,
  nb!r = Some v ->
  (merge_assocmap nb am) ! r = Some v.
Admitted.

Lemma st_greater_than_res :
  forall m res,
    (HTL.mod_st m) <> res.
Admitted.

Ltac subst_eq_hyp :=
  match goal with
    H1: ?x = Some ?i, H2: ?x = Some ?j |- _ =>
    let H := fresh "H" in
    rewrite H1 in H2; injection H2; intro H; clear H2; subst
  end.

Section CORRECTNESS.

  Variable prog : RTL.program.
  Variable tprog : HTL.module.

  Hypothesis TRANSL : match_program prog tprog.

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : HTL.genv := HTL.genv_empty.

  Lemma eval_correct :
    forall sp op rs args m v e assoc f,
      Op.eval_operation ge sp op
(List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some v ->
      tr_op op args e ->
      Verilog.expr_runp f assoc e (valToValue v).
  Admitted.

  (** The proof of semantic preservation for the translation of instructions
      is a simulation argument based on diagrams of the following form:
<<
                      match_states
    code st rs ---------------- State m st assoc
         ||                             |
         ||                             |
         ||                             |
         \/                             v
    code st rs' --------------- State m st assoc'
                      I
>>
      where [tr_code c data control fin rtrn st] is assumed to hold.

      The precondition and postcondition is that that should hold is [match_assocmaps rs assoc].
   *)

  Definition transl_instr_prop (instr : RTL.instruction) : Prop :=
    forall m assoc fin rtrn st stmt trans,
      tr_instr fin rtrn st instr stmt trans ->
      exists assoc',
        HTL.step tge (HTL.State m st assoc) Events.E0 (HTL.State m st assoc').

  Theorem transl_step_correct:
    forall (S1 : RTL.state) t S2,
      RTL.step ge S1 t S2 ->
      forall (R1 : HTL.state),
        match_states S1 R1 ->
        exists R2, HTL.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; intros R1 MSTATE.
    - (* Inop *)
      inversion MSTATE. subst.
      econstructor.
      split.

      inversion TC.
      eapply HTL.step_module; subst_eq_hyp; remember (HTL.mod_st m0) as st; inversion H3; subst.
      apply H2.
      apply H1.
      (* processing of state *)
      econstructor.
      simpl. trivial.
      econstructor. trivial.
      inversion H3. subst.
      econstructor.

      (* prove merge *)
      apply assocmap_merge_add.

      (* prove stval *)
      apply AssocMap.gss.
      apply assumption_32bit.

      (* prove match_state *)
      constructor.
      apply rs.
      apply regs_lessdef_regs.
      assumption.
      inversion TF. simpl. apply H0.
      assumption.
      unfold state_st_wf. intros. inversion H0. subst.
      apply AssocMap.gss.
    - (* Iop *)
      inversion MSTATE. subst.
      econstructor.
      split.

      inversion TC.
      eapply HTL.step_module; subst_eq_hyp; remember (HTL.mod_st m0) as st; inversion H4; subst.
      apply H3.
      apply H2.
      econstructor.
      simpl. trivial.
      constructor. trivial.
      econstructor.
      simpl. trivial.
      eapply eval_correct. apply H0. apply H10. trivial. trivial.
      apply access_merge_assocmap. rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply st_greater_than_res.
      trivial.

      (* match_states *)
      assert (pc' = valueToPos (posToValue 32 pc')). symmetry. apply assumption_32bit.
      rewrite <- H1.
      constructor. apply rs0.
      rewrite merge_inj.
      apply regs_add_match.
      rewrite merge_inj.
      unfold merge_assocmap. rewrite AssocMapExt.merge_base.
      apply regs_lessdef_regs.
      assumption.
      apply valToValue_lessdef.

      inversion TF. simpl. apply H2.
      assumption.

      unfold state_st_wf. intros. inversion H2. subst.
      rewrite merge_inj.
      rewrite AssocMap.gso.
      rewrite merge_inj.
      apply AssocMap.gss.
      apply st_greater_than_res.
    - inversion MSTATE. inversion TC. subst.
      econstructor. constructor.
      inversion H12; subst_eq_hyp; discriminate.
      apply match_state. apply rs0.
      apply regs_add_match. apply MASSOC. apply valToValue_lessdef.
      inversion TF. rewrite H3.

End CORRECTNESS.
