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

From coqup Require Import Coquplib HTLgenspec HTLgen Value AssocMap.
From coqup Require HTL Verilog.
From compcert Require RTL Registers Globalenvs AST.

Import AssocMapNotation.

Hint Resolve Smallstep.forward_simulation_plus : htlproof.
Hint Resolve AssocMap.gss : htlproof.
Hint Resolve AssocMap.gso : htlproof.

Inductive match_assocmaps : RTL.function -> RTL.regset -> assocmap -> Prop :=
  match_assocmap : forall f rs am,
    (forall r, Ple r (RTL.max_reg_function f) ->
               val_value_lessdef (Registers.Regmap.get r rs) am#r) ->
    match_assocmaps f rs am.
Hint Constructors match_assocmaps : htlproof.

Definition state_st_wf (m : HTL.module) (s : HTL.state) :=
  forall st assoc,
  s = HTL.State m st assoc ->
  assoc!(m.(HTL.mod_st)) = Some (posToValue 32 st).
Hint Unfold state_st_wf : htlproof.

Inductive match_states : RTL.state -> HTL.state -> Prop :=
| match_state : forall (rs : RTL.regset) assoc sf f sp rs mem m st
    (MASSOC : match_assocmaps f rs assoc)
    (TF : tr_module f m)
    (WF : state_st_wf m (HTL.State m st assoc)),
    match_states (RTL.State sf f sp st rs mem)
                 (HTL.State m st assoc)
| match_returnstate : forall v v' stack m,
    val_value_lessdef v v' ->
    match_states (RTL.Returnstate stack v m) (HTL.Returnstate v').
Hint Constructors match_states : htlproof.

Inductive match_program : RTL.program -> HTL.module -> Prop :=
  match_program_intro :
    forall ge p b m f,
    ge = Globalenvs.Genv.globalenv p ->
    Globalenvs.Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
    tr_module f m ->
    match_program p m.
Hint Constructors match_program : htlproof.

Lemma regs_lessdef_regs :
  forall f rs1 rs2 n v,
    Plt (RTL.max_reg_function f) n ->
    match_assocmaps f rs1 rs2 ->
    match_assocmaps f rs1 (AssocMap.add n v rs2).
Proof.
  inversion 2; subst.
  intros. constructor.
  intros. unfold find_assocmap. unfold AssocMapExt.find_default.
  rewrite AssocMap.gso. eauto.
  apply Pos.le_lt_trans with _ _ n in H2.
  unfold not. intros. subst. eapply Pos.lt_irrefl. eassumption. assumption.
Qed.

Lemma regs_add_match :
  forall f rs am r v v',
    val_value_lessdef v v' ->
    match_assocmaps f rs am ->
    match_assocmaps f (Registers.Regmap.set r v rs) (AssocMap.add r v' am).
Proof.
  inversion 2; subst.
  constructor. intros.
  destruct (peq r0 r); subst.
  rewrite Registers.Regmap.gss.
  unfold find_assocmap. unfold AssocMapExt.find_default.
  rewrite AssocMap.gss. assumption.

  rewrite Registers.Regmap.gso; try assumption.
  unfold find_assocmap. unfold AssocMapExt.find_default.
  rewrite AssocMap.gso; eauto.
Qed.

Lemma valToValue_lessdef :
  forall v v',
    valToValue v = Some v' <->
    val_value_lessdef v v'.
Proof.
  split; intros.
  destruct v; try discriminate; constructor.
  unfold valToValue in H. inversion H.
  Admitted.

(* Need to eventually move posToValue 32 to posToValueAuto, as that has this proof. *)
Lemma assumption_32bit :
  forall v,
    valueToPos (posToValue 32 v) = v.
Admitted.

Lemma assumption_32bit_bool :
  forall b,
    valueToBool (boolToValue 32 b) = b.
Admitted.

Lemma st_greater_than_res :
  forall m res : positive,
    m <> res.
Admitted.

Lemma finish_not_return :
  forall r f : positive,
    r <> f.
Admitted.

Lemma finish_not_res :
  forall f r : positive,
    f <> r.
Admitted.

Ltac inv_state :=
  match goal with
    MSTATE : match_states _ _ |- _ =>
    inversion MSTATE;
    match goal with
      TF : tr_module _ _ |- _ =>
      inversion TF;
      match goal with
        TC : forall _ _,
          Maps.PTree.get _ _ = Some _ -> tr_code _ _ _ _ _ _ _,
        H : Maps.PTree.get _ _ = Some _ |- _ =>
        apply TC in H; inversion H;
        match goal with
          TI : tr_instr _ _ _ _ _ _ |- _ =>
          inversion TI
        end
      end
    end
  end; subst.

Section CORRECTNESS.

  Variable prog : RTL.program.
  Variable tprog : HTL.module.

  Hypothesis TRANSL : match_program prog tprog.

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : HTL.genv := HTL.genv_empty.

  Lemma eval_correct :
    forall sp op rs args m v v' e assoc f,
      Op.eval_operation ge sp op
(List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some v ->
      tr_op op args e ->
      valToValue v = Some v' ->
      Verilog.expr_runp f assoc e v'.
  Admitted.

  Lemma eval_cond_correct :
    forall cond (args : list Registers.reg) s1 c s' i rs args m b f assoc,
    translate_condition cond args s1 = OK c s' i ->
    Op.eval_condition cond (List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some b ->
    Verilog.expr_runp f assoc c (boolToValue 32 b).
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
                      match_states
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
        exists R2, Smallstep.plus HTL.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; intros R1 MSTATE; try inv_state.
    - (* Inop *)
      econstructor.
      split.
      apply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      (* processing of state *)
      econstructor.
      simpl. trivial.
      econstructor. trivial.
      econstructor.

      (* prove stval *)
      unfold merge_assocmap. apply AssocMapExt.merge_add. simpl. apply AssocMap.gss.

      (* prove match_state *)
      rewrite assumption_32bit.
      constructor; auto.
      unfold merge_assocmap. rewrite AssocMapExt.merge_add. simpl. apply AssocMap.gss.
      apply regs_lessdef_regs. assumption.
      unfold state_st_wf. inversion 1. subst. apply AssocMap.gss.
    - (* Iop *)
      econstructor.
      split.
      apply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor; simpl; trivial.
      constructor; trivial.
      econstructor; simpl; eauto.
      eapply eval_correct; eauto.
      unfold_merge. simpl.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply st_greater_than_res.
      trivial.

      (* match_states *)
      assert (pc' = valueToPos (posToValue 32 pc')). symmetry. apply assumption_32bit.
      rewrite <- H1.
      constructor. apply rs0.
      unfold_merge.
      apply regs_add_match.
      apply regs_lessdef_regs.
      assumption.
      apply valToValue_lessdef.
      assumption.

      unfold state_st_wf. intros. inversion H2. subst.
      unfold_merge.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply st_greater_than_res.
    - econstructor. split. apply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      eapply Verilog.stmnt_runp_Vnonblock with
          (rhsval := if b then posToValue 32 ifso else posToValue 32 ifnot).
      simpl. trivial.
      destruct b.
      eapply Verilog.erun_Vternary_true.
      eapply eval_cond_correct; eauto.
      constructor.
      apply assumption_32bit_bool.
      eapply Verilog.erun_Vternary_false.
      eapply eval_cond_correct; eauto.
      constructor.
      apply assumption_32bit_bool.
      trivial.
      constructor.
      trivial.
      unfold_merge.
      apply AssocMap.gss.
      trivial.

      destruct b.
      rewrite assumption_32bit.
      apply match_state. apply rs0.
      unfold_merge.
      apply regs_lessdef_regs. assumption.
      assumption.

      unfold state_st_wf. intros. inversion H1.
      subst. unfold_merge.
      apply AssocMap.gss.
      rewrite assumption_32bit.
      apply match_state. apply rs0.
      unfold_merge.
      apply regs_lessdef_regs. assumption.
      assumption.

      unfold state_st_wf. intros. inversion H1.
      subst. unfold_merge.
      apply AssocMap.gss.

    - (* Return *)
      econstructor. split.
      eapply Smallstep.plus_two.
      
      eapply HTL.step_module; eauto.
      constructor.
      econstructor; simpl; trivial.
      econstructor; simpl; trivial.
      constructor.
      econstructor; simpl; trivial.
      constructor.
      unfold_merge.
      trivial.
      rewrite AssocMap.gso.
      rewrite AssocMap.gso.
      unfold state_st_wf in WF. apply WF. trivial.
      apply st_greater_than_res. apply st_greater_than_res. trivial.

      apply HTL.step_finish.
      unfold_merge; simpl.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply finish_not_return.
      apply AssocMap.gss.
      rewrite Events.E0_left. trivial.

      constructor. constructor.
    - destruct (assoc!r) eqn:?.
      inversion H11. subst.
      econstructor. split.
      eapply Smallstep.plus_two.
      eapply HTL.step_module; eauto.
      constructor.
      econstructor; simpl; trivial.
      econstructor; simpl; trivial.
      constructor.
      econstructor; simpl; trivial.
      apply Verilog.erun_Vvar.
      rewrite AssocMap.gso.
      apply Heqo. apply not_eq_sym. apply finish_not_res.
      unfold_merge.
      trivial.
      rewrite AssocMap.gso.
      rewrite AssocMap.gso.
      unfold state_st_wf in WF. apply WF. trivial.
      apply st_greater_than_res. apply st_greater_than_res. trivial.

      apply HTL.step_finish.
      unfold_merge.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply finish_not_return.
      apply AssocMap.gss.
      rewrite Events.E0_left. trivial.

      constructor. simpl.
      Admitted.
  Hint Resolve transl_step_correct : htlproof.

  Lemma senv_preserved :
    forall id : AST.ident,
      Globalenvs.Senv.public_symbol (Smallstep.symbolenv (HTL.semantics tprog)) id =
      Globalenvs.Senv.public_symbol (Smallstep.symbolenv (RTL.semantics prog)) id.
  Proof. Admitted.
  Hint Resolve senv_preserved : htlproof.

  Lemma transl_initial_states :
    forall s1 : Smallstep.state (RTL.semantics prog),
      Smallstep.initial_state (RTL.semantics prog) s1 ->
      exists s2 : Smallstep.state (HTL.semantics tprog),
        Smallstep.initial_state (HTL.semantics tprog) s2 /\ match_states s1 s2.
  Proof. Admitted.
  Hint Resolve transl_initial_states : htlproof.

  Lemma transl_final_states :
    forall (s1 : Smallstep.state (RTL.semantics prog)) (s2 : Smallstep.state (HTL.semantics tprog))
           (r : Integers.Int.int),
      match_states s1 s2 ->
      Smallstep.final_state (RTL.semantics prog) s1 r -> Smallstep.final_state (HTL.semantics tprog) s2 r.
  Proof. Admitted.
  Hint Resolve transl_final_states : htlproof.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog) (HTL.semantics tprog).
  Proof. eauto with htlproof. Qed.

End CORRECTNESS.
