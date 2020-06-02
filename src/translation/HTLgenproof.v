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

From compcert Require RTL Registers AST.
From compcert Require Import Globalenvs.
From coqup Require Import Coquplib HTLgenspec HTLgen Value AssocMap.
From coqup Require HTL Verilog.

Import AssocMapNotation.

Hint Resolve Smallstep.forward_simulation_plus : htlproof.
Hint Resolve AssocMap.gss : htlproof.
Hint Resolve AssocMap.gso : htlproof.

Hint Unfold find_assocmap AssocMapExt.get_default : htlproof.

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

Definition match_prog (p: RTL.program) (tp: HTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, HTLgen.transl_program p = Errors.OK tp -> match_prog p tp.
Proof.
  intros. apply Linking.match_transform_partial_program; auto.
Qed.

Lemma regs_lessdef_add_greater :
  forall f rs1 rs2 n v,
    Plt (RTL.max_reg_function f) n ->
    match_assocmaps f rs1 rs2 ->
    match_assocmaps f rs1 (AssocMap.set n v rs2).
Proof.
  inversion 2; subst.
  intros. constructor.
  intros. unfold find_assocmap. unfold AssocMapExt.get_default.
  rewrite AssocMap.gso. eauto.
  apply Pos.le_lt_trans with _ _ n in H2.
  unfold not. intros. subst. eapply Pos.lt_irrefl. eassumption. assumption.
Qed.
Hint Resolve regs_lessdef_add_greater : htlproof.

Lemma regs_lessdef_add_match :
  forall f rs am r v v',
    val_value_lessdef v v' ->
    match_assocmaps f rs am ->
    match_assocmaps f (Registers.Regmap.set r v rs) (AssocMap.set r v' am).
Proof.
  inversion 2; subst.
  constructor. intros.
  destruct (peq r0 r); subst.
  rewrite Registers.Regmap.gss.
  unfold find_assocmap. unfold AssocMapExt.get_default.
  rewrite AssocMap.gss. assumption.

  rewrite Registers.Regmap.gso; try assumption.
  unfold find_assocmap. unfold AssocMapExt.get_default.
  rewrite AssocMap.gso; eauto.
Qed.
Hint Resolve regs_lessdef_add_match : htlproof.

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
          Maps.PTree.get _ _ = Some _ -> tr_code _ _ _ _ _ _ _ _,
        H : Maps.PTree.get _ _ = Some _ |- _ =>
        apply TC in H; inversion H;
        match goal with
          TI : context[tr_instr] |- _ =>
          inversion TI
        end
      end
    end
end; subst.

Ltac unfold_func H :=
  match type of H with
  | ?f = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ _ = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ _ _ = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ _ _ _ = _ => unfold f in H; repeat (unfold_match H)
  end.

Section CORRECTNESS.

  Variable prog : RTL.program.
  Variable tprog : HTL.program.

  Hypothesis TRANSL : match_prog prog tprog.

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : HTL.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof
    (Genv.find_symbol_transf_partial TRANSL).

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: RTL.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: RTL.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof
    (Genv.senv_transf_partial TRANSL).
  Hint Resolve senv_preserved : htlproof.

  Lemma eval_correct :
    forall sp op rs args m v v' e assoc f,
      Op.eval_operation ge sp op
(List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some v ->
      tr_op op args e ->
      val_value_lessdef v v' ->
      Verilog.expr_runp f assoc e v'.
  Admitted.

  Lemma eval_cond_correct :
    forall cond (args : list Registers.reg) s1 c s' i rs args m b f assoc,
    translate_condition cond args s1 = OK c s' i ->
    Op.eval_condition
      cond
      (List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args)
      m = Some b ->
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

  Lemma greater_than_max_func :
    forall f st,
      Plt (RTL.max_reg_function f) st.
  Proof. Admitted.

  Theorem transl_step_correct:
    forall (S1 : RTL.state) t S2,
      RTL.step ge S1 t S2 ->
      forall (R1 : HTL.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus HTL.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; intros R1 MSTATE; try inv_state.
    - (* Inop *)
      unfold match_prog in TRANSL.
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
      unfold_merge. simpl. apply AssocMap.gss.

      (* prove match_state *)
      rewrite assumption_32bit.
      constructor; auto.
      unfold_merge. simpl. apply regs_lessdef_add_greater. apply greater_than_max_func.
      assumption.
      unfold state_st_wf. inversion 1. subst. unfold_merge. apply AssocMap.gss.
    - (* Iop *)
      destruct v eqn:?;
               try (
                 destruct op eqn:?; inversion H21; simpl in H0; repeat (unfold_match H0);
                 inversion H0; subst; simpl in *; try (unfold_func H4); try (unfold_func H5);
                 try (unfold_func H6);
                 try (unfold Op.eval_addressing32 in H6; repeat (unfold_match H6); inversion H6;
                      unfold_func H3);

                 inversion Heql; inversion MASSOC; subst;
                 assert (HPle : Ple r (RTL.max_reg_function f))
                   by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
                 apply H1 in HPle; inversion HPle;
                 rewrite H2 in *; discriminate
               ).

      + econstructor. split.
      apply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor; simpl; trivial.
      constructor; trivial.
      econstructor; simpl; eauto.
      eapply eval_correct; eauto. constructor.
      unfold_merge. simpl.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply st_greater_than_res.

      (* match_states *)
      assert (pc' = valueToPos (posToValue 32 pc')). auto using assumption_32bit.
      rewrite <- H1.
      constructor; auto.
      unfold_merge.
      apply regs_lessdef_add_match.
      constructor.
      apply regs_lessdef_add_greater.
      apply greater_than_max_func.
      assumption.

      unfold state_st_wf. intros. inversion H2. subst.
      unfold_merge.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply st_greater_than_res.

      + econstructor. split.
      apply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor; simpl; trivial.
      constructor; trivial.
      econstructor; simpl; eauto.
      eapply eval_correct; eauto.
      constructor. rewrite valueToInt_intToValue. trivial.
      unfold_merge. simpl.
      rewrite AssocMap.gso.
      apply AssocMap.gss.
      apply st_greater_than_res.

      (* match_states *)
      assert (pc' = valueToPos (posToValue 32 pc')). auto using assumption_32bit.
      rewrite <- H1.
      constructor. apply rs0.
      unfold_merge.
      apply regs_lessdef_add_match.
      constructor.
      symmetry. apply valueToInt_intToValue.
      apply regs_lessdef_add_greater.
      apply greater_than_max_func.
      assumption. assumption.

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
      apply regs_lessdef_add_greater. apply greater_than_max_func.
      assumption. assumption.

      unfold state_st_wf. intros. inversion H1.
      subst. unfold_merge.
      apply AssocMap.gss.
      rewrite assumption_32bit.
      apply match_state. apply rs0.
      unfold_merge.
      apply regs_lessdef_add_greater. apply greater_than_max_func. assumption.
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
Proof.
  eapply Smallstep.forward_simulation_plus.
  apply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  exact transl_step_correct.
Qed.

End CORRECTNESS.
