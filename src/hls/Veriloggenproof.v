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

From compcert Require Import Smallstep Linking Integers Globalenvs.
From compcert Require Errors.
From vericert Require HTL.
From vericert Require Import Vericertlib Veriloggen Verilog ValueInt AssocMap.
Require Import Lia.

Local Open Scope assocmap.

Definition match_prog (prog : HTL.program) (tprog : Verilog.program) :=
  match_program (fun cu f tf => Errors.OK tf = transl_fundef prog f) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transl_program prog = Errors.OK tprog -> match_prog prog tprog.
Proof.
  intros. unfold transl_program in *. eapply match_transform_partial_program_contextual; eauto.
Qed.

Instance TransfVerilogLink : TransfLink Veriloggenproof.match_prog.
Admitted.

(* Inductive match_stacks : list HTL.stackframe -> list stackframe -> Prop := *)
(* | match_stack : *)
(*     forall res m pc reg_assoc arr_assoc hstk vstk, *)
(*       match_stacks hstk vstk -> *)
(*       match_stacks (HTL.Stackframe res m pc reg_assoc arr_assoc :: hstk) *)
(*                    (Stackframe res (transl_module m) pc *)
(*                                        reg_assoc arr_assoc :: vstk) *)
(* | match_stack_nil : match_stacks nil nil. *)

(* Inductive match_states : HTL.state -> state -> Prop := *)
(* | match_state : *)
(*     forall m st reg_assoc arr_assoc hstk vstk, *)
(*       match_stacks hstk vstk -> *)
(*       match_states (HTL.State hstk m st reg_assoc arr_assoc) *)
(*                    (State vstk (transl_module m) st reg_assoc arr_assoc) *)
(* | match_returnstate : *)
(*     forall v hstk vstk, *)
(*       match_stacks hstk vstk -> *)
(*       match_states (HTL.Returnstate hstk v) (Returnstate vstk v) *)
(* | match_initial_call : *)
(*     forall m, *)
(*       match_states (HTL.Callstate nil m nil) (Callstate nil (transl_module m) nil). *)

(* Lemma Vlit_inj : *)
(*   forall a b, Vlit a = Vlit b -> a = b. *)
(* Proof. inversion 1. trivial. Qed. *)

(* Lemma posToValue_inj : *)
(*   forall a b, *)
(*     0 <= Z.pos a <= Int.max_unsigned -> *)
(*     0 <= Z.pos b <= Int.max_unsigned -> *)
(*     posToValue a = posToValue b -> *)
(*     a = b. *)
(* Proof. *)
(*   intros. rewrite <- Pos2Z.id at 1. rewrite <- Pos2Z.id. *)
(*   rewrite <- Int.unsigned_repr at 1; try assumption. *)
(*   symmetry. *)
(*   rewrite <- Int.unsigned_repr at 1; try assumption. *)
(*   unfold posToValue in *. rewrite H1; auto. *)
(* Qed. *)

(* Lemma valueToPos_inj : *)
(*   forall a b, *)
(*     0 < Int.unsigned a -> *)
(*     0 < Int.unsigned b -> *)
(*     valueToPos a = valueToPos b -> *)
(*     a = b. *)
(* Proof. *)
(*   intros. unfold valueToPos in *. *)
(*   rewrite <- Int.repr_unsigned at 1. *)
(*   rewrite <- Int.repr_unsigned. *)
(*   apply Pos2Z.inj_iff in H1. *)
(*   rewrite Z2Pos.id in H1; auto. *)
(*   rewrite Z2Pos.id in H1; auto. *)
(*   rewrite H1. auto. *)
(* Qed. *)

(* Lemma unsigned_posToValue_le : *)
(*   forall p, *)
(*     Z.pos p <= Int.max_unsigned -> *)
(*     0 < Int.unsigned (posToValue p). *)
(* Proof. *)
(*   intros. unfold posToValue. rewrite Int.unsigned_repr; lia. *)
(* Qed. *)

(* Lemma transl_ctrl_fun_fst : *)
(*   forall p1 p2 a b, *)
(*     0 <= Z.pos p1 <= Int.max_unsigned -> *)
(*     0 <= Z.pos p2 <= Int.max_unsigned -> *)
(*     transl_ctrl_fun (p1, a) = transl_ctrl_fun (p2, b) -> *)
(*     (p1, a) = (p2, b). *)
(* Proof. *)
(*   intros. unfold transl_ctrl_fun in H1. apply pair_equal_spec in H1. *)
(*   destruct H1. rewrite H2. apply Vlit_inj in H1. *)
(*   apply posToValue_inj in H1; try assumption. *)
(*   rewrite H1; auto. *)
(* Qed. *)

(* Lemma transl_data_fun_fst : *)
(*   forall p1 p2 a b, *)
(*     0 <= Z.pos p1 <= Int.max_unsigned -> *)
(*     0 <= Z.pos p2 <= Int.max_unsigned -> *)
(*     transl_datapath_fun (p1, a) = transl_datapath_fun (p2, b) -> *)
(*     p1 = p2. *)
(* Proof. *)
(*   intros. *)
(*   unfold transl_datapath_fun in H1. apply pair_equal_spec in H1. destruct H1. *)
(*   apply Vlit_inj in H1. apply posToValue_inj in H1; assumption. *)
(* Qed. *)

(* Lemma Zle_relax : *)
(*   forall p q r, *)
(*   p < q <= r -> *)
(*   p <= q <= r. *)
(* Proof. lia. Qed. *)
(* Hint Resolve Zle_relax : verilogproof. *)

(* Lemma transl_in : *)
(*   forall l p, *)
(*   0 <= Z.pos p <= Int.max_unsigned -> *)
(*   (forall p0, In p0 (List.map fst l) -> 0 < Z.pos p0 <= Int.max_unsigned) -> *)
(*   In (Vlit (posToValue p)) (map fst (map transl_ctrl_fun l)) -> *)
(*   In p (map fst l). *)
(* Proof. *)
(*   induction l. *)
(*   - simplify. auto. *)
(*   - intros. destruct a. simplify. destruct (peq p0 p); auto. *)
(*     right. inv H1. apply Vlit_inj in H. apply posToValue_inj in H; auto. contradiction. *)
(*     auto with verilogproof. *)
(*     apply IHl; auto. *)
(* Qed. *)

(* Lemma transl_notin : *)
(*   forall l p, *)
(*     0 <= Z.pos p <= Int.max_unsigned -> *)
(*     (forall p0, In p0 (List.map fst l) -> 0 < Z.pos p0 <= Int.max_unsigned) -> *)
(*     ~ In p (List.map fst l) -> ~ In (Vlit (posToValue p)) (List.map fst (transl_ctrl l)). *)
(* Proof. *)
(*   induction l; auto. intros. destruct a. unfold not in *. intros. *)
(*   simplify. *)
(*   destruct (peq p0 p). apply H1. auto. apply H1. *)
(*   unfold transl_ctrl in *. inv H2. apply Vlit_inj in H. apply posToValue_inj in H. *)
(*   contradiction. *)
(*   auto with verilogproof. auto. *)
(*   right. apply transl_in; auto. *)
(* Qed. *)

(* Lemma transl_norepet : *)
(*   forall l, *)
(*     (forall p0, In p0 (List.map fst l) -> 0 < Z.pos p0 <= Int.max_unsigned) -> *)
(*     list_norepet (List.map fst l) -> list_norepet (List.map fst (transl_ctrl l)). *)
(* Proof. *)
(*   induction l. *)
(*   - intros. simpl. apply list_norepet_nil. *)
(*   - destruct a. intros. simpl. apply list_norepet_cons. *)
(*     inv H0. apply transl_notin. apply Zle_relax. apply H. simplify; auto. *)
(*     intros. apply H. destruct (peq p0 p); subst; simplify; auto. *)
(*     assumption. apply IHl. intros. apply H. destruct (peq p0 p); subst; simplify; auto. *)
(*     simplify. inv H0. assumption. *)
(* Qed. *)

(* Lemma transl_ctrl_correct : *)
(*   forall l v ev f asr asa asrn asan asr' asa' asrn' asan', *)
(*     (forall p0, In p0 (List.map fst l) -> 0 < Z.pos p0 <= Int.max_unsigned) -> *)
(*     list_norepet (List.map fst l) -> *)
(*     asr!ev = Some v -> *)
(*     (forall p s, *)
(*         In (p, s) l -> *)
(*         v = posToValue p -> *)
(*         stmnt_runp f *)
(*                    {| assoc_blocking := asr; assoc_nonblocking := asrn |} *)
(*                    {| assoc_blocking := asa; assoc_nonblocking := asan |} *)
(*                    s *)
(*                    {| assoc_blocking := asr'; assoc_nonblocking := asrn' |} *)
(*                    {| assoc_blocking := asa'; assoc_nonblocking := asan' |} -> *)
(*         stmnt_runp f *)
(*                    {| assoc_blocking := asr; assoc_nonblocking := asrn |} *)
(*                    {| assoc_blocking := asa; assoc_nonblocking := asan |} *)
(*                    (Vcase (Vvar ev) (transl_ctrl l) (Some Vskip)) *)
(*                    {| assoc_blocking := asr'; assoc_nonblocking := asrn' |} *)
(*                    {| assoc_blocking := asa'; assoc_nonblocking := asan' |}). *)
(* Proof. *)
(*   induction l as [| a l IHl]. *)
(*   - contradiction. *)
(*   - intros v ev f asr asa asrn asan asr' asa' asrn' asan' BOUND NOREP ASSOC p s IN EQ SRUN. *)
(*     destruct a as [p' s']. simplify. *)
(*     destruct (peq p p'); subst. eapply stmnt_runp_Vcase_match. *)
(*     constructor. simplify. unfold AssocMap.find_assocmap, AssocMapExt.get_default. *)
(*     rewrite ASSOC. trivial. constructor. auto. *)
(*     inversion IN as [INV | INV]. inversion INV as [INV2]; subst. assumption. *)
(*     inv NOREP. eapply in_map with (f := fst) in INV. contradiction. *)

(*     eapply stmnt_runp_Vcase_nomatch. constructor. simplify. *)
(*     unfold AssocMap.find_assocmap, AssocMapExt.get_default. rewrite ASSOC. *)
(*     trivial. constructor. unfold not. intros. apply n. apply posToValue_inj. *)
(*     apply Zle_relax. apply BOUND. right. inv IN. inv H0; contradiction. *)
(*     eapply in_map with (f := fst) in H0. auto. *)
(*     apply Zle_relax. apply BOUND; auto. auto. *)

(*     eapply IHl. auto. inv NOREP. auto. eassumption. inv IN. inv H. contradiction. apply H. *)
(*     trivial. assumption. *)
(* Qed. *)
(* Hint Resolve transl_ctrl_correct : verilogproof. *)

(* (* FIXME Probably wrong we probably need some statemnt about datapath_statement_runp *) *)
(* Lemma transl_datapath_correct : *)
(*   forall l v ev f asr asa asrn asan asr' asa' asrn' asan', *)
(*     (forall p0, In p0 (List.map fst l) -> 0 < Z.pos p0 <= Int.max_unsigned) -> *)
(*     list_norepet (List.map fst l) -> *)
(*     asr!ev = Some v -> *)
(*     (forall p s, *)
(*         In (p, s) l -> *)
(*         v = posToValue p -> *)
(*         stmnt_runp f *)
(*                    {| assoc_blocking := asr; assoc_nonblocking := asrn |} *)
(*                    {| assoc_blocking := asa; assoc_nonblocking := asan |} *)
(*                    s *)
(*                    {| assoc_blocking := asr'; assoc_nonblocking := asrn' |} *)
(*                    {| assoc_blocking := asa'; assoc_nonblocking := asan' |} -> *)
(*         stmnt_runp f *)
(*                    {| assoc_blocking := asr; assoc_nonblocking := asrn |} *)
(*                    {| assoc_blocking := asa; assoc_nonblocking := asan |} *)
(*                    (Vcase (Vvar ev) (transl_ctrl l) (Some Vskip)) *)
(*                    {| assoc_blocking := asr'; assoc_nonblocking := asrn' |} *)
(*                    {| assoc_blocking := asa'; assoc_nonblocking := asan' |}). *)
(* Proof. Admitted. *)

(* Lemma pc_wf : *)
(*   forall A m p v, *)
(*   (forall p0, In p0 (List.map fst (@AssocMap.elements A m)) -> 0 < Z.pos p0 <= Int.max_unsigned) -> *)
(*   m!p = Some v -> *)
(*   0 <= Z.pos p <= Int.max_unsigned. *)
(* Proof. *)
(*   intros A m p v LT S. apply Zle_relax. apply LT. *)
(*   apply AssocMap.elements_correct in S. remember (p, v) as x. *)
(*   exploit in_map. apply S. instantiate (1 := fst). subst. simplify. auto. *)
(* Qed. *)

(* Lemma mis_stepp_decl : *)
(*   forall l asr asa f, *)
(*     mis_stepp f asr asa (map Vdeclaration l) asr asa. *)
(* Proof. *)
(*   induction l. *)
(*   - intros. constructor. *)
(*   - intros. simplify. econstructor. constructor. auto. *)
(* Qed. *)
(* Hint Resolve mis_stepp_decl : verilogproof. *)

(* Lemma mis_stepp_negedge_decl : *)
(*   forall l asr asa f, *)
(*     mis_stepp_negedge f asr asa (map Vdeclaration l) asr asa. *)
(* Proof. *)
(*   induction l. *)
(*   - intros. constructor. *)
(*   - intros. simplify. econstructor. constructor. auto. *)
(* Qed. *)
(* Hint Resolve mis_stepp_negedge_decl : verilogproof. *)

(* Lemma mod_entrypoint_equiv m : mod_entrypoint (transl_module m) = HTL.mod_entrypoint m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_st_equiv m : mod_st (transl_module m) = HTL.mod_st m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_stk_equiv m : mod_stk (transl_module m) = HTL.mod_stk m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_stk_len_equiv m : mod_stk_len (transl_module m) = HTL.mod_stk_len m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_finish_equiv m : mod_finish (transl_module m) = HTL.mod_finish m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_reset_equiv m : mod_reset (transl_module m) = HTL.mod_reset m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_clk_equiv m : mod_clk (transl_module m) = HTL.mod_clk m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_return_equiv m : mod_return (transl_module m) = HTL.mod_return m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma mod_params_equiv m : mod_args (transl_module m) = HTL.mod_params m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Lemma empty_stack_equiv m : empty_stack (transl_module m) = HTL.empty_stack m. *)
(* Proof. unfold transl_module; intros; destruct (HTL.mod_ram m) eqn:?; crush. Qed. *)

(* Ltac rewrite_eq := rewrite mod_return_equiv *)
(*                    || rewrite mod_clk_equiv *)
(*                    || rewrite mod_reset_equiv *)
(*                    || rewrite mod_finish_equiv *)
(*                    || rewrite mod_stk_len_equiv *)
(*                    || rewrite mod_stk_equiv *)
(*                    || rewrite mod_st_equiv *)
(*                    || rewrite mod_entrypoint_equiv *)
(*                    || rewrite mod_params_equiv *)
(*                    || rewrite empty_stack_equiv. *)

(* Lemma find_assocmap_get r i v : r ! i = Some v -> r # i = v. *)
(* Proof. *)
(*   intros. unfold find_assocmap, AssocMapExt.get_default. rewrite H. auto. *)
(* Qed. *)

(* Lemma ram_exec_match : *)
(*   forall f asr asa asr' asa' r clk, *)
(*     HTL.exec_ram asr asa (Some r) asr' asa' -> *)
(*     mi_stepp_negedge f asr asa (inst_ram clk r) asr' asa'. *)
(* Proof. *)
(*   inversion 1; subst; simplify. *)
(*   { unfold inst_ram. econstructor. *)
(*     eapply stmnt_runp_Vcond_false. *)
(*     econstructor. econstructor. econstructor. auto. *)
(*     econstructor. auto. *)
(*     simplify. *)
(*     unfold boolToValue, natToValue, valueToBool. *)
(*     rewrite Int.eq_sym. rewrite H3. simplify. *)
(*     auto. constructor. } *)
(*   { unfold inst_ram. econstructor. econstructor. econstructor. *)
(*     econstructor. econstructor. auto. *)
(*     econstructor. auto. *)
(*     simplify. *)
(*     unfold boolToValue, natToValue, valueToBool. *)
(*     pose proof H4 as X. apply find_assocmap_get in X. *)
(*     rewrite X. rewrite Int.eq_sym. rewrite H1. auto. *)
(*     econstructor. econstructor. econstructor. econstructor. *)
(*     pose proof H5 as X. apply find_assocmap_get in X. *)
(*     rewrite X. *)
(*     unfold valueToBool. unfold ZToValue in *. *)
(*     unfold Int.eq in H2. *)
(*     unfold uvalueToZ. *)
(*     assert (Int.unsigned wr_en =? 0 = false). *)
(*     apply Z.eqb_neq. rewrite Int.unsigned_repr in H2 by (simplify; lia). *)
(*     destruct (zeq (Int.unsigned wr_en) 0); crush. *)
(*     rewrite H0. auto. *)
(*     apply stmnt_runp_Vnonblock_arr. econstructor. econstructor. auto. *)
(*     econstructor. econstructor. *)
(*     apply find_assocmap_get in H9. rewrite H9. *)
(*     apply find_assocmap_get in H6. rewrite H6. *)
(*     repeat econstructor. apply find_assocmap_get; auto. *)
(*   } *)
(*   { econstructor. econstructor. econstructor. econstructor. auto. *)
(*     econstructor. auto. *)
(*     econstructor. *)
(*     unfold boolToValue, natToValue, valueToBool. *)
(*     apply find_assocmap_get in H3. rewrite H3. *)
(*     rewrite Int.eq_sym. rewrite H1. auto. *)
(*     econstructor. *)
(*     eapply stmnt_runp_Vcond_false. econstructor. auto. *)
(*     simplify. apply find_assocmap_get in H4. rewrite H4. *)
(*     auto. *)
(*     repeat (econstructor; auto). apply find_assocmap_get in H5. *)
(*     rewrite H5. eassumption. *)
(*     repeat econstructor. simplify. apply find_assocmap_get; auto. *)
(*   } *)
(* Qed. *)


Section CORRECTNESS.

  Variable prog: HTL.program.
  Variable tprog: program.

  Hypothesis TRANSL : match_prog prog tprog.

  Let ge : HTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. intros. eapply (Genv.find_symbol_match TRANSL). Qed.
  #[local] Hint Resolve symbols_preserved : verilogproof.

(*   Lemma function_ptr_translated: *)
(*     forall (b: Values.block) (f: HTL.fundef), *)
(*       Genv.find_funct_ptr ge b = Some f -> *)
(*       exists tf, *)
(*         Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = tf. *)
(*   Proof. *)
(*     intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto. *)
(*     intros (cu & tf & P & Q & R); exists tf; auto. *)
(*   Qed. *)
(*   Hint Resolve function_ptr_translated : verilogproof. *)

(*   Lemma functions_translated: *)
(*     forall (v: Values.val) (f: HTL.fundef), *)
(*       Genv.find_funct ge v = Some f -> *)
(*       exists tf, *)
(*         Genv.find_funct tge v = Some tf /\ transl_fundef f = tf. *)
(*   Proof. *)
(*     intros. exploit (Genv.find_funct_match TRANSL); eauto. *)
(*     intros (cu & tf & P & Q & R); exists tf; auto. *)
(*   Qed. *)
(*   Hint Resolve functions_translated : verilogproof. *)

(*   Lemma senv_preserved: *)
(*     Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge). *)
(*   Proof. *)
(*     intros. eapply (Genv.senv_match TRANSL). *)
(*   Qed. *)
(*   Hint Resolve senv_preserved : verilogproof. *)

(*   Theorem transl_step_correct : *)
(*     forall (S1 : HTL.state) t S2, *)
(*       HTL.step ge S1 t S2 -> *)
(*       forall (R1 : state), *)
(*         match_states S1 R1 -> *)
(*         exists R2, Smallstep.plus step tge R1 t R2 /\ match_states S2 R2. *)
(*   Proof. *)
(*     induction 1; intros R1 MSTATE; inv MSTATE. *)
(*     - econstructor; split. apply Smallstep.plus_one. econstructor. *)
(*       assumption. assumption. eassumption. apply valueToPos_posToValue. *)
(*       split. lia. *)
(*       eapply pc_wf. intros. pose proof (HTL.mod_wf m) as HP. destruct HP as [HP _]. *)
(*       split. lia. apply HP. eassumption. eassumption. *)
(*       econstructor. econstructor. eapply stmnt_runp_Vcond_false. econstructor. econstructor. *)
(*       simpl. unfold find_assocmap. unfold AssocMapExt.get_default. *)
(*       rewrite H. trivial. *)

(*       econstructor. simpl. auto. auto. *)

(*       eapply transl_ctrl_correct. *)
(*       intros. split. lia. pose proof (HTL.mod_wf m) as HP. destruct HP as [HP _]. auto. *)
(*       apply Maps.PTree.elements_keys_norepet. eassumption. *)
(*       2: { apply valueToPos_inj. apply unsigned_posToValue_le. *)
(*            eapply pc_wf. intros. pose proof (HTL.mod_wf m) as HP. destruct HP as [HP _]. *)
(*            split. lia. apply HP. eassumption. eassumption. *)
(*            apply unsigned_posToValue_le. eapply pc_wf. intros. pose proof (HTL.mod_wf m) as HP. *)
(*            destruct HP as [HP _]. *)
(*            split. lia. apply HP. eassumption. eassumption. trivial. *)
(*       } *)
(*       apply Maps.PTree.elements_correct. eassumption. eassumption. *)

(*       econstructor. econstructor. *)

(*       { admit. *)
(*       (* *) *)
(* (*       eapply transl_list_correct. *) *)
(* (*       intros. split. lia. pose proof (HTL.mod_wf m) as HP. destruct HP as [_ HP]. auto. *) *)
(* (*       apply Maps.PTree.elements_keys_norepet. eassumption. *) *)
(* (*       2: { apply valueToPos_inj. apply unsigned_posToValue_le. *) *)
(* (*            eapply pc_wf. intros. pose proof (HTL.mod_wf m) as HP. destruct HP as [HP _]. *) *)
(* (*            split. lia. apply HP. eassumption. eassumption. *) *)
(* (*            apply unsigned_posToValue_le. eapply pc_wf. intros. pose proof (HTL.mod_wf m) as HP. *) *)
(* (*            destruct HP as [HP _]. *) *)
(* (*            split. lia. apply HP. eassumption. eassumption. trivial. *) *)
(* (*       } *) *)
(* (*       apply Maps.PTree.elements_correct. eassumption. eassumption. *) *)
(* (*       *) *)
(*       } *)

(*       apply mis_stepp_decl. trivial. trivial. simpl. eassumption. auto. *)
(*       rewrite valueToPos_posToValue. constructor; assumption. lia. *)
(*     - econstructor; split. apply Smallstep.plus_one. apply step_finish. assumption. eassumption. *)
(*       constructor; assumption. *)
(*     - econstructor; split. apply Smallstep.plus_one. constructor. *)

(*       constructor. constructor. *)
(*     - inv H3. econstructor; split. apply Smallstep.plus_one. constructor. trivial. *)

(*       apply match_state. assumption. *)
(*   Admitted. *)
(*   Hint Resolve transl_step_correct : verilogproof. *)

(*   Lemma transl_initial_states : *)
(*     forall s1 : Smallstep.state (HTL.semantics prog), *)
(*       Smallstep.initial_state (HTL.semantics prog) s1 -> *)
(*       exists s2 : Smallstep.state (Verilog.semantics tprog), *)
(*         Smallstep.initial_state (Verilog.semantics tprog) s2 /\ match_states s1 s2. *)
(*   Proof. *)
(*     induction 1. *)
(*     econstructor; split. econstructor. *)
(*     apply (Genv.init_mem_transf TRANSL); eauto. *)
(*     rewrite symbols_preserved. *)
(*     replace (AST.prog_main tprog) with (AST.prog_main prog); eauto. *)
(*     symmetry; eapply Linking.match_program_main; eauto. *)
(*     exploit function_ptr_translated; eauto. intros [tf [A B]]. *)
(*     inv B. eauto. *)
(*     constructor. *)
(*   Qed. *)
(*   Hint Resolve transl_initial_states : verilogproof. *)

(*   Lemma transl_final_states : *)
(*     forall (s1 : Smallstep.state (HTL.semantics prog)) *)
(*            (s2 : Smallstep.state (Verilog.semantics tprog)) *)
(*            (r : Integers.Int.int), *)
(*       match_states s1 s2 -> *)
(*       Smallstep.final_state (HTL.semantics prog) s1 r -> *)
(*       Smallstep.final_state (Verilog.semantics tprog) s2 r. *)
(*   Proof. *)
(*     intros. inv H0. inv H. inv H3. constructor. reflexivity. *)
(*   Qed. *)
(*   Hint Resolve transl_final_states : verilogproof. *)

  Theorem transf_program_correct:
    forward_simulation (HTL.semantics prog) (Verilog.semantics tprog).
  Proof.
    (* eapply Smallstep.forward_simulation_plus; eauto with verilogproof. *)
    (* apply senv_preserved. *)
    admit.
  Admitted.

End CORRECTNESS.
