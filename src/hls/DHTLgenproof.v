(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.micromega.Lia.

Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require compcert.backend.Registers.
Require Import compcert.common.Linking.
Require Import compcert.common.Memory.
Require compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import vericert.common.IntegerExtra.
Require Import vericert.common.Vericertlib.
Require Import vericert.common.ZExtra.
Require Import vericert.hls.Array.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.DHTL.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSubPar.
Require Import vericert.hls.DHTLgen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require vericert.hls.Verilog.
Require Import vericert.common.Errormonad.
Import ErrorMonad.
Import ErrorMonadExtra.

Require Import Lia.

Local Open Scope assocmap.

Local Opaque Int.max_unsigned.

#[local] Hint Resolve AssocMap.gss : htlproof.
#[local] Hint Resolve AssocMap.gso : htlproof.

#[local] Hint Unfold find_assocmap AssocMapExt.get_default : htlproof.

Definition get_mem n r := 
  Option.default (NToValue 0) (Option.join (array_get_error n r)).

Inductive match_assocmaps : positive -> positive -> Gible.regset -> Gible.predset -> assocmap -> Prop :=
  match_assocmap : forall rs pr am max_reg max_pred,
    (forall r, Ple r max_reg ->
               val_value_lessdef (Registers.Regmap.get r rs) (find_assocmap 32 (reg_enc r) am)) ->
    (forall r, Ple r max_pred ->
               find_assocmap 1 (pred_enc r) am = boolToValue (PMap.get r pr)) ->
    match_assocmaps max_reg max_pred rs pr am.
#[local] Hint Constructors match_assocmaps : htlproof.

Inductive match_arrs (stack_size: Z) (stk: positive) (stk_len: nat) (sp : Values.val) (mem : mem) :
  Verilog.assocmap_arr -> Prop :=
| match_arr : forall asa stack,
    asa ! stk = Some stack /\
    stack.(arr_length) = Z.to_nat (stack_size / 4) /\
    stack.(arr_length) = stk_len /\
    (forall ptr,
        0 <= ptr < Z.of_nat stack.(arr_length) ->
        opt_val_value_lessdef (Mem.loadv AST.Mint32 mem
                                         (Values.Val.offset_ptr sp (Ptrofs.repr (4 * ptr))))
                              (get_mem (Z.to_nat ptr) stack)) ->
    match_arrs stack_size stk stk_len sp mem asa.

Definition stack_based (v : Values.val) (sp : Values.block) : Prop :=
   match v with
   | Values.Vptr sp' off => sp' = sp
   | _ => True
   end.

Definition reg_stack_based_pointers (sp : Values.block) (rs : Registers.Regmap.t Values.val) : Prop :=
  forall r, stack_based (Registers.Regmap.get r rs) sp.

Definition arr_stack_based_pointers (spb : Values.block) (m : mem) (stack_length : Z)
  (sp : Values.val) : Prop :=
  forall ptr,
    0 <= ptr < (stack_length / 4) ->
    stack_based (Option.default
                   Values.Vundef
                   (Mem.loadv AST.Mint32 m
                              (Values.Val.offset_ptr sp (Ptrofs.repr (4 * ptr)))))
                spb.

Definition stack_bounds (sp : Values.val) (hi : Z) (m : mem) : Prop :=
  forall ptr v,
    hi <= ptr <= Ptrofs.max_unsigned ->
    Z.modulo ptr 4 = 0 ->
    Mem.loadv AST.Mint32 m (Values.Val.offset_ptr sp (Ptrofs.repr ptr )) = None /\
    Mem.storev AST.Mint32 m (Values.Val.offset_ptr sp (Ptrofs.repr ptr )) v = None.

Inductive match_frames : list GibleSubPar.stackframe -> list DHTL.stackframe -> Prop :=
| match_frames_nil :
    match_frames nil nil.

Inductive match_constants (rst fin: reg) (asr: assocmap) : Prop :=
  match_constant :
      asr!rst = Some (ZToValue 0) ->
      asr!fin = Some (ZToValue 0) ->
      match_constants rst fin asr.

Definition state_st_wf (asr: assocmap) (st_reg: reg) (st: positive) :=
  asr!st_reg = Some (posToValue st).
#[local] Hint Unfold state_st_wf : htlproof.

Inductive match_states : GibleSubPar.state -> DHTL.state -> Prop :=
| match_state : forall asa asr sf f sp sp' rs mem m st res ps
    (MASSOC : match_assocmaps (max_reg_function f) (max_pred_function f) rs ps asr)
    (TF : transl_module f = Errors.OK m)
    (WF : state_st_wf asr m.(DHTL.mod_st) st)
    (MF : match_frames sf res)
    (MARR : match_arrs f.(fn_stacksize) m.(DHTL.mod_stk) m.(DHTL.mod_stk_len) sp mem asa)
    (SP : sp = Values.Vptr sp' (Ptrofs.repr 0))
    (RSBP : reg_stack_based_pointers sp' rs)
    (ASBP : arr_stack_based_pointers sp' mem (f.(GibleSubPar.fn_stacksize)) sp)
    (BOUNDS : stack_bounds sp (f.(GibleSubPar.fn_stacksize)) mem)
    (CONST : match_constants m.(DHTL.mod_reset) m.(DHTL.mod_finish) asr),
    (* Add a relation about ps compared with the state register. *)
    match_states (GibleSubPar.State sf f sp st rs ps mem)
                 (DHTL.State res m st asr asa)
| match_returnstate :
    forall
      v v' stack mem res
      (MF : match_frames stack res),
      val_value_lessdef v v' ->
      match_states (GibleSubPar.Returnstate stack v mem) (DHTL.Returnstate res v')
| match_initial_call :
    forall f m m0
    (TF : transl_module f = Errors.OK m),
      match_states (GibleSubPar.Callstate nil (AST.Internal f) nil m0) (DHTL.Callstate nil m nil).
#[local] Hint Constructors match_states : htlproof.

Inductive match_states_reduced : nat -> GibleSubPar.state -> DHTL.state -> Prop :=
| match_states_reduced_intro : forall asa asr sf f sp sp' rs mem m st res ps n
    (MASSOC : match_assocmaps (max_reg_function f) (max_pred_function f) rs ps asr)
    (TF : transl_module f = Errors.OK m)
    (WF : state_st_wf asr m.(DHTL.mod_st) (Pos.of_nat (Pos.to_nat st - n)%nat))
    (MF : match_frames sf res)
    (MARR : match_arrs f.(fn_stacksize) m.(DHTL.mod_stk) m.(DHTL.mod_stk_len) sp mem asa)
    (SP : sp = Values.Vptr sp' (Ptrofs.repr 0))
    (RSBP : reg_stack_based_pointers sp' rs)
    (ASBP : arr_stack_based_pointers sp' mem (f.(GibleSubPar.fn_stacksize)) sp)
    (BOUNDS : stack_bounds sp (f.(GibleSubPar.fn_stacksize)) mem)
    (CONST : match_constants m.(DHTL.mod_reset) m.(DHTL.mod_finish) asr),
    (* Add a relation about ps compared with the state register. *)
    match_states_reduced n (GibleSubPar.State sf f sp st rs ps mem)
                 (DHTL.State res m (Pos.of_nat (Pos.to_nat st - n)%nat) asr asa).

Definition match_prog (p: GibleSubPar.program) (tp: DHTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp /\
  main_is_internal p = true.

Ltac unfold_match H :=
  match type of H with
  | context[match ?g with _ => _ end] => destruct g eqn:?; try discriminate
  end.

#[global] Instance TransfHTLLink (tr_fun: GibleSubPar.program -> Errors.res DHTL.program):
  TransfLink (fun (p1: GibleSubPar.program) (p2: DHTL.program) => match_prog p1 p2).
Proof.
  red. intros. exfalso. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  apply link_prog_inv in H.

  unfold match_prog in *.
  unfold main_is_internal in *. simplify. repeat (unfold_match H4).
  repeat (unfold_match H3). simplify.
  subst. rewrite H0 in *. specialize (H (AST.prog_main p2)).
  exploit H.
  apply Genv.find_def_symbol. exists b. split.
  assumption. apply Genv.find_funct_ptr_iff. eassumption.
  apply Genv.find_def_symbol. exists b0. split.
  assumption. apply Genv.find_funct_ptr_iff. eassumption.
  intros. inv H3. inv H5. destruct H6. inv H5.
Qed.

Definition match_prog' (p: GibleSubPar.program) (tp: DHTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Lemma match_prog_matches :
  forall p tp, match_prog p tp -> match_prog' p tp.
Proof. unfold match_prog. tauto. Qed.

Lemma transf_program_match:
  forall p tp, transl_program p = Errors.OK tp -> match_prog p tp.
Proof.
  intros. unfold transl_program in H.
  destruct (main_is_internal p) eqn:?; try discriminate.
  unfold match_prog. split.
  apply Linking.match_transform_partial_program; auto.
  assumption.
Qed.

Lemma max_reg_lt_resource :
  forall f n,
    Plt (max_resource_function f) n ->
    Plt (reg_enc (max_reg_function f)) n.
Proof.
  unfold max_resource_function, Plt, reg_enc, pred_enc in *; intros. lia.
Qed.

Lemma max_pred_lt_resource :
  forall f n,
    Plt (max_resource_function f) n ->
    Plt (pred_enc (max_pred_function f)) n.
Proof.
  unfold max_resource_function, Plt, reg_enc, pred_enc in *; intros. lia.
Qed.

Lemma plt_reg_enc :
  forall a b, Ple a b -> Ple (reg_enc a) (reg_enc b).
Proof. unfold Ple, reg_enc, pred_enc in *; intros. lia. Qed.

Lemma plt_pred_enc :
  forall a b, Ple a b -> Ple (pred_enc a) (pred_enc b).
Proof. unfold Ple, reg_enc, pred_enc in *; intros. lia. Qed.

Lemma reg_enc_inj :
  forall a b, reg_enc a = reg_enc b -> a = b.
Proof. unfold reg_enc; intros; lia. Qed.

Lemma pred_enc_inj :
  forall a b, pred_enc a = pred_enc b -> a = b.
Proof. unfold pred_enc; intros; lia. Qed.

(* Lemma regs_lessdef_add_greater : *)
(*   forall n m rs1 ps1 rs2 n v, *)
(*     Plt (max_resource_function f) n -> *)
(*     match_assocmaps n m rs1 ps1 rs2 -> *)
(*     match_assocmaps n m rs1 ps1 (AssocMap.set n v rs2). *)
(* Proof. *)
(*   inversion 2; subst. *)
(*   intros. constructor. *)
(*   - apply max_reg_lt_resource in H. intros. unfold find_assocmap. unfold AssocMapExt.get_default. *)
(*     rewrite AssocMap.gso. eauto. apply plt_reg_enc in H3. unfold Ple, Plt in *. lia. *)
(*   - apply max_pred_lt_resource in H. intros. unfold find_assocmap. unfold AssocMapExt.get_default. *)
(*     rewrite AssocMap.gso. eauto. apply plt_pred_enc in H3. unfold Ple, Plt in *. lia. *)
(* Qed. *)
(* #[local] Hint Resolve regs_lessdef_add_greater : htlproof. *)

Lemma pred_enc_reg_enc_ne :
  forall a b, pred_enc a <> reg_enc b.
Proof. unfold not, pred_enc, reg_enc; lia. Qed.

Lemma regs_lessdef_add_match :
  forall m n rs ps am r v v',
    val_value_lessdef v v' ->
    match_assocmaps m n rs ps am ->
    match_assocmaps m n (Registers.Regmap.set r v rs) ps (AssocMap.set (reg_enc r) v' am).
Proof.
  inversion 2; subst.
  constructor. intros.
  destruct (peq r0 r); subst.
  rewrite Registers.Regmap.gss.
  unfold find_assocmap. unfold AssocMapExt.get_default.
  rewrite AssocMap.gss. assumption.

  rewrite Registers.Regmap.gso; try assumption.
  unfold find_assocmap. unfold AssocMapExt.get_default.
  rewrite AssocMap.gso; eauto. unfold not in *; intros; apply n0. apply reg_enc_inj; auto.

  intros. pose proof (pred_enc_reg_enc_ne r0 r) as HNE.
  rewrite assocmap_gso by auto. now apply H2.
Qed.
#[local] Hint Resolve regs_lessdef_add_match : htlproof.

Lemma list_combine_none :
  forall n l,
    length l = n ->
    list_combine Verilog.merge_cell (list_repeat None n) l = l.
Proof.
  induction n; intros; crush.
  - symmetry. apply length_zero_iff_nil. auto.
  - destruct l; crush.
    rewrite list_repeat_cons.
    crush. f_equal.
    eauto.
Qed.

Lemma combine_none :
  forall n a,
    a.(arr_length) = n ->
    arr_contents (combine Verilog.merge_cell (arr_repeat None n) a) = arr_contents a.
Proof.
  intros.
  unfold combine.
  crush.

  rewrite <- (arr_wf a) in H.
  apply list_combine_none.
  assumption.
Qed.

Lemma list_combine_lookup_first :
  forall l1 l2 n,
    length l1 = length l2 ->
    nth_error l1 n = Some None ->
    nth_error (list_combine Verilog.merge_cell l1 l2) n = nth_error l2 n.
Proof.
  induction l1; intros; crush.

  rewrite nth_error_nil in H0.
  discriminate.

  destruct l2 eqn:EQl2. crush.
  simpl in H. inv H.
  destruct n; simpl in *.
  inv H0. simpl. reflexivity.
  eauto.
Qed.

Lemma combine_lookup_first :
  forall a1 a2 n,
    a1.(arr_length) = a2.(arr_length) ->
    array_get_error n a1 = Some None ->
    array_get_error n (combine Verilog.merge_cell a1 a2) = array_get_error n a2.
Proof.
  intros.

  unfold array_get_error in *.
  apply list_combine_lookup_first; eauto.
  rewrite a1.(arr_wf). rewrite a2.(arr_wf).
  assumption.
Qed.

Lemma list_combine_lookup_second :
  forall l1 l2 n x,
    length l1 = length l2 ->
    nth_error l1 n = Some (Some x) ->
    nth_error (list_combine Verilog.merge_cell l1 l2) n = Some (Some x).
Proof.
  induction l1; intros; crush; auto.

  destruct l2 eqn:EQl2. crush.
  simpl in H. inv H.
  destruct n; simpl in *.
  inv H0. simpl. reflexivity.
  eauto.
Qed.

Lemma combine_lookup_second :
  forall a1 a2 n x,
    a1.(arr_length) = a2.(arr_length) ->
    array_get_error n a1 = Some (Some x) ->
    array_get_error n (combine Verilog.merge_cell a1 a2) = Some (Some x).
Proof.
  intros.

  unfold array_get_error in *.
  apply list_combine_lookup_second; eauto.
  rewrite a1.(arr_wf). rewrite a2.(arr_wf).
  assumption.
Qed.

Ltac unfold_func H :=
  match type of H with
  | ?f = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ _ = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ _ _ = _ => unfold f in H; repeat (unfold_match H)
  | ?f _ _ _ _ = _ => unfold f in H; repeat (unfold_match H)
  end.

Lemma init_reg_assoc_empty :
  forall n m l,
    match_assocmaps n m (Gible.init_regs nil l) (PMap.init false) (DHTL.init_regs nil l).
Proof.
  induction l; simpl; constructor; intros.
  - rewrite Registers.Regmap.gi. unfold find_assocmap.
    unfold AssocMapExt.get_default. rewrite AssocMap.gempty.
    constructor.

  - rewrite Registers.Regmap.gi. unfold find_assocmap.
    unfold AssocMapExt.get_default. rewrite AssocMap.gempty.
    constructor.

  - rewrite Registers.Regmap.gi. unfold find_assocmap.
    unfold AssocMapExt.get_default. rewrite AssocMap.gempty.
    constructor.

  - rewrite Registers.Regmap.gi. unfold find_assocmap.
    unfold AssocMapExt.get_default. rewrite AssocMap.gempty.
    constructor.
Qed.

Lemma arr_lookup_some:
  forall (z : Z) (r0 : Registers.reg) (r : Verilog.reg) (asr : assocmap) (asa : Verilog.assocmap_arr)
    (stack : Array (option value)) (H5 : asa ! r = Some stack) n,
    exists x, Verilog.arr_assocmap_lookup asa r n = Some x.
Proof.
  intros z r0 r asr asa stack H5 n.
  eexists.
  unfold Verilog.arr_assocmap_lookup. rewrite H5. reflexivity.
Qed.
#[local] Hint Resolve arr_lookup_some : htlproof.

Section CORRECTNESS.

  Variable prog : GibleSubPar.program.
  Variable tprog : DHTL.program.

  Hypothesis TRANSL : match_prog prog tprog.

  Lemma TRANSL' :
    Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.
  Proof. intros; apply match_prog_matches; assumption. Qed.

  Let ge : GibleSubPar.genv := Globalenvs.Genv.globalenv prog.
  Let tge : DHTL.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. intros. eapply (Genv.find_symbol_match TRANSL'). Qed.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: GibleSubPar.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL'); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: GibleSubPar.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_match TRANSL'); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof
    (Genv.senv_transf_partial TRANSL').
  #[local] Hint Resolve senv_preserved : htlproof.

  Lemma ptrofs_inj :
    forall a b,
      Ptrofs.unsigned a = Ptrofs.unsigned b -> a = b.
  Proof.
    intros. rewrite <- Ptrofs.repr_unsigned. symmetry. rewrite <- Ptrofs.repr_unsigned.
    rewrite H. auto.
  Qed.

  Lemma op_stack_based :
    forall F V sp v m args rs op ge ver,
      translate_instr op args = Errors.OK ver ->
      reg_stack_based_pointers sp rs ->
      @Op.eval_operation F V ge (Values.Vptr sp Ptrofs.zero) op
                        (List.map (fun r : positive => Registers.Regmap.get r rs) args) m = Some v ->
      stack_based v sp.
  Proof.
    Ltac solve_no_ptr :=
      match goal with
      | H: reg_stack_based_pointers ?sp ?rs |- stack_based (Registers.Regmap.get ?r ?rs) _ =>
        solve [apply H]
      | H1: reg_stack_based_pointers ?sp ?rs, H2: Registers.Regmap.get _ _ = Values.Vptr ?b ?i
        |- context[Values.Vptr ?b _] =>
        let H := fresh "H" in
        assert (H: stack_based (Values.Vptr b i) sp) by (rewrite <- H2; apply H1); simplify; solve [auto]
      | |- context[Registers.Regmap.get ?lr ?lrs] =>
        destruct (Registers.Regmap.get lr lrs) eqn:?; simplify; auto
      | |- stack_based (?f _) _ => unfold f
      | |- stack_based (?f _ _) _ => unfold f
      | |- stack_based (?f _ _ _) _ => unfold f
      | |- stack_based (?f _ _ _ _) _ => unfold f
      | H: ?f _ _ = Some _ |- _ =>
        unfold f in H; repeat (unfold_match H); inv H
      | H: ?f _ _ _ _ _ _ = Some _ |- _ =>
        unfold f in H; repeat (unfold_match H); inv H
      | H: map (fun r : positive => Registers.Regmap.get r _) ?args = _ |- _ =>
        destruct args; inv H
      | |- context[if ?c then _ else _] => destruct c; try discriminate
      | H: match _ with _ => _ end = Some _ |- _ => repeat (unfold_match H; try discriminate)
      | H: match _ with _ => _ end = OK _ _ _ |- _ => repeat (unfold_match H; try discriminate)
      | |- context[match ?g with _ => _ end] => destruct g; try discriminate
      | |- _ => simplify; solve [auto]
      end.
    intros **.
    unfold translate_instr in *.
    unfold_match H; repeat (unfold_match H); simplify; try solve [repeat solve_no_ptr].
    subst.
    unfold translate_eff_addressing in H.
    repeat (unfold_match H; try discriminate); simplify; try solve [repeat solve_no_ptr].
  Qed.

  Lemma int_inj :
    forall x y,
      Int.unsigned x = Int.unsigned y ->
      x = y.
  Proof.
    intros. rewrite <- Int.repr_unsigned at 1. rewrite <- Int.repr_unsigned.
    rewrite <- H. trivial.
  Qed.

  Lemma Ptrofs_compare_correct :
    forall a b,
      Ptrofs.ltu (valueToPtr a) (valueToPtr b) = Int.ltu a b.
  Proof.
    intros. unfold valueToPtr. unfold Ptrofs.ltu. unfold Ptrofs.of_int. unfold Int.ltu.
    rewrite !Ptrofs.unsigned_repr in *; auto using Int.unsigned_range_2.
  Qed.

  Lemma eval_cond_correct :
    forall stk f sp pc rs m res ml st asr asa e b f' args cond pr,
      match_states (GibleSubPar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
      (forall v, In v args -> Ple v (max_reg_function f)) ->
      Op.eval_condition cond (List.map (fun r : positive => Registers.Regmap.get r rs) args) m = Some b ->
      translate_condition cond args = OK e ->
      Verilog.expr_runp f' asr asa e (boolToValue b).
  Proof.
    intros * MSTATE MAX_FUN EVAL TR_INSTR.
    unfold translate_condition, translate_comparison, translate_comparisonu, translate_comparison_imm, translate_comparison_immu in TR_INSTR.
    repeat (destruct_match; try discriminate); subst; unfold ret in *; match goal with H: OK _ = OK _ |- _ => inv H end; unfold bop in *; cbn in *;
     try (solve [econstructor; try econstructor; eauto; unfold binop_run;
      unfold Values.Val.cmp_bool, Values.Val.cmpu_bool in EVAL; repeat (destruct_match; try discriminate); inv EVAL;
      inv MSTATE; inv MASSOC;
      assert (X: Ple p (max_reg_function f)) by eauto;
      assert (X1: Ple p0 (max_reg_function f)) by eauto;
      apply H in X; apply H in X1;
      rewrite Heqv in X;
      rewrite Heqv0 in X1;
      inv X; inv X1; auto; try (rewrite Ptrofs_compare_correct; auto)|
      econstructor; try econstructor; eauto; unfold binop_run;
      unfold Values.Val.cmp_bool, Values.Val.cmpu_bool in EVAL; repeat (destruct_match; try discriminate); inv EVAL;
      inv MSTATE; inv MASSOC;
      assert (X: Ple p (max_reg_function f)) by eauto;
        apply H in X;
        rewrite Heqv in X;
        inv X; auto]).
  Qed.

  Lemma eval_cond_correct' :
    forall e stk f sp pc rs m res ml st asr asa v f' args cond pr,
      match_states (GibleSubPar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
      (forall v, In v args -> Ple v (max_reg_function f)) ->
      Values.Val.of_optbool None = v ->
      translate_condition cond args = OK e ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
  Proof.
    intros * MSTATE MAX_FUN EVAL TR_INSTR.
    unfold translate_condition, translate_comparison, translate_comparisonu,
    translate_comparison_imm, translate_comparison_immu, bop, boplit in *.
    repeat unfold_match TR_INSTR; inv TR_INSTR; repeat econstructor.
  Qed.

  Ltac eval_correct_tac :=
      match goal with
      | |- context[valueToPtr] => unfold valueToPtr
      | |- context[valueToInt] => unfold valueToInt
      | |- context[bop] => unfold bop
      | H : context[bop] |- _ => unfold bop in H
      | |- context[boplit] => unfold boplit
      | H : context[boplit] |- _ => unfold boplit in H
      | |- context[boplitz] => unfold boplitz
      | H : context[boplitz] |- _ => unfold boplitz in H
      | |- val_value_lessdef Values.Vundef _ => solve [constructor]
      | H : val_value_lessdef _ _ |- val_value_lessdef (Values.Vint _) _ => constructor; inv H
      | |- val_value_lessdef (Values.Vint _) _ => constructor; auto
      | H : ret _ _ = OK _ _ _ |- _ => inv H
      | H : _ :: _ = _ :: _ |- _ => inv H
      | |- context[match ?d with _ => _ end] => destruct d eqn:?; try discriminate
      | H : match ?d with _ => _ end = _ |- _ => repeat unfold_match H
      | H : match ?d with _ => _ end _ = _ |- _ => repeat unfold_match H
      | |- Verilog.expr_runp _ _ _ ?f _ =>
        match f with
        | Verilog.Vternary _ _ _ => idtac
        | _ => econstructor
        end
      | |- val_value_lessdef (?f _ _) _ => unfold f
      | |- val_value_lessdef (?f _) _ => unfold f
      | H : ?f (Registers.Regmap.get _ _) _ = Some _ |- _ =>
        unfold f in H; repeat (unfold_match H)
      | H1 : Registers.Regmap.get ?r ?rs = Values.Vint _, H2 : val_value_lessdef (Registers.Regmap.get ?r ?rs) _
        |- _ => rewrite H1 in H2; inv H2
      | |- _ => eexists; split; try constructor; solve [eauto]
      | |- context[if ?c then _ else _] => destruct c eqn:?; try discriminate
      | H : ?b = _ |- _ = boolToValue ?b => rewrite H
      end.

  Lemma eval_correct_Oshrximm :
    forall sp rs m v e asr asa f f' stk pc args res ml st n pr,
      match_states (GibleSubPar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
      Forall (fun x => (Ple x (max_reg_function f))) args ->
      Op.eval_operation ge sp (Op.Oshrximm n)
                        (List.map (fun r : BinNums.positive =>
                                     Registers.Regmap.get r rs) args) m = Some v ->
      translate_instr (Op.Oshrximm n) args = OK e ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
  Proof.
    intros * MSTATE INSTR EVAL TR_INSTR.
    pose proof MSTATE as MSTATE_2. inv MSTATE.
    inv MASSOC. unfold translate_instr in TR_INSTR; repeat (unfold_match TR_INSTR); inv TR_INSTR;
    unfold Op.eval_operation in EVAL; repeat (unfold_match EVAL); inv EVAL.
    (*repeat (simplify; eval_correct_tac; unfold valueToInt in * ).
            destruct (Z_lt_ge_dec (Int.signed i0) 0).
            econstructor.*)
    unfold Values.Val.shrx in *.
    destruct v0; try discriminate.
    destruct (Int.ltu n (Int.repr 31)) eqn:?; try discriminate.
    inversion H2. clear H2.
    assert (Int.unsigned n <= 30).
    { unfold Int.ltu in *. destruct (zlt (Int.unsigned n) (Int.unsigned (Int.repr 31))); try discriminate.
      rewrite Int.unsigned_repr in l by (simplify; lia).
      replace 31 with (Z.succ 30) in l by auto.
      apply Zlt_succ_le in l.
      auto.
    }
    rewrite IntExtra.shrx_shrx_alt_equiv in H3 by auto.
    unfold IntExtra.shrx_alt in *.
    destruct (zlt (Int.signed i) 0).
    - repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
      repeat (simplify; eval_correct_tac).
      unfold valueToInt in *. inv INSTR. apply H in H5. rewrite H4 in H5.
      inv H5. clear H6.
      unfold Int.lt in *. rewrite zlt_true in Heqb0. simplify.
      rewrite Int.unsigned_repr in Heqb0. discriminate.
      simplify; lia.
      unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
      auto.
      rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_true; try lia.
      simplify. inv INSTR. clear H6.  apply H in H5. rewrite H4 in H5. inv H5. auto.
    - econstructor; econstructor; [eapply Verilog.erun_Vternary_false|idtac]; repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
      repeat (simplify; eval_correct_tac).
      inv INSTR. clear H6. apply H in H5. rewrite H4 in H5.
      inv H5.
      unfold Int.lt in *. rewrite zlt_false in Heqb0. simplify.
      rewrite Int.unsigned_repr in Heqb0. lia.
      simplify; lia.
      unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
      auto.
      rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_false; try lia.
      simplify. inv INSTR. apply H in H5. unfold valueToInt in *. rewrite H4 in H5. inv H5. auto.
  Qed.

  Lemma max_reg_function_use:
    forall l y m,
      Forall (fun x => Ple x m) l ->
      In y l ->
      Ple y m.
  Proof.
    intros. eapply Forall_forall in H; eauto.
  Qed.

  Ltac eval_correct_tac' :=
      match goal with
      | |- context[valueToPtr] => unfold valueToPtr
      | |- context[valueToInt] => unfold valueToInt
      | |- context[bop] => unfold bop
      | H : context[bop] |- _ => unfold bop in H
      | |- context[boplit] => unfold boplit
      | H : context[boplit] |- _ => unfold boplit in H
      | |- context[boplitz] => unfold boplitz
      | H : context[boplitz] |- _ => unfold boplitz in H
      | |- val_value_lessdef Values.Vundef _ => solve [constructor]
      | H : val_value_lessdef _ _ |- val_value_lessdef (Values.Vint _) _ => constructor; inv H
      | |- val_value_lessdef (Values.Vint _) _ => constructor; auto
      | H : ret _ _ = OK _ _ _ |- _ => inv H
      | H : context[max_reg_function ?f]
        |- context[_ (Registers.Regmap.get ?r ?rs) (Registers.Regmap.get ?r0 ?rs)] =>
        let HPle1 := fresh "HPle" in
        let HPle2 := fresh "HPle" in
        assert (HPle1 : Ple r (max_reg_function f)) by (eapply max_reg_function_use; eauto; simpl; auto; repeat (apply in_cons; try solve [constructor; auto]));
        assert (HPle2 : Ple r0 (max_reg_function f)) by (eapply max_reg_function_use; eauto; simpl; auto; repeat (apply in_cons; try solve [constructor; auto]));
        apply H in HPle1; apply H in HPle2; eexists; split;
        [econstructor; eauto; constructor; trivial | inv HPle1; inv HPle2; try (constructor; auto)]
      | H : context[max_reg_function ?f]
        |- context[_ (Registers.Regmap.get ?r ?rs) _] =>
        let HPle1 := fresh "HPle" in
        assert (HPle1 : Ple r (max_reg_function f)) by (eapply max_reg_function_use; eauto; simpl; auto; repeat (apply in_cons; try solve [constructor; auto]));
        apply H in HPle1; eexists; split;
        [econstructor; eauto; constructor; trivial | inv HPle1; try (constructor; auto)]
      | H : _ :: _ = _ :: _ |- _ => inv H
      | |- context[match ?d with _ => _ end] => destruct d eqn:?; try discriminate
      | H : match ?d with _ => _ end = _ |- _ => repeat unfold_match H
      | H : match ?d with _ => _ end _ = _ |- _ => repeat unfold_match H
      | |- Verilog.expr_runp _ _ _ ?f _ =>
        match f with
        | Verilog.Vternary _ _ _ => idtac
        | _ => econstructor
        end
      | |- val_value_lessdef (?f _ _) _ => unfold f
      | |- val_value_lessdef (?f _) _ => unfold f
      | H : ?f (Registers.Regmap.get _ _) _ = Some _ |- _ =>
        unfold f in H; repeat (unfold_match H)
      | H1 : Registers.Regmap.get ?r ?rs = Values.Vint _, H2 : val_value_lessdef (Registers.Regmap.get ?r ?rs) _
        |- _ => rewrite H1 in H2; inv H2
      | |- _ => eexists; split; try constructor; solve [eauto]
      | H : context[max_reg_function ?f] |- context[_ (Verilog.Vvar ?r) (Verilog.Vvar ?r0)] =>
        let HPle1 := fresh "H" in
        let HPle2 := fresh "H" in
        assert (HPle1 : Ple r (max_reg_function f)) by (eapply max_reg_function_use; eauto; simpl; auto; repeat (apply in_cons; try solve [constructor; auto]));
        assert (HPle2 : Ple r0 (max_reg_function f)) by (eapply max_reg_function_use; eauto; simpl; auto; repeat (apply in_cons; try solve [constructor; auto]));
        apply H in HPle1; apply H in HPle2; eexists; split; try constructor; eauto
      | H : context[max_reg_function ?f] |- context[Verilog.Vvar ?r] =>
        let HPle := fresh "H" in
        assert (HPle : Ple r (max_reg_function f)) by (eapply max_reg_function_use; eauto; simpl; auto; repeat (apply in_cons; try solve [constructor; auto]));
        apply H in HPle; eexists; split; try constructor; eauto
      | |- context[if ?c then _ else _] => destruct c eqn:?; try discriminate
      | H : ?b = _ |- _ = boolToValue ?b => rewrite H
      end.

  Lemma int_unsigned_lt_ptrofs_max :
    forall a,
      0 <= Int.unsigned a <= Ptrofs.max_unsigned.
  Proof.
    intros. pose proof (Int.unsigned_range_2 a).
    assert (Int.max_unsigned = Ptrofs.max_unsigned) by auto.
    lia.
  Qed.

  Lemma ptrofs_unsigned_lt_int_max :
    forall a,
      0 <= Ptrofs.unsigned a <= Int.max_unsigned.
  Proof.
    intros. pose proof (Ptrofs.unsigned_range_2 a).
    assert (Int.max_unsigned = Ptrofs.max_unsigned) by auto.
    lia.
  Qed.

  Hint Resolve int_unsigned_lt_ptrofs_max : int_ptrofs.
  Hint Resolve ptrofs_unsigned_lt_int_max : int_ptrofs.
  Hint Resolve Ptrofs.unsigned_range_2 : int_ptrofs.
  Hint Resolve Int.unsigned_range_2 : int_ptrofs.

(* Ptrofs.agree32_of_int_eq: forall (a : ptrofs) (b : int), Ptrofs.agree32 a b -> Ptrofs.of_int b = a *)
(* Ptrofs.agree32_of_int: Archi.ptr64 = false -> forall b : int, Ptrofs.agree32 (Ptrofs.of_int b) b *)
(* Ptrofs.agree32_sub: *)
(*   Archi.ptr64 = false -> *)
(*   forall (a1 : ptrofs) (b1 : int) (a2 : ptrofs) (b2 : int), *)
(*   Ptrofs.agree32 a1 b1 -> Ptrofs.agree32 a2 b2 -> Ptrofs.agree32 (Ptrofs.sub a1 a2) (Int.sub b1 b2) *)
  Lemma eval_correct_sub :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.sub a b) (Int.sub a' b').
  Proof.
    intros * HPLE HPLE0.
    assert (ARCHI: Archi.ptr64 = false) by auto.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try solve [constructor; auto].
    - rewrite ARCHI. constructor. unfold valueToPtr.
      apply ptrofs_inj. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr; auto with int_ptrofs.
      apply Ptrofs.agree32_sub; auto; rewrite <- Int.repr_unsigned; now apply Ptrofs.agree32_repr.
    - rewrite ARCHI. destruct_match; constructor.
      unfold Ptrofs.to_int. unfold valueToInt.
      apply int_inj. rewrite Int.unsigned_repr; auto with int_ptrofs.
      apply Ptrofs.agree32_sub; auto; unfold valueToPtr; now apply Ptrofs.agree32_of_int.
  Qed.

  Lemma eval_correct_mul :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.mul a b) (Int.mul a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_mul' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.mul a (Values.Vint n)) (Int.mul a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_and :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.and a b) (Int.and a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_and' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.and a (Values.Vint n)) (Int.and a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_or :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.or a b) (Int.or a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_or' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.or a (Values.Vint n)) (Int.or a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_xor :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.xor a b) (Int.xor a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_xor' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.xor a (Values.Vint n)) (Int.xor a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try solve [constructor; auto].
  Qed.

  Lemma eval_correct_shl :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.shl a b) (Int.shl a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try destruct_match; now constructor.
  Qed.

  Lemma eval_correct_shl' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.shl a (Values.Vint n)) (Int.shl a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try destruct_match; now constructor.
  Qed.

  Lemma eval_correct_shr :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.shr a b) (Int.shr a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try destruct_match; now constructor.
  Qed.

  Lemma eval_correct_shr' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.shr a (Values.Vint n)) (Int.shr a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try destruct_match; now constructor.
  Qed.

  Lemma eval_correct_shru :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.shru a b) (Int.shru a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt; try destruct_match; now constructor.
  Qed.

  Lemma eval_correct_shru' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.shru a (Values.Vint n)) (Int.shru a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try destruct_match; now constructor.
  Qed.

  Lemma eval_correct_add :
    forall a b a' b',
      val_value_lessdef a a' ->
      val_value_lessdef b b' ->
      val_value_lessdef (Values.Val.add a b) (Int.add a' b').
  Proof.
    intros * HPLE HPLE0.
    inv HPLE; inv HPLE0; cbn in *; unfold valueToInt;
    try destruct_match; constructor; auto; unfold valueToPtr;
    unfold Ptrofs.of_int; apply ptrofs_inj;
    rewrite Ptrofs.unsigned_repr by auto with int_ptrofs;
    [rewrite Int.add_commut|]; apply Ptrofs.agree32_add; auto;
    rewrite <- Int.repr_unsigned; now apply Ptrofs.agree32_repr.
  Qed.

  Lemma eval_correct_add' :
    forall a a' n,
      val_value_lessdef a a' ->
      val_value_lessdef (Values.Val.add a (Values.Vint n)) (Int.add a' (intToValue n)).
  Proof.
    intros * HPLE.
    inv HPLE; cbn in *; unfold valueToInt; try destruct_match; try constructor; auto.
    unfold valueToPtr. apply ptrofs_inj. unfold Ptrofs.of_int.
    rewrite Ptrofs.unsigned_repr by auto with int_ptrofs.
    apply Ptrofs.agree32_add; auto. rewrite <- Int.repr_unsigned.
    apply Ptrofs.agree32_repr; auto.
    unfold intToValue. rewrite <- Int.repr_unsigned.
    apply Ptrofs.agree32_repr; auto.
  Qed.

  Lemma eval_correct :
    forall sp op rs m v e asr asa f f' stk pc args res ml st pr,
      match_states (GibleSubPar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
      Forall (fun x => (Ple x (max_reg_function f))) args ->
      Op.eval_operation ge sp op
                        (List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some v ->
      translate_instr op args = OK e ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
  Proof.
    intros * MSTATE INSTR EVAL TR_INSTR.
    pose proof MSTATE as MSTATE_2. inv MSTATE.
    inv MASSOC. unfold translate_instr in TR_INSTR; repeat (unfold_match TR_INSTR); inv TR_INSTR;
    unfold Op.eval_operation in EVAL; repeat (unfold_match EVAL); inv EVAL;
    repeat (simplify; eval_correct_tac; unfold valueToInt in *);
    repeat (apply Forall_cons_iff in INSTR; destruct INSTR as (?HPLE & INSTR));
      try (apply H in HPLE); try (apply H in HPLE0).
    - do 2 econstructor; eauto. repeat econstructor.
    - do 2 econstructor; eauto. repeat econstructor. cbn.
      inv HPLE; cbn; try solve [constructor]; unfold valueToInt in *.
      constructor; unfold valueToInt; auto.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_sub.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_mul.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_mul'.
    - inv H2. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - inv H2. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - inv H2. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - inv H2. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_and.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_and'.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_or.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_or'.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_xor.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_xor'.
    - do 2 econstructor; eauto. repeat econstructor. cbn. inv HPLE; now constructor.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shl.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shl'.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shr.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shr'.
    - inv H2. rewrite Heqv0 in HPLE. inv HPLE.
      assert (0 <= 31 <= Int.max_unsigned).
      { pose proof Int.two_wordsize_max_unsigned as Y.
        unfold Int.zwordsize, Int.wordsize, Wordsize_32.wordsize in Y. lia. }
      assert (Int.unsigned n <= 30).
      { unfold Int.ltu in Heqb. destruct_match; try discriminate.
        clear Heqs. rewrite Int.unsigned_repr in l by auto. lia. }
      rewrite IntExtra.shrx_shrx_alt_equiv by auto.
      case_eq (Int.lt (find_assocmap 32 (reg_enc p) asr) (ZToValue 0)); intros HLT.
      + assert ((if zlt (Int.signed (valueToInt (find_assocmap 32 (reg_enc p) asr))) 0 then true else false) = true).
        { destruct_match; auto; unfold valueToInt in *. exfalso.
          assert (Int.signed (find_assocmap 32 (reg_enc p) asr) < 0 -> False) by auto. apply H3. unfold Int.lt in HLT.
          destruct_match; try discriminate. auto. }
        destruct_match; try discriminate.
        do 2 econstructor; eauto. repeat econstructor. now rewrite HLT.
        constructor; cbn. unfold IntExtra.shrx_alt. rewrite Heqs. auto.
      + assert ((if zlt (Int.signed (valueToInt (find_assocmap 32 (reg_enc p) asr))) 0 then true else false) = false).
        { destruct_match; auto; unfold valueToInt in *. exfalso.
          assert (Int.signed (find_assocmap 32 (reg_enc p) asr) >= 0 -> False) by auto. apply H3. unfold Int.lt in HLT.
          destruct_match; try discriminate. auto. }
        destruct_match; try discriminate.
        do 2 econstructor; eauto. eapply erun_Vternary_false; repeat econstructor.
        now rewrite HLT.
        constructor; cbn. unfold IntExtra.shrx_alt. rewrite Heqs. auto.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shru.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shru'.
    - unfold translate_eff_addressing in H2.
      repeat (destruct_match; try discriminate); unfold boplitz in *; simplify;
          repeat (apply Forall_cons_iff in INSTR; destruct INSTR as (?HPLE & INSTR));
      try (apply H in HPLE); try (apply H in HPLE0).
      + inv H2. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        now apply eval_correct_add'.
      + inv H2. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        apply eval_correct_add; auto. apply eval_correct_add; auto.
        constructor; auto.
      + inv H2. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        apply eval_correct_add; try constructor; auto.
        apply eval_correct_mul; try constructor; auto.
      + inv H2. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        apply eval_correct_add; try constructor; auto.
        apply eval_correct_add; try constructor; auto.
        apply eval_correct_mul; try constructor; auto.
      + inv H2. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        assert (X: Archi.ptr64 = false) by auto.
        rewrite X in H3. inv H3.
        constructor. unfold valueToPtr. unfold Ptrofs.of_int.
        rewrite Int.unsigned_repr by auto with int_ptrofs.
        rewrite Ptrofs.repr_unsigned. apply Ptrofs.add_zero_l.
    - remember (Op.eval_condition cond (List.map (fun r : positive => rs !! r) args) m).
      destruct o. cbn. symmetry in Heqo.
      exploit eval_cond_correct; eauto. intros. apply Forall_forall with (x := v) in INSTR; auto.
      intros. econstructor. split. eauto. destruct b; constructor; auto.
      exploit eval_cond_correct'; eauto.
      intros. apply Forall_forall with (x := v) in INSTR; auto.
    - assert (HARCHI: Archi.ptr64 = false) by auto.
      unfold Errors.bind in *. destruct_match; try discriminate; []. inv H2.
      remember (Op.eval_condition c (List.map (fun r : positive => rs !! r) l0) m).
      destruct o; cbn; symmetry in Heqo.
      + exploit eval_cond_correct; eauto. intros. apply Forall_forall with (x := v) in INSTR; auto.
        intros. destruct b.
        * intros. econstructor. split. econstructor. eauto. econstructor; auto. auto.
          unfold Values.Val.normalize. rewrite HARCHI. destruct_match; auto; constructor.
        * intros. econstructor. split. eapply erun_Vternary_false; repeat econstructor. eauto. auto.
          unfold Values.Val.normalize. rewrite HARCHI. destruct_match; auto; constructor.
      + exploit eval_cond_correct'; eauto.
        intros. apply Forall_forall with (x := v) in INSTR; auto. simplify.
        case_eq (valueToBool x); intros HVALU.
        * econstructor. econstructor. econstructor. eauto. constructor. eauto. auto. constructor.
        * econstructor. econstructor. eapply erun_Vternary_false. eauto. constructor. eauto. auto. constructor.
  Qed.

Ltac name_goal name := refine ?[name].

Ltac unfold_merge :=
  unfold merge_assocmap; repeat (rewrite AssocMapExt.merge_add_assoc);
  try (rewrite AssocMapExt.merge_base_1).

  Lemma match_assocmaps_merge_empty:
    forall n m rs ps ars,
      match_assocmaps n m rs ps ars ->
      match_assocmaps n m rs ps (AssocMapExt.merge value empty_assocmap ars).
  Proof.
    inversion 1; subst; clear H.
    constructor; intros.
    rewrite merge_get_default2 by auto. auto.
    rewrite merge_get_default2 by auto. auto.
  Qed.

  Lemma match_constants_merge_empty:
    forall n m ars,
      match_constants n m ars ->
      match_constants n m (AssocMapExt.merge value empty_assocmap ars).
  Proof.
    inversion 1. constructor; unfold AssocMapExt.merge.
    - rewrite PTree.gcombine; auto.
    - rewrite PTree.gcombine; auto.
  Qed.

  Lemma match_state_st_wf_empty:
    forall asr st pc,
      state_st_wf asr st pc ->
      state_st_wf (AssocMapExt.merge value empty_assocmap asr) st pc.
  Proof.
    unfold state_st_wf; intros.
    unfold AssocMapExt.merge. rewrite AssocMap.gcombine by auto. rewrite H.
    rewrite AssocMap.gempty. auto.
  Qed.

  Lemma match_arrs_merge_empty:
    forall sz stk stk_len sp mem asa,
      match_arrs sz stk stk_len sp mem asa ->
      match_arrs sz stk stk_len sp mem (merge_arrs (DHTL.empty_stack stk stk_len) asa).
  Proof.
    inversion 1. inv H0. inv H3. inv H1. destruct stack. econstructor; unfold AssocMapExt.merge.
    split; [|split]; [| |split]; cbn in *.
    - unfold merge_arrs in *. rewrite AssocMap.gcombine by auto.
      setoid_rewrite H2. unfold DHTL.empty_stack. rewrite AssocMap.gss.
      cbn in *. eauto.
    - cbn. rewrite list_combine_length. rewrite list_repeat_len. lia.
    - cbn. rewrite list_combine_length. rewrite list_repeat_len. lia.
    - cbn; intros.
      assert ((Datatypes.length (list_combine merge_cell (list_repeat None arr_length) arr_contents)) = arr_length).
      { rewrite list_combine_length. rewrite list_repeat_len. lia. }
      rewrite H3 in H1. apply H4 in H1.
      inv H1; try constructor.
      assert (array_get_error (Z.to_nat ptr)
           {| arr_contents := arr_contents; arr_length := Datatypes.length arr_contents; arr_wf := eq_refl |} =
           (array_get_error (Z.to_nat ptr)
             (combine merge_cell (arr_repeat None (Datatypes.length arr_contents))
                {| arr_contents := arr_contents; arr_length := Datatypes.length arr_contents; arr_wf := eq_refl |}))).
      { apply array_get_error_equal; auto. cbn. now rewrite list_combine_none. }
      unfold get_mem in *.
      rewrite <- H1. auto.
  Qed.

  Lemma match_states_merge_empty :
    forall st f sp pc rs ps m st' modle asr asa,
      match_states (GibleSubPar.State st f sp pc rs ps m) (DHTL.State st' modle pc asr asa) ->
      match_states (GibleSubPar.State st f sp pc rs ps m) (DHTL.State st' modle pc (AssocMapExt.merge value empty_assocmap asr) asa).
  Proof.
    inversion 1; econstructor; eauto using match_assocmaps_merge_empty,
      match_constants_merge_empty, match_state_st_wf_empty.
  Qed.

  Lemma match_states_merge_empty_arr :
    forall st f sp pc rs ps m st' modle asr asa,
      match_states (GibleSubPar.State st f sp pc rs ps m) (DHTL.State st' modle pc asr asa) ->
      match_states (GibleSubPar.State st f sp pc rs ps m) (DHTL.State st' modle pc asr (merge_arrs (DHTL.empty_stack modle.(DHTL.mod_stk) modle.(DHTL.mod_stk_len)) asa)).
  Proof. inversion 1; econstructor; eauto using match_arrs_merge_empty. Qed.

  Lemma match_states_merge_empty_all :
    forall st f sp pc rs ps m st' modle asr asa,
      match_states (GibleSubPar.State st f sp pc rs ps m) (DHTL.State st' modle pc asr asa) ->
      match_states (GibleSubPar.State st f sp pc rs ps m) (DHTL.State st' modle pc (AssocMapExt.merge value empty_assocmap asr) (merge_arrs (DHTL.empty_stack modle.(DHTL.mod_stk) modle.(DHTL.mod_stk_len)) asa)).
  Proof. eauto using match_states_merge_empty, match_states_merge_empty_arr. Qed.

  Opaque AssocMap.get.
  Opaque AssocMap.set.
  Opaque AssocMapExt.merge.
  Opaque Verilog.merge_arr.

  Lemma match_assocmaps_ext :
    forall n m rs ps ars1 ars2,
      (forall x, Ple x n -> ars1 ! (reg_enc x) = ars2 ! (reg_enc x)) ->
      (forall x, Ple x m -> ars1 ! (pred_enc x) = ars2 ! (pred_enc x)) ->
      match_assocmaps n m rs ps ars1 ->
      match_assocmaps n m rs ps ars2.
  Proof.
    intros * YFRL YFRL2 YMATCH.
    inv YMATCH. constructor; intros x' YPLE.
    unfold "#", AssocMapExt.get_default in *.
    rewrite <- YFRL by auto. eauto.
    unfold "#", AssocMapExt.get_default. rewrite <- YFRL2 by auto. eauto.
  Qed.

  Definition e_assoc asr : reg_associations := mkassociations asr (AssocMap.empty _).
  Definition e_assoc_arr stk stk_len asr : arr_associations := mkassociations asr (DHTL.empty_stack stk stk_len).

  Lemma option_inv :
    forall A x y,
      @Some A x = Some y -> x = y.
  Proof. intros. inversion H. trivial. Qed.

  Lemma main_tprog_internal :
    forall b,
      Globalenvs.Genv.find_symbol tge tprog.(AST.prog_main) = Some b ->
      exists f, Genv.find_funct_ptr (Genv.globalenv tprog) b = Some (AST.Internal f).
  Proof.
    intros.
    destruct TRANSL. unfold main_is_internal in H1.
    repeat (unfold_match H1). replace b with b0.
    exploit function_ptr_translated; eauto. intros [tf [A B]].
    unfold transl_fundef, AST.transf_partial_fundef, Errors.bind in B.
    unfold_match B. inv B. econstructor. apply A.

    apply option_inv. rewrite <- Heqo. rewrite <- H.
    rewrite symbols_preserved. replace (AST.prog_main tprog) with (AST.prog_main prog).
    trivial. symmetry; eapply Linking.match_program_main; eauto.
  Qed.

  Lemma transl_initial_states :
    forall s1 : Smallstep.state (GibleSubPar.semantics prog),
      Smallstep.initial_state (GibleSubPar.semantics prog) s1 ->
      exists s2 : Smallstep.state (DHTL.semantics tprog),
        Smallstep.initial_state (DHTL.semantics tprog) s2 /\ match_states s1 s2.
  Proof.
    induction 1.
    destruct TRANSL. unfold main_is_internal in H4.
    repeat (unfold_match H4).
    assert (f = AST.Internal f1). apply option_inv.
    rewrite <- Heqo0. rewrite <- H1. replace b with b0.
    auto. apply option_inv. rewrite <- H0. rewrite <- Heqo.
    trivial.
    exploit function_ptr_translated; eauto.
    intros [tf [A B]].
    unfold transl_fundef, Errors.bind in B.
    unfold AST.transf_partial_fundef, Errors.bind in B.
    repeat (unfold_match B). inversion B. subst.
    exploit main_tprog_internal; eauto; intros.
    rewrite symbols_preserved. replace (AST.prog_main tprog) with (AST.prog_main prog).
    apply Heqo. symmetry; eapply Linking.match_program_main; eauto.
    inversion H5.
    econstructor; split. econstructor.
    apply (Genv.init_mem_transf_partial TRANSL'); eauto.
    replace (AST.prog_main tprog) with (AST.prog_main prog).
    rewrite symbols_preserved; eauto.
    symmetry; eapply Linking.match_program_main; eauto.
    apply H6.

    constructor. inv B.
    assert (Some (AST.Internal x) = Some (AST.Internal m)).
    replace (AST.fundef DHTL.module) with (DHTL.fundef).
    rewrite <- H6. setoid_rewrite <- A. trivial.
    trivial. inv H7. assumption.
  Qed.
  #[local] Hint Resolve transl_initial_states : htlproof.

  Lemma transl_final_states :
    forall (s1 : Smallstep.state (GibleSubPar.semantics prog))
           (s2 : Smallstep.state (DHTL.semantics tprog))
           (r : Integers.Int.int),
      match_states s1 s2 ->
      Smallstep.final_state (GibleSubPar.semantics prog) s1 r ->
      Smallstep.final_state (DHTL.semantics tprog) s2 r.
  Proof.
    intros. inv H0. inv H. inv H4. inv MF. constructor. reflexivity.
  Qed.
  #[local] Hint Resolve transl_final_states : htlproof.

  Lemma ple_max_resource_function:
    forall f r,
      Ple r (max_reg_function f) ->
      Ple (reg_enc r) (max_resource_function f).
  Proof.
    intros * Hple.
    unfold max_resource_function, reg_enc, Ple in *. lia.
  Qed.

  Lemma ple_pred_max_resource_function:
    forall f r,
      Ple r (max_pred_function f) ->
      Ple (pred_enc r) (max_resource_function f).
  Proof.
    intros * Hple.
    unfold max_resource_function, pred_enc, Ple in *. lia.
  Qed.

  Lemma stack_correct_inv :
    forall s,
      stack_correct s = true ->
      (0 <= s) /\ (s < Ptrofs.modulus) /\ (s mod 4 = 0).
  Proof.
    unfold stack_correct; intros.
    crush.
  Qed.

  Lemma init_regs_empty:
    forall l, init_regs nil l = (Registers.Regmap.init Values.Vundef).
  Proof. destruct l; auto. Qed.

  Lemma dhtl_init_regs_empty:
    forall l, DHTL.init_regs nil l = (AssocMap.empty _).
  Proof. destruct l; auto. Qed.

Lemma assocmap_gempty :
  forall n a,
    find_assocmap n a (AssocMap.empty _) = ZToValue 0.
Proof.
  intros. unfold find_assocmap, AssocMapExt.get_default.
  now rewrite AssocMap.gempty.
Qed.

  Lemma transl_iop_correct:
    forall ctrl sp max_reg max_pred d d' curr_p next_p rs ps m rs' ps' p op args dst asr arr asr' arr' stk stk_len n,
      transf_instr n ctrl (curr_p, d) (RBop p op args dst) = Errors.OK (next_p, d') ->
      step_instr ge sp (Iexec (mk_instr_state rs ps m)) (RBop p op args dst) (Iexec (mk_instr_state rs' ps m)) ->
      stmnt_runp tt (e_assoc asr) (e_assoc_arr stk stk_len arr) d (e_assoc asr') (e_assoc_arr stk stk_len arr') ->
      match_assocmaps max_reg max_pred rs ps asr' ->
      exists asr'', stmnt_runp tt (e_assoc asr) (e_assoc_arr stk stk_len arr) d' (e_assoc asr'') (e_assoc_arr stk stk_len arr')
        /\ match_assocmaps max_reg max_pred rs' ps' asr''.
  Proof.
    Admitted.

Transparent Mem.load.
Transparent Mem.store.
Transparent Mem.alloc.
  Lemma transl_callstate_correct:
    forall (s : list GibleSubPar.stackframe) (f : GibleSubPar.function) (args : list Values.val)
      (m : mem) (m' : Mem.mem') (stk : Values.block),
      Mem.alloc m 0 (GibleSubPar.fn_stacksize f) = (m', stk) ->
      forall R1 : DHTL.state,
        match_states (GibleSubPar.Callstate s (AST.Internal f) args m) R1 ->
        exists R2 : DHTL.state,
          Smallstep.plus DHTL.step tge R1 Events.E0 R2 /\
          match_states
            (GibleSubPar.State s f (Values.Vptr stk Integers.Ptrofs.zero) (GibleSubPar.fn_entrypoint f)
                       (Gible.init_regs args (GibleSubPar.fn_params f)) (PMap.init false) m') R2.
  Proof.
    intros * H R1 MSTATE.

    inversion MSTATE; subst. inversion TF; subst.
    econstructor. split. apply Smallstep.plus_one.
    eapply DHTL.step_call.

    unfold transl_module, Errors.bind, Errors.bind2, ret in *.
    repeat (destruct_match; try discriminate; []). inv TF. cbn.
    econstructor; eauto; inv MSTATE; inv H1; eauto.

    - constructor; intros.
      + pose proof (ple_max_resource_function f r H0) as Hple.
        unfold Ple in *. repeat rewrite assocmap_gso by lia. rewrite init_regs_empty.
        rewrite dhtl_init_regs_empty. rewrite assocmap_gempty. rewrite Registers.Regmap.gi.
        constructor.
      + pose proof (ple_pred_max_resource_function f r H0) as Hple.
        unfold Ple in *. repeat rewrite assocmap_gso by lia.
        rewrite dhtl_init_regs_empty. rewrite assocmap_gempty. rewrite PMap.gi.
        auto.
    - cbn in *. unfold state_st_wf. repeat rewrite AssocMap.gso by lia.
      now rewrite AssocMap.gss.
    - constructor.
    - unfold DHTL.empty_stack. cbn in *. econstructor. repeat split; intros.
      + now rewrite AssocMap.gss.
      + cbn. now rewrite list_repeat_len.
      + cbn. now rewrite list_repeat_len.
      + destruct (Mem.loadv Mint32 m' (Values.Val.offset_ptr (Values.Vptr stk Ptrofs.zero) (Ptrofs.repr (4 * ptr)))) eqn:Heqn; constructor.
        unfold Mem.loadv in Heqn. destruct_match; try discriminate. cbn in Heqv0.
        symmetry in Heqv0. inv Heqv0.
        pose proof Mem.load_alloc_same as LOAD_ALLOC.
        pose proof H as ALLOC.
        eapply LOAD_ALLOC in ALLOC; eauto; subst. constructor.
    - unfold reg_stack_based_pointers; intros. unfold stack_based.
      unfold init_regs;
      destruct (GibleSubPar.fn_params f);
      rewrite Registers.Regmap.gi; constructor.
    - unfold arr_stack_based_pointers; intros. unfold stack_based.
      destruct (Mem.loadv Mint32 m' (Values.Val.offset_ptr (Values.Vptr stk Ptrofs.zero) (Ptrofs.repr (4 * ptr)))) eqn:LOAD; cbn; auto.
      pose proof Mem.load_alloc_same as LOAD_ALLOC.
      pose proof H as ALLOC.
      eapply LOAD_ALLOC in ALLOC. now rewrite ALLOC.
      exact LOAD.
    - unfold stack_bounds; intros. split.
      + unfold Mem.loadv. destruct_match; auto.
        unfold Mem.load, Mem.alloc in *. inv H. cbn -[Ptrofs.max_unsigned] in *.
        destruct_match; auto. unfold Mem.valid_access, Mem.range_perm, Mem.perm, Mem.perm_order' in *.
        clear Heqs2. inv v0. cbn -[Ptrofs.max_unsigned] in *. inv Heqv0. exfalso.
        specialize (H ptr). rewrite ! Ptrofs.add_zero_l in H. rewrite ! Ptrofs.unsigned_repr in H.
        specialize (H ltac:(lia)). destruct_match; auto. rewrite PMap.gss in Heqo.
        destruct_match; try discriminate. simplify. apply proj_sumbool_true in H5. lia.
        apply stack_correct_inv in Heqb. lia.
      + unfold Mem.storev. destruct_match; auto.
        unfold Mem.store, Mem.alloc in *. inv H. cbn -[Ptrofs.max_unsigned] in *.
        destruct_match; auto. unfold Mem.valid_access, Mem.range_perm, Mem.perm, Mem.perm_order' in *.
        clear Heqs2. inv v0. cbn -[Ptrofs.max_unsigned] in *. inv Heqv0. exfalso.
        specialize (H ptr). rewrite ! Ptrofs.add_zero_l in H. rewrite ! Ptrofs.unsigned_repr in H.
        specialize (H ltac:(lia)). destruct_match; auto. rewrite PMap.gss in Heqo.
        destruct_match; try discriminate. simplify. apply proj_sumbool_true in H5. lia.
        apply stack_correct_inv in Heqb. lia.
    - cbn; constructor; repeat rewrite PTree.gso by lia; now rewrite PTree.gss.
  Qed.
Opaque Mem.load.
Opaque Mem.store.
Opaque Mem.alloc.

  Lemma transl_returnstate_correct:
    forall (res0 : Registers.reg) (f : GibleSubPar.function) (sp : Values.val) (pc : Gible.node)
      (rs : Gible.regset) (s : list GibleSubPar.stackframe) (vres : Values.val) (m : mem) ps
      (R1 : DHTL.state),
      match_states (GibleSubPar.Returnstate (GibleSubPar.Stackframe res0 f sp pc rs ps :: s) vres m) R1 ->
      exists R2 : DHTL.state,
        Smallstep.plus DHTL.step tge R1 Events.E0 R2 /\
        match_states (GibleSubPar.State s f sp pc (Registers.Regmap.set res0 vres rs) ps m) R2.
  Proof.
    intros * MSTATE.
    inversion MSTATE. inversion MF.
  Qed.
  #[local] Hint Resolve transl_returnstate_correct : htlproof.

  Lemma mfold_left_error:
    forall A B f l m, @mfold_left A B f l (Error m) = Error m.
  Proof. now induction l. Qed.

  Lemma mfold_left_cons:
    forall A B f a l x y, 
      @mfold_left A B f (a :: l) x = OK y ->
      exists x' y', @mfold_left A B f l (OK y') = OK y /\ f x' a = OK y' /\ x = OK x'.
  Proof.
    intros.
    destruct x; [|now rewrite mfold_left_error in H].
    cbn in H.
    replace (fold_left (fun (a : mon A) (b : B) => bind (fun a' : A => f a' b) a) l (f a0 a) = OK y) with
      (mfold_left f l (f a0 a) = OK y) in H by auto.
    destruct (f a0 a) eqn:?; [|now rewrite mfold_left_error in H].
    eauto.
  Qed.

  Lemma mfold_left_app:
    forall A B f a l x y, 
      @mfold_left A B f (a ++ l) x = OK y ->
      exists y', @mfold_left A B f a x = OK y' /\ @mfold_left A B f l (OK y') = OK y.
  Proof.
    induction a.
    - intros. destruct x; [|now rewrite mfold_left_error in H]. exists a. eauto.
    - intros. destruct x; [|now rewrite mfold_left_error in H]. rewrite <- app_comm_cons in H.
      exploit mfold_left_cons; eauto.
  Qed.

  Lemma step_cf_instr_pc_ind :
    forall s f sp rs' pr' m' pc pc' cf t state,
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf t state ->
      step_cf_instr ge (GibleSubPar.State s f sp pc' rs' pr' m') cf t state.
  Proof. destruct cf; intros; inv H; econstructor; eauto. Qed.

  Definition mk_ctrl f := {|
                 ctrl_st := Pos.succ (max_resource_function f);
                 ctrl_stack := Pos.succ (Pos.succ (Pos.succ (Pos.succ (max_resource_function f))));
                 ctrl_fin := Pos.succ (Pos.succ (max_resource_function f));
                 ctrl_return := Pos.succ (Pos.succ (Pos.succ (max_resource_function f)))
               |}.

  Lemma step_list_inter_not_term :
    forall A step_i sp i cf l i' cf',
      @step_list_inter A step_i sp (Iterm i cf) l (Iterm i' cf') ->
      i = i' /\ cf = cf'.
  Proof. now inversion 1. Qed.

  Lemma step_exec_concat2' :
    forall sp i c a l cf,
      SubParBB.step_instr_list ge sp (Iexec a) i (Iterm c cf) ->
      SubParBB.step_instr_list ge sp (Iexec a) (i ++ l) (Iterm c cf).
  Proof. 
    induction i.
    - inversion 1.
    - inversion 1; subst; clear H; cbn.
      destruct i1. econstructor; eauto. eapply IHi; eauto.
      exploit step_list_inter_not_term; eauto; intros. inv H.
      eapply exec_term_RBcons; eauto. eapply exec_term_RBcons_term.
  Qed.

  Lemma step_exec_concat' :
    forall sp i c a b l,
      SubParBB.step_instr_list ge sp (Iexec a) i (Iexec c) ->
      SubParBB.step_instr_list ge sp (Iexec c) l b ->
      SubParBB.step_instr_list ge sp (Iexec a) (i ++ l) b.
  Proof.
    induction i.
    - inversion 1. eauto.
    - inversion 1; subst. clear H. cbn. intros. econstructor; eauto.
      destruct i1; [|inversion H6].
      eapply IHi; eauto.
  Qed.

  Lemma step_exec_concat:
    forall sp bb a b,
      SubParBB.step ge sp a bb b ->
      SubParBB.step_instr_list ge sp a (concat bb) b.
  Proof.
    induction bb.
    - inversion 1.
    - inversion 1; subst; clear H.
      + cbn. eapply step_exec_concat'; eauto.
      + cbn in *. eapply step_exec_concat2'; eauto.
  Qed.

  Lemma one_ne_zero:
    Int.repr 1 <> Int.repr 0.
  Proof.
    unfold not; intros.
    assert (Int.unsigned (Int.repr 1) = Int.unsigned (Int.repr 0)) by (now rewrite H).
    rewrite ! Int.unsigned_repr in H0 by crush. lia.
  Qed.

  Lemma int_and_boolToValue :
    forall b1 b2,
      Int.and (boolToValue b1) (boolToValue b2) = boolToValue (b1 && b2).
  Proof.
    destruct b1; destruct b2; cbn; unfold boolToValue; unfold natToValue;
    replace (Z.of_nat 1) with 1 by auto;
    replace (Z.of_nat 0) with 0 by auto.
    - apply Int.and_idem.
    - apply Int.and_zero.
    - apply Int.and_zero_l.
    - apply Int.and_zero.
  Qed.

  Lemma int_or_boolToValue :
    forall b1 b2,
      Int.or (boolToValue b1) (boolToValue b2) = boolToValue (b1 || b2).
  Proof.
    destruct b1; destruct b2; cbn; unfold boolToValue; unfold natToValue;
    replace (Z.of_nat 1) with 1 by auto;
    replace (Z.of_nat 0) with 0 by auto.
    - apply Int.or_idem.
    - apply Int.or_zero.
    - apply Int.or_zero_l.
    - apply Int.or_zero_l.
  Qed.

  Lemma pred_expr_correct :
    forall curr_p pr asr asa,
      (forall r, Ple r (max_predicate curr_p) ->
          find_assocmap 1 (pred_enc r) asr = boolToValue (PMap.get r pr)) ->
      expr_runp tt asr asa (pred_expr curr_p) (boolToValue (eval_predf pr curr_p)).
  Proof.
    induction curr_p.
    - intros * HFRL. cbn. destruct p as [b p']. destruct b.
      + constructor. eapply HFRL. cbn. unfold Ple. lia.
      + econstructor. constructor. eapply HFRL. cbn. unfold Ple; lia.
        econstructor. cbn. f_equal. unfold boolToValue.
        f_equal. destruct pr !! p' eqn:?. cbn.
        rewrite Int.eq_false; auto. unfold natToValue.
        replace (Z.of_nat 1) with 1 by auto. unfold Int.zero.
        apply one_ne_zero.
        cbn. rewrite Int.eq_true; auto.
    - intros. cbn. constructor.
    - intros. cbn. constructor.
    - cbn -[eval_predf]; intros. econstructor. eapply IHcurr_p1. intros. eapply H.
      unfold Ple in *. lia.
      eapply IHcurr_p2; intros. eapply H. unfold Ple in *; lia.
      cbn -[eval_predf]. f_equal. symmetry. apply int_and_boolToValue.
    - cbn -[eval_predf]; intros. econstructor. eapply IHcurr_p1. intros. eapply H.
      unfold Ple in *. lia.
      eapply IHcurr_p2; intros. eapply H. unfold Ple in *; lia.
      cbn -[eval_predf]. f_equal. symmetry. apply int_or_boolToValue.
  Qed.

  Local Opaque deep_simplify.

  Lemma valueToBool_correct: 
    forall b,
      valueToBool (boolToValue b) = b.
  Proof.
    unfold valueToBool, boolToValue; intros. 
    unfold uvalueToZ, natToValue. destruct b; cbn;
    rewrite Int.unsigned_repr; crush.
  Qed.

  Lemma negb_inj':
    forall a b, a = b -> negb a = negb b.
  Proof. intros. destruct a, b; auto. Qed.

  Lemma transl_predicate_correct :
    forall asr asa a b asr' asa' p r e max_pred max_reg rs ps,
      stmnt_runp tt (e_assoc asr) (e_assoc_arr a b asa) (translate_predicate Vblock (Some p) (Vvar r) e) (e_assoc asr') (e_assoc_arr a b asa') ->
      Ple (max_predicate p) max_pred ->
      match_assocmaps max_reg max_pred rs ps asr ->
      eval_predf ps p = false ->
      (forall x, asr # x = asr' # x) /\ asa = asa'.
  Proof.
    intros * HSTMNT HPLE HMATCH HEVAL *.
    pose proof HEVAL as HEVAL_DEEP.
    erewrite <- eval_predf_deep_simplify in HEVAL_DEEP.
    cbn in *. destruct_match.
    - inv HSTMNT; inv H6. split; auto. intros.
      exploit pred_expr_correct. inv HMATCH; eauto. intros. eapply H0. instantiate (1 := deep_simplify peq p) in H1.
      eapply max_predicate_deep_simplify in H1. unfold Ple in *. lia.
      intros. inv H7. unfold e_assoc in *; cbn in *. 
      pose proof H as H'. eapply expr_runp_determinate in H6; eauto. rewrite HEVAL_DEEP in H6.
      rewrite H6 in H10. now rewrite valueToBool_correct in H10.
      unfold e_assoc_arr, e_assoc in *; cbn in *. inv H9.
      destruct (peq r0 x); subst; [now rewrite assocmap_gss|now rewrite assocmap_gso by auto].
    - unfold sat_pred_simple in Heqo. repeat (destruct_match; try discriminate).
      unfold eval_predf in HEVAL_DEEP. 
      apply negb_inj' in HEVAL_DEEP.
      rewrite <- negate_correct in HEVAL_DEEP. rewrite e0 in HEVAL_DEEP. discriminate.
  Qed.

  Inductive lessdef_memory: option value -> option value -> Prop := 
  | lessdef_memory_none: 
    lessdef_memory None (Some (ZToValue 0))
  | lessdef_memory_eq: forall a,
    lessdef_memory a a.

  Lemma transl_predicate_correct_arr :
    forall asr asa a b asr' asa' p r e max_pred max_reg rs ps e1,
      stmnt_runp tt (e_assoc asr) (e_assoc_arr a b asa) (translate_predicate Vblock (Some p) (Vvari r e1) e) (e_assoc asr') (e_assoc_arr a b asa') ->
      Ple (max_predicate p) max_pred ->
      match_assocmaps max_reg max_pred rs ps asr ->
      eval_predf ps p = false ->
      asr = asr' /\ (forall x a, asa ! x = Some a -> exists a', asa' ! x = Some a'
                     /\ (forall y, (y < arr_length a)%nat -> exists av av', array_get_error y a = Some av /\ array_get_error y a' = Some av' /\ lessdef_memory av av')).
  Proof.
    intros * HSTMNT HPLE HMATCH HEVAL *.
    pose proof HEVAL as HEVAL_DEEP.
    erewrite <- eval_predf_deep_simplify in HEVAL_DEEP.
    cbn in *. destruct_match.
    - inv HSTMNT; inv H6; split; auto; intros.
      exploit pred_expr_correct. inv HMATCH; eauto. intros. eapply H1. instantiate (1 := deep_simplify peq p) in H2.
      eapply max_predicate_deep_simplify in H2. unfold Ple in *. lia.
      intros. inv H7. unfold e_assoc in *; cbn in *.
      pose proof H0 as H'. eapply expr_runp_determinate in H9; eauto. rewrite HEVAL_DEEP in H9.
      rewrite H9 in H12. now rewrite valueToBool_correct in H12.
      unfold e_assoc_arr, e_assoc in *; cbn in *. inv H11.
      destruct (peq r0 x); subst. 
      + unfold arr_assocmap_set. rewrite H.
        rewrite AssocMap.gss. eexists. split; eauto. unfold arr_assocmap_lookup in H10.
        rewrite H in H10. inv H10. eapply expr_runp_determinate in H3; eauto. subst.
        intros.
        destruct (Nat.eq_dec y (valueToNat i)); subst.
        * rewrite array_get_error_set_bound by auto.
          destruct (array_get_error (valueToNat i) a1) eqn:?.
          -- do 2 eexists. split; eauto. split. eauto.
             destruct o; cbn; constructor.
          -- exploit (@array_get_error_bound (option value)); eauto. simplify. 
             rewrite H3 in Heqo0. discriminate.
        * rewrite array_gso by auto.
          exploit (@array_get_error_bound (option value)); eauto. simplify.
          rewrite H3. do 2 eexists; repeat split; constructor.
      + unfold arr_assocmap_set. destruct_match.
        * rewrite PTree.gso by auto. setoid_rewrite H. eexists. split; eauto.
          intros. exploit (@array_get_error_bound (option value)); eauto. simplify.
          rewrite H4. do 2 eexists; repeat split; constructor.
        * eexists. split; eauto. intros. exploit (@array_get_error_bound (option value)); eauto. simplify.
          rewrite H4. do 2 eexists; repeat split; constructor.
    - unfold sat_pred_simple in Heqo. repeat (destruct_match; try discriminate).
      unfold eval_predf in HEVAL_DEEP. 
      apply negb_inj' in HEVAL_DEEP.
      rewrite <- negate_correct in HEVAL_DEEP. rewrite e0 in HEVAL_DEEP. discriminate.
  Qed.

  Lemma transl_predicate_correct2 :
    forall asr asa a b p r e max_pred max_reg rs ps,
      Ple (max_predicate p) max_pred ->
      match_assocmaps max_reg max_pred rs ps asr ->
      eval_predf ps p = false ->
      exists asr', stmnt_runp tt (e_assoc asr) (e_assoc_arr a b asa) (translate_predicate Vblock (Some p) (Vvar r) e) (e_assoc asr') (e_assoc_arr a b asa) /\ (forall x, asr # x = asr' # x).
  Proof.
    intros * HPLE HMATCH HEVAL. pose proof HEVAL as HEVAL_DEEP. 
    unfold translate_predicate. erewrite <- eval_predf_deep_simplify in HEVAL_DEEP.
    destruct_match.
    - econstructor; split.
      + econstructor; [econstructor|]. eapply erun_Vternary_false. 
        * eapply pred_expr_correct. intros. eapply max_predicate_deep_simplify in H.
        inv HMATCH. eapply H1; unfold Ple in *. lia.
        * now econstructor.
        * rewrite HEVAL_DEEP. auto.
      + intros. destruct (peq x r); subst.
        * now rewrite assocmap_gss.
        * now rewrite assocmap_gso.
   - unfold sat_pred_simple in Heqo. repeat (destruct_match; try discriminate).
     apply negb_inj' in HEVAL_DEEP. unfold eval_predf in *. rewrite <- negate_correct in HEVAL_DEEP.
     now rewrite e0 in HEVAL_DEEP.
  Qed.

  Lemma arr_assocmap_set_gss :
    forall r i v asa ar,
      asa ! r = Some ar ->
      (arr_assocmap_set r i v asa) ! r = Some (array_set i (Some v) ar).
  Proof.
    unfold arr_assocmap_set.
    intros. rewrite H. rewrite PTree.gss. auto.
  Qed.

  Lemma arr_assocmap_set_gso :
    forall r x i v asa ar,
      asa ! x = Some ar ->
      r <> x ->
      (arr_assocmap_set r i v asa) ! x = asa ! x.
  Proof.
    unfold arr_assocmap_set. intros. 
    destruct (asa!r) eqn:?; auto; now rewrite PTree.gso by auto.
  Qed.

  Lemma arr_assocmap_set_gs2 :
    forall r x i v asa,
      asa ! x = None ->
      (arr_assocmap_set r i v asa) ! x = None.
  Proof.
    unfold arr_assocmap_set. intros. 
    destruct (peq r x); subst; [now rewrite H|].
    destruct (asa!r) eqn:?; auto.
    now rewrite PTree.gso by auto.
  Qed.

  Lemma get_mem_set_array_gss :
    forall y a x,
      (y < arr_length a)%nat ->
      get_mem y (array_set y (Some x) a) = x.
  Proof.
    unfold get_mem; intros.
    rewrite array_get_error_set_bound by eauto; auto.
  Qed.

  Lemma get_mem_set_array_gss2 :
    forall y a,
      (y < arr_length a)%nat ->
      get_mem y (array_set y None a) = ZToValue 0.
  Proof.
    unfold get_mem; intros.
    rewrite array_get_error_set_bound by eauto; auto.
  Qed.

  Lemma get_mem_set_array_gso :
    forall y a x z,
      y <> z ->
      get_mem y (array_set z x a) = get_mem y a.
  Proof. unfold get_mem; intros. now rewrite array_gso by auto. Qed.

  Lemma get_mem_set_array_gso2 :
    forall y a x z,
      (y >= arr_length a)%nat ->
      get_mem y (array_set z x a) = ZToValue 0.
  Proof.
    intros; unfold get_mem. unfold array_get_error.
    erewrite array_set_len with (i:=z) (x:=x) in H.
    remember (array_set z x a). destruct a0. cbn in *. rewrite <- arr_wf in H.
    assert (Datatypes.length arr_contents <= y)%nat by lia.
    apply nth_error_None in H0. rewrite H0. auto.
  Qed.

  Lemma get_mem_set_array_gss3 :
    forall y a,
      get_mem y (array_set y None a) = ZToValue 0.
  Proof.
    intros.
    assert (y < arr_length a \/ y >= arr_length a)%nat by lia.
    inv H.
    - now rewrite get_mem_set_array_gss2.
    - now rewrite get_mem_set_array_gso2.
  Qed.

  Lemma arr_assocmap_lookup_get_mem: 
    forall asa r i v,
      arr_assocmap_lookup asa r i = Some v ->
      exists ar, asa ! r = Some ar /\ get_mem i ar = v.
  Proof.
    unfold arr_assocmap_lookup in *; intros.
    repeat (destruct_match; try discriminate). inv H.
    eexists; eauto.
  Qed.

  Lemma transl_predicate_correct_arr2 :
    forall asr asa a b p r e max_pred max_reg rs ps e1 v1 ar,
      Ple (max_predicate p) max_pred ->
      match_assocmaps max_reg max_pred rs ps asr ->
      eval_predf ps p = false ->
      expr_runp tt (assoc_blocking (e_assoc asr)) (assoc_blocking (e_assoc_arr a b asa)) e1 v1 ->
      arr_assocmap_lookup (assoc_blocking (e_assoc_arr a b asa)) r (valueToNat v1) = Some ar ->
      exists asa', stmnt_runp tt (e_assoc asr) (e_assoc_arr a b asa) (translate_predicate Vblock (Some p) (Vvari r e1) e) (e_assoc asr) (e_assoc_arr a b asa') 
      /\ (forall x a, asa ! x = Some a -> 
            exists a', asa' ! x = Some a'
            /\ (forall y, (y < arr_length a)%nat -> get_mem y a = get_mem y a')
            /\ (arr_length a = arr_length a')).
  Proof.
    intros * HPLE HMATCH HEVAL HEXPRRUN HLOOKUP. pose proof HEVAL as HEVAL_DEEP. 
    unfold translate_predicate. erewrite <- eval_predf_deep_simplify in HEVAL_DEEP.
    destruct_match.
    - econstructor; split.
      + econstructor; [econstructor|]; eauto. eapply erun_Vternary_false.
        * eapply pred_expr_correct. intros. eapply max_predicate_deep_simplify in H.
          inv HMATCH. eapply H1; unfold Ple in *. lia.
        * econstructor; eauto.
        * rewrite HEVAL_DEEP. auto.
      + intros. destruct (peq x r); subst.
        * erewrite arr_assocmap_set_gss by eauto.
          eexists; repeat split; eauto; intros.
          destruct (Nat.eq_dec y (valueToNat v1)); subst.
          -- rewrite get_mem_set_array_gss by auto. 
             exploit arr_assocmap_lookup_get_mem; eauto. intros (ar' & HASSOC & HGET).
             unfold e_assoc_arr in HASSOC. cbn in *. rewrite HASSOC in H. inv H. auto.
          -- now rewrite get_mem_set_array_gso by auto.
        * erewrite arr_assocmap_set_gso by eauto. unfold e_assoc_arr; cbn. eexists; split; eauto.
   - unfold sat_pred_simple in Heqo. repeat (destruct_match; try discriminate).
     apply negb_inj' in HEVAL_DEEP. unfold eval_predf in *. rewrite <- negate_correct in HEVAL_DEEP.
     now rewrite e0 in HEVAL_DEEP.
  Qed.

  Definition unchanged (asr : assocmap) asa asr' asa' :=
    (forall x, asr ! x = asr' ! x)
    /\ (forall x a, asa ! x = Some a -> 
          exists a', asa' ! x = Some a'
          /\ (forall y, (y < arr_length a)%nat -> get_mem y a = get_mem y a')
          /\ arr_length a = arr_length a').

  Lemma unchanged_refl :
    forall a b, unchanged a b a b.
  Proof.
    unfold unchanged; split; intros. eauto.
    eexists; eauto.
  Qed.

  Lemma unchanged_trans :
    forall a b a' b' a'' b'', unchanged a b a' b' -> unchanged a' b' a'' b'' -> unchanged a b a'' b''.
  Proof.
    unfold unchanged; simplify; intros.
    congruence.
    pose proof H as H'. apply H3 in H'. simplify. pose proof H5 as H5'.
    apply H2 in H5'. simplify. eexists; eauto; simplify; eauto; try congruence.
    intros. rewrite H4 by auto. now rewrite <- H6 by lia.
  Qed.

  Lemma transl_step_state_correct_single_instr :
    forall s f sp pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n i,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) i = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) i
             (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc rs' pr' m') (DHTL.State s' m_ pc asr' asa')
        /\ eval_predf pr' next_p = true.
  Proof. Admitted.

  Lemma transl_step_state_correct_single_instr_term :
    forall s f sp pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n i cf pc',
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) i = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) i
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.State s f sp pc' rs' pr' m') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc' rs' pr' m') (DHTL.State s' m_ pc' asr' asa')
        /\ eval_predf pr' next_p = false.
  Proof. Admitted.

  Lemma transl_step_state_correct_single_instr_term_return :
    forall s f sp pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n i cf v m'',
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) i = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      step_instr ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) i
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.Returnstate s v m'') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists retval,
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc (AssocMap.set m_.(DHTL.mod_st) (posToValue n) (AssocMap.set (m_.(DHTL.mod_return)) retval (AssocMap.set (m_.(DHTL.mod_finish)) (ZToValue 1) asr)))) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa)
        /\ val_value_lessdef v retval
        /\ eval_predf pr' next_p = false.
  Proof. Admitted.

  #[local] Ltac destr := destruct_match; try discriminate; [].

  Lemma pred_in_pred_uses:
    forall A (p: A) pop,
      PredIn p pop ->
      In p (predicate_use pop).
  Proof.
    induction pop; crush.
    - destr. inv Heqp1. inv H. now constructor.
    - inv H.
    - inv H.
    - apply in_or_app. inv H. inv H1; intuition.
    - apply in_or_app. inv H. inv H1; intuition.
  Qed.

  Lemma le_max_pred :
    forall p max_pred,
      Forall (fun x : positive => Ple x max_pred) (predicate_use p) ->
      Ple (max_predicate p) max_pred.
  Proof.
    induction p; intros.
    - intros; cbn. destruct_match. inv Heqp0. cbn in *. now inv H.
    - cbn. unfold Ple. lia.
    - cbn. unfold Ple. lia.
    - cbn in *. eapply Forall_app in H. inv H. unfold Ple in *. eapply IHp1 in H0.
      eapply IHp2 in H1. lia.
    - cbn in *. eapply Forall_app in H. inv H. unfold Ple in *. eapply IHp1 in H0.
      eapply IHp2 in H1. lia.
  Qed.

  (* Lemma storev_stack_bounds : *)
  (*   forall m sp v dst m' hi, *)
  (*     Mem.storev Mint32 m (Values.Vptr sp (Ptrofs.repr v)) dst = Some m' -> *)
  (*     stack_bounds (Values.Vptr sp (Ptrofs.repr 0)) hi m -> *)
  (*     v mod 4 = 0 -> *)
  (*     0 <= v < hi. *)
  (* Proof. *)
  (*   intros. unfold stack_bounds in *. *)
  (*   assert (0 <= v < hi \/ hi <= ) *)

  Ltac tac :=
    repeat match goal with
           | [ _ : error _ _ = OK _ _ _ |- _ ] => discriminate
           | [ _ : context[if (?x && ?y) then _ else _] |- _ ] =>
             let EQ1 := fresh "EQ" in
             let EQ2 := fresh "EQ" in
             destruct x eqn:EQ1; destruct y eqn:EQ2; simpl in *
           | [ _ : context[if ?x then _ else _] |- _ ] =>
             let EQ := fresh "EQ" in
             destruct x eqn:EQ; simpl in *
           | [ H : ret _ _ = _  |- _ ] => inv H
           | [ _ : context[match ?x with | _ => _ end] |- _ ] => destruct x
           end.

  Ltac inv_arr_access :=
    match goal with
    | [ _ : translate_arr_access ?chunk ?addr ?args _ _ = OK ?c _ _ |- _] =>
      destruct c, chunk, addr, args; crush; tac; crush
    end.

  Lemma offset_expr_ok :
    forall v z, (Z.to_nat
                   (Integers.Ptrofs.unsigned
                      (Integers.Ptrofs.divu
                         (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ v))
                                              (Integers.Ptrofs.of_int (Integers.Int.repr z)))
                         (Integers.Ptrofs.repr 4)))
                 = valueToNat (Int.divu (Int.add v (ZToValue z)) (ZToValue 4))).
  Proof.
    simplify_val. unfold valueToNat. unfold Int.divu, Ptrofs.divu.
    pose proof Integers.Ptrofs.agree32_add as AGR.
    unfold Integers.Ptrofs.agree32 in AGR.
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (Int.unsigned v))
                                        (Ptrofs.repr (Int.unsigned (Int.repr z)))) =
            Int.unsigned (Int.add v (ZToValue z))).
    apply AGR; auto.
    apply Ptrofs.unsigned_repr. apply Int.unsigned_range_2.
    apply Ptrofs.unsigned_repr. apply Int.unsigned_range_2.
    rewrite H. replace (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
    replace (Int.unsigned (ZToValue 4)) with 4.
    pose proof Ptrofs.agree32_repr. unfold Ptrofs.agree32 in *.
    rewrite H0. trivial. auto.
    unfold ZToValue. symmetry. apply Int.unsigned_repr.
    unfold_constants. lia.
    unfold ZToValue. symmetry. apply Int.unsigned_repr.
    unfold_constants. lia.
  Qed.

  Lemma offset_expr_ok_2 :
    forall v0 v1 z0 z1,
      (Z.to_nat
         (Integers.Ptrofs.unsigned
            (Integers.Ptrofs.divu
               (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ v0))
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add
                                          (Integers.Int.mul (valueToInt v1) (Integers.Int.repr z1))
                                          (Integers.Int.repr z0)))) (Ptrofs.repr 4))))
      = valueToNat (Int.divu (Int.add (Int.add v0 (ZToValue z0))
                                      (Int.mul v1 (ZToValue z1))) (ZToValue 4)).
    intros. unfold ZToValue, valueToNat, valueToInt, Ptrofs.divu, Int.divu, Ptrofs.of_int.

    assert (H : (Ptrofs.unsigned
             (Ptrofs.add (Ptrofs.repr (uvalueToZ v0))
                (Ptrofs.of_int (Int.add (Int.mul (valueToInt v1) (Int.repr z1)) (Int.repr z0)))) /
           Ptrofs.unsigned (Ptrofs.repr 4))
                = (Int.unsigned (Int.add (Int.add v0 (Int.repr z0)) (Int.mul v1 (Int.repr z1))) /
           Int.unsigned (Int.repr 4))).
    { unfold ZToValue, valueToNat, valueToInt, Ptrofs.divu, Int.divu, Ptrofs.of_int.
      rewrite Ptrofs.unsigned_repr by (unfold_constants; lia).
      rewrite Int.unsigned_repr by (unfold_constants; lia).

      unfold Ptrofs.of_int. rewrite Int.add_commut.
      pose proof Integers.Ptrofs.agree32_add as AGR. unfold Ptrofs.agree32 in *.
      erewrite AGR.
      3: { unfold uvalueToZ. rewrite Ptrofs.unsigned_repr. trivial. apply Int.unsigned_range_2. }
      3: { rewrite Ptrofs.unsigned_repr. trivial. apply Int.unsigned_range_2. }
      rewrite Int.add_assoc. trivial. auto.
    }

    rewrite <- H. auto.

  Qed.

  Lemma offset_expr_ok_3 :
    forall OFFSET,
      Z.to_nat (Ptrofs.unsigned (Ptrofs.divu OFFSET (Ptrofs.repr 4)))
      = valueToNat (ZToValue (Ptrofs.unsigned OFFSET / 4)).
  Proof. auto. Qed.

  Lemma storev_mod_ok' :
    forall m sp' ptr src m',
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.storev Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) src = Some m' ->
      ptr mod 4 = 0.
  Proof.
    unfold Mem.storev; intros * BOUND **. repeat destruct_match; try discriminate.
    eapply Mem.store_valid_access_3 in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    inv Heqv. rewrite Ptrofs.add_unsigned in H1.
    rewrite ! Ptrofs.unsigned_repr in H1; try lia. auto.
    rewrite ! Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma loadv_mod_ok' :
    forall m sp' ptr v,
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.loadv Mint32 m (Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) (Ptrofs.repr ptr)) = Some v ->
      ptr mod 4 = 0.
  Proof.
    unfold Mem.loadv; intros * BOUND **. repeat destruct_match; try discriminate.
    eapply Mem.load_valid_access in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    inv Heqv0. rewrite Ptrofs.add_unsigned in H1.
    rewrite ! Ptrofs.unsigned_repr in H1; try lia. auto.
    rewrite ! Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma offset_ptr_equiv :
    forall sp' v,
      Values.Val.offset_ptr (Values.Vptr sp' (Ptrofs.repr 0)) v = Values.Vptr sp' v.
  Proof.
    unfold Values.Val.offset_ptr; intros.
    replace (Ptrofs.repr 0) with Ptrofs.zero by auto.
    now rewrite Ptrofs.add_zero_l.
  Qed.

  Lemma loadv_mod_ok :
    forall m sp' ptr v,
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.loadv Mint32 m (Values.Vptr sp' (Ptrofs.repr ptr)) = Some v ->
      ptr mod 4 = 0.
  Proof.
    intros. eapply loadv_mod_ok'; eauto.
    rewrite offset_ptr_equiv; eauto.
  Qed.

  Lemma storev_mod_ok :
    forall m sp' ptr src m',
      0 <= ptr <= Ptrofs.max_unsigned ->
      Mem.storev Mint32 m (Values.Vptr sp' (Ptrofs.repr ptr)) src = Some m' ->
      ptr mod 4 = 0.
  Proof.
    intros. eapply storev_mod_ok'; eauto.
    rewrite offset_ptr_equiv; eauto.
  Qed.

  Lemma loadv_mod_ok2 :
    forall m sp' v v',
      Mem.loadv Mint32 m (Values.Vptr sp' v) = Some v' ->
      (Ptrofs.unsigned v) mod 4 = 0.
  Proof.
    unfold Mem.loadv; intros. repeat destruct_match; try discriminate.
    eapply Mem.load_valid_access in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    auto.
  Qed.

  Lemma storev_mod_ok2 :
    forall m sp' src m' v,
      Mem.storev Mint32 m (Values.Vptr sp' v) src = Some m' ->
      (Ptrofs.unsigned v) mod 4 = 0.
  Proof.
    unfold Mem.storev; intros. repeat destruct_match; try discriminate.
    eapply Mem.store_valid_access_3 in H.
    unfold Mem.valid_access in H. inv H. apply Zdivide_mod. cbn -[Ptrofs.max_unsigned]in *.
    auto.
  Qed.

  Lemma storev_exists_ptr:
    forall m v src m',
      Mem.storev Mint32 m v src = Some m' ->
      exists sp v', v = Values.Vptr sp v'.
  Proof.
    intros.
    unfold Mem.storev in *. destruct_match; try discriminate.
    subst. eauto.
  Qed.

  Lemma val_add_stack_based :
    forall v1 v2 sp,
      stack_based v1 sp ->
      stack_based v2 sp ->
      stack_based (Values.Val.add v1 v2) sp.
  Proof.
    intros. destruct v1, v2; auto.
    inv H. inv H0. cbn; auto.
  Qed.

  Lemma ptrofs_unsigned_add_0:
    forall x0,
      Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr (Ptrofs.unsigned x0))) = Ptrofs.unsigned x0.
  Proof.
    intros. replace (Ptrofs.repr 0) with (Ptrofs.zero) by auto.
    rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_repr; auto.
    apply Ptrofs.unsigned_range_2.
  Qed.

  Lemma exists_ptr_add_int :
    forall a b sp' x0,
      Values.Val.add a (Values.Vint b) = Values.Vptr sp' x0 ->
      exists a', a = Values.Vptr sp' a'.
  Proof.
    intros. destruct a; eauto; cbn in *; try discriminate.
    assert (Xx: Archi.ptr64 = false) by auto. rewrite Xx in H. inv H. eauto.
  Qed.

  Lemma transl_arr_access_correct :
    forall addr args e rs ps m sp a chnk src m' s f pc s' m_ asr arr,
      translate_arr_access chnk addr args m_.(DHTL.mod_stk) = OK e ->
      Op.eval_addressing ge sp addr (List.map (fun r => Registers.Regmap.get r rs) args) = Some a ->
      Mem.storev chnk m a (Registers.Regmap.get src rs) = Some m' ->
      match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr arr) ->
      exists x, expr_runp tt asr arr e x.
  Proof.
    assert (HARCH: Archi.ptr64 = false) by auto.
    intros. unfold translate_arr_access in *. repeat destr.
    destruct_match; try discriminate; repeat destr.
    - inv H. cbn in *. unfold Op.eval_addressing in *. rewrite HARCH in H0.
      cbn in *. inv H0. inv H2. unfold stack_bounds in *.
      exploit storev_exists_ptr; eauto. simplify.
      assert (stack_based (Values.Vint (Int.repr z)) sp') by (cbn; auto).
      assert (stack_based (rs !! r) sp') by (cbn; auto).
      eapply val_add_stack_based in H0; eauto. rewrite H in H0. cbn in *. inv H0.
      rewrite H in H1. exploit storev_mod_ok2; eauto; intros.
      specialize (BOUNDS (Ptrofs.unsigned x0) rs !! src).
      pose proof (ptrofs_unsigned_lt_int_max x0).
      assert (0 <= Ptrofs.unsigned x0 < fn_stacksize f \/ fn_stacksize f <= Ptrofs.unsigned x0 <= Int.max_unsigned) by lia.
      inv H4.
      + inv MARR. inv H4. eexists. econstructor. econstructor. econstructor. econstructor.
        eauto. econstructor. cbn. eauto. econstructor. cbn. unfold ZToValue.
        unfold Int.zero. unfold Int.eq. rewrite ! Int.unsigned_repr by crush.
        cbn. eauto. (* exploit exists_ptr_add_int; eauto. intros (a & HPTR). *)
        (* rewrite HPTR in H. cbn in H. *)
        assert (HARCHI: Archi.ptr64 = false) by auto.
        unfold arr_assocmap_lookup. setoid_rewrite H6. eauto.
      + apply BOUNDS in H5; auto. inv H5. rewrite ptrofs_unsigned_add_0 in H6.
        unfold Mem.storev in H1. rewrite H6 in H1. discriminate.
    - inv H. inv H2. inv MARR. inv H. repeat econstructor. unfold arr_assocmap_lookup.
      setoid_rewrite H2. auto.
    - inv H. inv H2. inv MARR. inv H. repeat econstructor. unfold arr_assocmap_lookup.
      setoid_rewrite H2. auto.
  Qed.

  Lemma transl_step_state_correct_single_false_standard :
    forall f bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n max_reg max_pred rs ps sp m o,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) bb = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun x => Ple x max_pred) (pred_uses bb) ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      step_instr ge sp (Iexec (mk_instr_state rs ps m)) bb o ->
      (forall a b c d e, bb <> RBstore a b c d e) ->
      (forall a b, bb <> RBexit a b) ->
      exists asr' asa', stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
        (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') 
        /\ unchanged asr asa asr' asa'
        /\ Ple (max_predicate next_p) max_pred 
        /\ eval_predf ps next_p = false.
  Proof.
    destruct bb; intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH HSTEP_INSTR HNO_RBSTORE HNO_EXIT.
    - cbn in HTRANSF. inv HTRANSF. exists asr, asa; repeat split; eauto.
    - cbn -[translate_predicate deep_simplify] in HTRANSF; unfold Errors.bind in HTRANSF.
      destruct_match; try discriminate.
      assert (forall A a b, @OK A a = OK b -> a = b) by now inversion 1. apply H in HTRANSF.
      assert (forall A B (a b: A) (c d: B), (a, c) = (b, d) -> a = b /\ c = d) by now inversion 1. 
      apply H0 in HTRANSF. destruct HTRANSF. rewrite H1 in *. rewrite <- H2 in *.
      assert (eval_predf ps (Pand next_p (dfltp o)) = false).
      { rewrite eval_predf_Pand. subst. rewrite HEVAL. auto. }
      assert (Ple (max_predicate (Pand next_p (dfltp o))) max_pred).
      { cbn. cbn in HFRL. destruct o; cbn; [|unfold Ple in *; lia].
        eapply le_max_pred in HFRL. unfold Ple in *; lia. }
      exploit transl_predicate_correct2; eauto. intros (asr' & HSTMNT' & FRL).
      exists asr', asa. repeat split; eauto.
      econstructor; eauto.
    - cbn -[translate_predicate deep_simplify] in HTRANSF; unfold Errors.bind in HTRANSF.
      destruct_match; try discriminate.
      assert (forall A a b, @OK A a = OK b -> a = b) by now inversion 1. apply H in HTRANSF.
      assert (forall A B (a b: A) (c d: B), (a, c) = (b, d) -> a = b /\ c = d) by now inversion 1. 
      apply H0 in HTRANSF. destruct HTRANSF. rewrite H1 in *. rewrite <- H2 in *.
      assert (eval_predf ps (Pand next_p (dfltp o)) = false).
      { rewrite eval_predf_Pand. subst. rewrite HEVAL. auto. }
      assert (Ple (max_predicate (Pand next_p (dfltp o))) max_pred).
      { cbn. cbn in HFRL. destruct o; cbn; [|unfold Ple in *; lia].
        eapply le_max_pred in HFRL. unfold Ple in *; lia. }
      exploit transl_predicate_correct2; eauto. intros (asr' & HSTMNT' & FRL).
      exists asr', asa. repeat split; eauto.
      econstructor; eauto.
    - exfalso; eapply HNO_RBSTORE; auto.
    - cbn -[translate_predicate deep_simplify] in HTRANSF; unfold Errors.bind in HTRANSF.
      destruct_match; try discriminate.
      assert (forall A a b, @OK A a = OK b -> a = b) by now inversion 1. apply H in HTRANSF.
      assert (forall A B (a b: A) (c d: B), (a, c) = (b, d) -> a = b /\ c = d) by now inversion 1. 
      apply H0 in HTRANSF. destruct HTRANSF. rewrite H1 in *. rewrite <- H2 in *.
      assert (eval_predf ps (Pand next_p (dfltp o)) = false).
      { rewrite eval_predf_Pand. subst. rewrite HEVAL. auto. }
      assert (Ple (max_predicate (Pand next_p (dfltp o))) max_pred).
      { cbn. cbn in HFRL. destruct o; cbn; [|unfold Ple in *; lia]. inv HFRL.
        eapply le_max_pred in H7. unfold Ple in *; lia. }
      exploit transl_predicate_correct2; eauto. intros (asr' & HSTMNT' & FRL).
      exists asr', asa. repeat split; eauto.
      econstructor; eauto.
    - exfalso; eapply HNO_EXIT; auto.
  Qed.

  Lemma unchanged_implies_match :
    forall s f sp rs ps m s' m_ pc asr' asa' asa asr,
      unchanged asr' asa' asr asa ->
      match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr' asa') ->
      match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr asa).
  Proof.
    intros. inv H. inv H0.
    econstructor; auto.
    - econstructor; intros; inv MASSOC; rewrite <- H1; eauto.
    - unfold state_st_wf in *. destruct 

  Lemma transl_step_state_correct_single_false_standard_top :
    forall f s s' pc bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n rs ps sp m o,
      (* (fn_code f) ! pc = Some bb -> *)
      transf_instr n (mk_ctrl f) (curr_p, stmnt) bb = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) 
        stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun x => Ple x (max_pred_function f)) (pred_uses bb) ->
      Ple (max_predicate curr_p) (max_pred_function f) ->
      eval_predf ps curr_p = false ->
      match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr asa) ->
      step_instr ge sp (Iexec (mk_instr_state rs ps m)) bb o ->
      exists asr' asa', 
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' 
          (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa') 
        /\ match_states (GibleSubPar.State s f sp pc rs ps m) (DHTL.State s' m_ pc asr' asa')
        /\ Ple (max_predicate next_p) (max_pred_function f)
        /\ eval_predf ps next_p = false.
  Proof.
    intros * HTRANSF HSTMNT HFRL HPLE HEVAL HMATCH HSTEP. destruct bb.
    - inv HMATCH.
      exploit transl_step_state_correct_single_false_standard; eauto; try discriminate.
      intros (asr' & asa' & HSTMNT' & HUNCHG & HPLE' & HEVAL').
      exists asr', asa'. repeat split; auto.

  Lemma iterm_intermediate_state :
    forall sp rs pr m bb rs' pr' m' cf,
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
               (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      exists bb' i bb'', 
        SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb'
               (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |})
        /\ step_instr ge sp (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) i (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf)
        /\ bb = bb' ++ (i :: bb'').
  Proof. Admitted.

  Lemma transl_step_state_correct_instr :
    forall s f sp bb pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa n,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iexec {| is_rs := rs'; is_ps := pr'; is_mem := m' |}) ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc rs' pr' m') (DHTL.State s' m_ pc asr' asa')
        /\ eval_predf pr' next_p = true.
  Proof. Admitted.

  Lemma transl_step_state_correct_instr_false :
    forall f bb curr_p next_p m_ stmnt stmnt' asr0 asa0 asr asa n max_reg max_pred rs ps,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      Forall (fun i => Forall (fun x : positive => Ple x max_pred) (pred_uses i)) bb ->
      Ple (max_predicate curr_p) max_pred ->
      eval_predf ps curr_p = false ->
      match_assocmaps max_reg max_pred rs ps asr ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa).
  Proof.
    induction bb.
    - cbn; inversion 2; auto.
    - intros * HFOLD HSTMNT HFRL HPLE HEVAL HMATCH. exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANS & HINV). inv HINV. destruct y'.
  (*     exploit transl_step_state_correct_single_false; eauto; intros. inv HFRL; eauto. *)
  (*     inv H. inv H1. *)
  (*     exploit IHbb; eauto. inv HFRL; eauto. *)
  (* Qed. *) Admitted.

  Lemma transl_step_state_correct_instr_state :
    forall s f sp bb pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa cf pc' n,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.State s f sp pc' rs' pr' m') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc' rs' pr' m') (DHTL.State s' m_ pc' asr' asa').
  Proof. 
    intros * HFOLD HSTMNT HEVAL HSTEP HSTEPCF HMATCH.
    exploit iterm_intermediate_state; eauto.
    intros (bb' & i & bb'' & HSTEP' & HSTEPINSTR & HBB). subst.
    exploit mfold_left_app; eauto. intros (y' & HFOLD1 & HFOLD2).
    exploit mfold_left_cons; eauto. intros (x' & y_other & HFOLDFINAL & HINSTR & HSUBST).
    inv HSUBST.
    destruct x'. destruct y_other.
    exploit transl_step_state_correct_instr; try eapply HFOLD1; eauto.
    intros (asr' & asa' & HSTMNT' & HMATCH' & HNEXT).
    exploit transl_step_state_correct_single_instr_term; eauto.
    intros (asr'0 & asa'0 & HSTMNT'' & HMATCH'' & HNEXT'').
    exploit transl_step_state_correct_instr_false; eauto.
  Admitted.

  Lemma transl_step_state_correct_instr_return :
    forall s f sp bb pc curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa cf v m'' n,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_instr n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step_instr_list ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.Returnstate s v m'') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists asr' asa' retval,
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ val_value_lessdef v retval
        /\ asr'!(m_.(DHTL.mod_finish)) = Some (ZToValue 1)
        /\ asr'!(m_.(DHTL.mod_return)) = Some retval
        /\ asr'!(m_.(DHTL.mod_st)) = Some (posToValue n).
  Proof.
    intros * HFOLD HSTMNT HEVAL HSTEP HSTEPCF HMATCH.
    exploit iterm_intermediate_state; eauto.
    intros (bb' & i & bb'' & HSTEP' & HSTEPINSTR & HBB). subst.
    exploit mfold_left_app; eauto. intros (y' & HFOLD1 & HFOLD2).
    exploit mfold_left_cons; eauto. intros (x' & y_other & HFOLDFINAL & HINSTR & HSUBST).
    inv HSUBST.
    destruct x'. destruct y_other.
    exploit transl_step_state_correct_instr; try eapply HFOLD1; eauto.
    intros (asr' & asa' & HSTMNT' & HMATCH' & HNEXT).
    exploit transl_step_state_correct_single_instr_term_return; eauto.
    intros (v' & HSTMNT'' & HEVAL2 & HEVAL3).
    exploit transl_step_state_correct_instr_false; eauto.
    intros.
    pose proof (mod_ordering_wf m_). unfold module_ordering in H0. inv H0. inv H2.
    eexists. exists asa'. exists v'.
    repeat split; eauto; repeat rewrite PTree.gso by lia; apply PTree.gss.
  Qed.

  Lemma transl_step_state_correct_chained_state :
    forall s f sp bb pc pc' curr_p next_p rs rs' m m' pr pr' m_ s' stmnt stmnt' asr0 asa0 asr asa cf n,
      (* (fn_code f) ! pc = Some bb -> *)
      mfold_left (transf_chained_block n (mk_ctrl f)) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt (e_assoc asr) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa) ->
      eval_predf pr curr_p = true ->
      SubParBB.step ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf Events.E0 (GibleSubPar.State s f sp pc' rs' pr' m') ->
      match_states (GibleSubPar.State s f sp pc rs pr m) (DHTL.State s' m_ pc asr asa) ->
      exists asr' asa',
        stmnt_runp tt (e_assoc asr0) (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa0) stmnt' (e_assoc asr') (e_assoc_arr (DHTL.mod_stk m_) (DHTL.mod_stk_len m_) asa')
        /\ match_states (GibleSubPar.State s f sp pc' rs' pr' m') (DHTL.State s' m_ pc' asr' asa').
  Proof. Abort.

  Lemma transl_step_through_cfi' :
    forall bb ctrl curr_p stmnt next_p stmnt' p cf n,
      mfold_left (transf_instr n ctrl) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      In (RBexit p cf) bb ->
      exists curr_p' stmnt'', translate_cfi n ctrl (Some (Pand curr_p' (dfltp p))) cf = OK stmnt'' /\ check_cfi n cf = OK tt.
  Proof.
    induction bb.
    - inversion 2.
    - intros * HFOLD HIN.
      exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANSF & HSUBST).
      inversion HSUBST. inv H0. clear HSUBST.
      inv HIN; destruct y'; eauto.
      cbn in HTRANSF. unfold Errors.bind in HTRANSF. repeat (destruct_match; try discriminate; []).
      inv HTRANSF. destruct u. eauto.
  Qed.

  Lemma transl_step_through_cfi :
    forall bb ctrl curr_p stmnt next_p stmnt' l p cf n,
      mfold_left (transf_chained_block n ctrl) bb (OK (curr_p, stmnt)) = OK (next_p, stmnt') ->
      In l bb ->
      In (RBexit p cf) l ->
      exists curr_p' stmnt'', translate_cfi n ctrl (Some (Pand curr_p' (dfltp p))) cf = OK stmnt''.
  Proof.
    induction bb.
    - inversion 2.
    - intros * HFOLD HIN1 HIN2.
      exploit mfold_left_cons; eauto.
      intros (x' & y' & HFOLD' & HTRANSF & HSUBST).
      destruct y'. inv HSUBST.
      inv HIN1; eauto.
      exploit transl_step_through_cfi'; eauto.
      simplify. eauto.
  Qed.

  Lemma cf_in_bb_subparbb' :
    forall sp bb a b cf,
      SubParBB.step_instr_list ge sp (Iexec a) bb (Iterm b cf) ->
      exists curr_p, In (RBexit curr_p cf) bb /\ truthy (is_ps b) curr_p.
  Proof.
    induction bb.
    - intros. inv H.
    - intros. inv H.
      destruct i1.
      + exploit IHbb; eauto. intros (curr_p & HIN & HTRY).
        exists curr_p. split; auto. now apply in_cons.
      + inv H4. exists p. inv H6; split; auto; now constructor.
  Qed.

  Lemma cf_in_bb_subparbb :
    forall sp bb a b cf,
      SubParBB.step_instr_seq ge sp (Iexec a) bb (Iterm b cf) ->
      exists l curr_p, In l bb /\ In (RBexit curr_p cf) l /\ truthy (is_ps b) curr_p.
  Proof.
    induction bb.
    - intros. inv H.
    - intros. inv H.
      + exploit IHbb; eauto. intros (l & curr_p & HIN2 & HIN & HTRY).
        exists l, curr_p. split; auto. now apply in_cons.
      + exploit cf_in_bb_subparbb'; eauto. 
        intros (curr_p & HIN & HTR).
        exists a, curr_p. split; auto. now constructor.
  Qed.

  Lemma match_states_cf_events_translate_cfi:
    forall T1 cf T2 p t ctrl stmnt n,
      translate_cfi n ctrl p cf = OK stmnt ->
      step_cf_instr ge T1 cf t T2 ->
      t = Events.E0.
  Proof.
    intros * HGET HSTEP.
    destruct cf; try discriminate; inv HSTEP; eauto.
  Qed.

  Lemma match_states_cf_states_translate_cfi:
    forall T1 cf T2 p t ctrl stmnt n,
      translate_cfi n ctrl p cf = OK stmnt ->
      step_cf_instr ge T1 cf t T2 ->
      exists s f sp pc rs pr m,
        T1 = GibleSubPar.State s f sp pc rs pr m
        /\ ((exists pc', T2 = GibleSubPar.State s f sp pc' rs pr m)
            \/ (exists v m' stk, Mem.free m stk 0 (fn_stacksize f) = Some m' /\ sp = Values.Vptr stk Ptrofs.zero /\ T2 = GibleSubPar.Returnstate s v m')).
  Proof.
    intros * HGET HSTEP.
    destruct cf; try discriminate; inv HSTEP; try (now repeat econstructor).
  Qed.

  Lemma translate_cfi_goto:
    forall pr curr_p pc s ctrl asr asa n,
      (forall r, Ple r (max_predicate curr_p) ->
        find_assocmap 1 (pred_enc r) asr = boolToValue (PMap.get r pr)) ->
      eval_predf pr curr_p = true ->
      translate_cfi n ctrl (Some curr_p) (RBgoto pc) = OK s ->
      stmnt_runp tt (e_assoc asr) asa s
        (e_assoc (AssocMap.set ctrl.(ctrl_st) (posToValue pc) asr)) asa.
  Proof.
    intros * HPLE HEVAL HTRANSL. unfold translate_cfi in *.
    inversion_clear HTRANSL as []. destruct_match.
    - constructor. constructor. econstructor. eapply pred_expr_correct.
      intros. unfold Ple in *. eapply HPLE.
      now apply max_predicate_deep_simplify in H.
      eauto. constructor. rewrite eval_predf_deep_simplify. rewrite HEVAL. auto.
    - repeat constructor.
  Qed.

  Lemma translate_cfi_goto_none:
    forall pc s ctrl asr asa n,
      translate_cfi n ctrl None (RBgoto pc) = OK s ->
      stmnt_runp tt (e_assoc asr) asa s
        (e_assoc (AssocMap.set ctrl.(ctrl_st) (posToValue pc) asr)) asa.
  Proof. intros; inversion_clear H as []; repeat constructor. Qed.

  Lemma transl_module_ram_none :
    forall f m_,
      transl_module f = OK m_ ->
      m_.(mod_ram) = None.
  Proof.
    unfold transl_module, Errors.bind, Errors.bind2, ret; intros.
    repeat (destruct_match; try discriminate). inversion_clear H as []. auto.
  Qed.

  Lemma match_states_ok_transl :
    forall s f sp pc rs pr mem R1,
      match_states (GibleSubPar.State s f sp pc rs pr mem) R1 ->
      exists m asr asa s', transl_module f = OK m /\ R1 = DHTL.State s' m pc asr asa.
  Proof. inversion 1; subst. now repeat eexists. Qed.

  Lemma transl_spec_in_output :
    forall l ctrl d_in d_out pc stmnt,
      mfold_left (transf_seq_block ctrl) l (OK d_in) = OK d_out ->
      d_in ! pc = Some stmnt ->
      d_out ! pc = Some stmnt.
  Proof.
    induction l; intros * HFOLD HIN.
    - cbn in *; now (inversion HFOLD; subst).
    - exploit mfold_left_cons; eauto. 
      intros (x' & y' & HFOLD_EXP & TRANSFSEQ & HINV). inv HINV.
      unfold transf_seq_block in TRANSFSEQ. repeat (destruct_match; try discriminate; []).
      destruct (peq pc n); subst.
      + now rewrite Heqo in HIN.
      + unfold Errors.bind2 in TRANSFSEQ. repeat (destruct_match; try discriminate; []).
        inv TRANSFSEQ. eapply IHl; eauto. now rewrite PTree.gso by auto.
  Qed.

  Lemma transl_spec_correct' :
    forall l ctrl d_in d_out pc bb,
      mfold_left (transf_seq_block ctrl) l (OK d_in) = OK d_out ->
      In (pc, bb) l ->
      exists n pred' stmnt, transf_chained_block n ctrl (Ptrue, Vskip) (concat bb) = OK (pred', stmnt)
        /\ d_out ! pc = Some stmnt.
  Proof.
    induction l; [now inversion 2|].
    cbn -[mfold_left]. intros * HFOLD HIN.
    exploit mfold_left_cons; eauto. 
    intros (x' & y' & HFOLD_EXP & TRANSFSEQ & HINV). inv HINV.
    inversion_clear HIN as [HIN' | HIN']; eauto.
    inversion HIN' as [HIN_CLEAR]; subst. clear HIN_CLEAR.
    unfold transf_seq_block, Errors.bind2 in TRANSFSEQ. 
    repeat (destruct_match; try discriminate; []).
    inversion TRANSFSEQ as []; subst. clear TRANSFSEQ.
    exploit transl_spec_in_output; eauto. now rewrite PTree.gss.
  Qed.

  Lemma transl_spec_correct :
    forall ctrl d_in d_out pc bb c,
      mfold_left (transf_seq_block ctrl) (PTree.elements c) (OK d_in) = OK d_out ->
      c ! pc = Some bb ->
      exists n pred' stmnt, transf_chained_block n ctrl (Ptrue, Vskip) (concat bb) = OK (pred', stmnt)
        /\ d_out ! pc = Some stmnt.
  Proof. intros. eapply transl_spec_correct'; eauto using PTree.elements_correct. Qed.

  Lemma lt_check_step_cf_instr :
    forall s f sp pc rs pr m cf t s' f' sp' x rs' pr' m' ctrl p st n,
      translate_cfi n ctrl p cf = OK st ->
      check_cfi n cf = OK tt ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs pr m) cf t
            (GibleSubPar.State s' f' sp' x rs' pr' m') ->
      Z.pos x <= Int.max_unsigned.
  Proof.
    intros.
    destruct cf; cbn in *; try discriminate; unfold check_cfi, assert_, Errors.bind in *; repeat (destruct_match; try discriminate); simplify; inv H1; try destruct_match; try lia.
    apply list_nth_z_in in H19.
    eapply forallb_forall in Heqb; eauto. lia.
  Qed.

  Lemma lt_check_step_cf_instr2 :
    forall cf n,
      check_cfi n cf = OK tt ->
      Z.pos n <= Int.max_unsigned.
  Proof.
    intros.
    destruct cf; cbn in *; try discriminate; unfold check_cfi, assert_, Errors.bind in *; repeat (destruct_match; try discriminate); simplify; try destruct_match; try lia.
  Qed.

  Lemma transl_step_state_correct :
    forall s f sp pc rs rs' m m' bb pr pr' state cf t,
      (fn_code f) ! pc = Some bb ->
      SubParBB.step ge sp (Iexec {| is_rs := rs; is_ps := pr; is_mem := m |}) bb
             (Iterm {| is_rs := rs'; is_ps := pr'; is_mem := m' |} cf) ->
      step_cf_instr ge (GibleSubPar.State s f sp pc rs' pr' m') cf t state ->
      forall R1 : DHTL.state,
        match_states (GibleSubPar.State s f sp pc rs pr m) R1 ->
        exists R2 : DHTL.state, Smallstep.plus DHTL.step tge R1 t R2 /\ match_states state R2.
  Proof.
    intros * HIN HSTEP HCF * HMATCH.
    exploit match_states_ok_transl; eauto.
    intros (m0 & asr & asa & s' & HTRANSL & ?). subst.
    unfold transl_module, Errors.bind, bind, ret in HTRANSL.
    repeat (destruct_match; try discriminate; []).
    exploit transl_spec_correct; eauto.
    intros (n & pred' & stmnt0 & HTRANSF & HGET).
    exploit step_exec_concat; eauto; intros HCONCAT.
    exploit cf_in_bb_subparbb'; eauto. intros (exit_p & HINEXIT & HTRUTHY).
    exploit transl_step_through_cfi'; eauto. intros (curr_p & _stmnt & HCFI & HCHECK).
    exploit match_states_cf_states_translate_cfi; eauto. intros (s0 & f1 & sp0 & pc0 & rs0 & pr0 & m2 & HPARSTATE & HEXISTS).
    exploit match_states_cf_events_translate_cfi; eauto; intros; subst.
    inv HEXISTS.
    - inv HPARSTATE. inv H. exploit transl_step_state_correct_instr_state; eauto.
      constructor. intros (asr' & asa' & HSTMNTRUN & HMATCH').
      do 2 apply match_states_merge_empty_all in HMATCH'.
      eexists. split; eauto. inv HMATCH. inv CONST.
      apply Smallstep.plus_one. econstructor; eauto.
      inv HTRANSL. auto. erewrite transl_module_ram_none by eauto. constructor.
      inv HMATCH'. unfold state_st_wf in WF0. auto.
      eapply lt_check_step_cf_instr; eauto.
    - inv HPARSTATE; simplify. exploit transl_step_state_correct_instr_return; eauto.
      constructor. intros (asr' & asa' & retval & HSTMNT_RUN & HVAL & HASR1 & HASR2 & HASR3).
      inv HMATCH. inv CONST.
      econstructor. split.
      eapply Smallstep.plus_two.
      econstructor.
      + eauto.
      + eauto.
      + eauto.
      + inv HTRANSL. eauto.
      + eauto.
      + erewrite transl_module_ram_none by eauto. constructor.
      + eauto.
      + eauto.
      + unfold merge_regs. rewrite AssocMapExt.merge_base_1. rewrite AssocMapExt.merge_base_1. eauto.
      + eapply lt_check_step_cf_instr2; eauto.
      + eapply DHTL.step_finish.
        * now do 2 rewrite AssocMapExt.merge_base_1.
        * do 2 rewrite AssocMapExt.merge_base_1; eauto.
      + auto.
      + constructor. auto. auto.
  Qed.

  Theorem transl_step_correct:
    forall (S1 : GibleSubPar.state) t S2,
      GibleSubPar.step ge S1 t S2 ->
      forall (R1 : DHTL.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus DHTL.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1.
    - now (eapply transl_step_state_correct; eauto).
    - now apply transl_callstate_correct.
    - inversion 1.
    - now apply transl_returnstate_correct.
  Qed.
  #[local] Hint Resolve transl_step_correct : htlproof.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (GibleSubPar.semantics prog) (DHTL.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus; eauto with htlproof.
    apply senv_preserved.
  Qed.

End CORRECTNESS.
