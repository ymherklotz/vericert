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
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.HTLPargen.
Require Import vericert.hls.HTLPargen.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require vericert.hls.Verilog.
Require Import vericert.common.Errormonad.
Import ErrorMonad.
Import ErrorMonadExtra.

Require Import Lia.

Local Open Scope assocmap.

#[local] Hint Resolve AssocMap.gss : htlproof.
#[local] Hint Resolve AssocMap.gso : htlproof.

#[local] Hint Unfold find_assocmap AssocMapExt.get_default : htlproof.

Inductive match_assocmaps : GiblePar.function -> Gible.regset -> assocmap -> Prop :=
  match_assocmap : forall f rs am,
    (forall r, Ple r (max_reg_function f) ->
               val_value_lessdef (Registers.Regmap.get r rs) am#r) ->
    match_assocmaps f rs am.
#[local] Hint Constructors match_assocmaps : htlproof.

Inductive match_arrs (m : DHTL.module) (f : GiblePar.function) (sp : Values.val) (mem : mem) :
  Verilog.assocmap_arr -> Prop :=
| match_arr : forall asa stack,
    asa ! (m.(DHTL.mod_stk)) = Some stack /\
    stack.(arr_length) = Z.to_nat (f.(GiblePar.fn_stacksize) / 4) /\
    (forall ptr,
        0 <= ptr < Z.of_nat m.(DHTL.mod_stk_len) ->
        opt_val_value_lessdef (Mem.loadv AST.Mint32 mem
                                         (Values.Val.offset_ptr sp (Ptrofs.repr (4 * ptr))))
                              (Option.default (NToValue 0)
                                 (Option.join (array_get_error (Z.to_nat ptr) stack)))) ->
    match_arrs m f sp mem asa.

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

Inductive match_frames : list GiblePar.stackframe -> list DHTL.stackframe -> Prop :=
| match_frames_nil :
    match_frames nil nil.

Inductive match_constants : DHTL.module -> assocmap -> Prop :=
  match_constant :
    forall m asr,
      asr!(DHTL.mod_reset m) = Some (ZToValue 0) ->
      asr!(DHTL.mod_finish m) = Some (ZToValue 0) ->
      match_constants m asr.

Definition state_st_wf (m : DHTL.module) (s : DHTL.state) :=
  forall st asa asr res,
  s = DHTL.State res m st asa asr ->
  asa!(m.(DHTL.mod_st)) = Some (posToValue st).
#[local] Hint Unfold state_st_wf : htlproof.

Inductive match_states : GiblePar.state -> DHTL.state -> Prop :=
| match_state : forall asa asr sf f sp sp' rs mem m st res ps
    (MASSOC : match_assocmaps f rs asr)
    (TF : transl_module f = Errors.OK m)
    (WF : state_st_wf m (DHTL.State res m st asr asa))
    (MF : match_frames sf res)
    (MARR : match_arrs m f sp mem asa)
    (SP : sp = Values.Vptr sp' (Ptrofs.repr 0))
    (RSBP : reg_stack_based_pointers sp' rs)
    (ASBP : arr_stack_based_pointers sp' mem (f.(GiblePar.fn_stacksize)) sp)
    (BOUNDS : stack_bounds sp (f.(GiblePar.fn_stacksize)) mem)
    (CONST : match_constants m asr),
    (* Add a relation about ps compared with the state register. *)
    match_states (GiblePar.State sf f sp st rs ps mem)
                 (DHTL.State res m st asr asa)
| match_returnstate :
    forall
      v v' stack mem res
      (MF : match_frames stack res),
      val_value_lessdef v v' ->
      match_states (GiblePar.Returnstate stack v mem) (DHTL.Returnstate res v')
| match_initial_call :
    forall f m m0
    (TF : transl_module f = Errors.OK m),
      match_states (GiblePar.Callstate nil (AST.Internal f) nil m0) (DHTL.Callstate nil m nil).
#[local] Hint Constructors match_states : htlproof.

Definition match_prog (p: GiblePar.program) (tp: DHTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp /\
  main_is_internal p = true.

Ltac unfold_match H :=
  match type of H with
  | context[match ?g with _ => _ end] => destruct g eqn:?; try discriminate
  end.

#[global] Instance TransfHTLLink (tr_fun: GiblePar.program -> Errors.res DHTL.program):
  TransfLink (fun (p1: GiblePar.program) (p2: DHTL.program) => match_prog p1 p2).
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

Definition match_prog' (p: GiblePar.program) (tp: DHTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Lemma match_prog_matches :
  forall p tp, match_prog p tp -> match_prog' p tp.
Proof. unfold match_prog. tauto. Qed.

Lemma transf_program_match:
  forall p tp, HTLPargen.transl_program p = Errors.OK tp -> match_prog p tp.
Proof.
  intros. unfold transl_program in H.
  destruct (main_is_internal p) eqn:?; try discriminate.
  unfold match_prog. split.
  apply Linking.match_transform_partial_program; auto.
  assumption.
Qed.

Lemma regs_lessdef_add_greater :
  forall f rs1 rs2 n v,
    Plt (max_reg_function f) n ->
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
#[local] Hint Resolve regs_lessdef_add_greater : htlproof.

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
  forall f l,
    match_assocmaps f (Gible.init_regs nil l) (DHTL.init_regs nil l).
Proof.
  induction l; simpl; constructor; intros.
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

  Variable prog : GiblePar.program.
  Variable tprog : DHTL.program.

  Hypothesis TRANSL : match_prog prog tprog.

  Lemma TRANSL' :
    Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.
  Proof. intros; apply match_prog_matches; assumption. Qed.

  Let ge : GiblePar.genv := Globalenvs.Genv.globalenv prog.
  Let tge : DHTL.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. intros. eapply (Genv.find_symbol_match TRANSL'). Qed.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: GiblePar.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL'); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: GiblePar.fundef),
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
      match_states (GiblePar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
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
      match_states (GiblePar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
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
      match_states (GiblePar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
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
    inversion H1. clear H1.
    assert (Int.unsigned n <= 30).
    { unfold Int.ltu in *. destruct (zlt (Int.unsigned n) (Int.unsigned (Int.repr 31))); try discriminate.
      rewrite Int.unsigned_repr in l by (simplify; lia).
      replace 31 with (Z.succ 30) in l by auto.
      apply Zlt_succ_le in l.
      auto.
    }
    rewrite IntExtra.shrx_shrx_alt_equiv in H2 by auto.
    unfold IntExtra.shrx_alt in *.
    destruct (zlt (Int.signed i) 0).
    - repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
      repeat (simplify; eval_correct_tac).
      unfold valueToInt in *. inv INSTR. apply H in H4. rewrite H3 in H4.
      inv H4. clear H5.
      unfold Int.lt in *. rewrite zlt_true in Heqb0. simplify.
      rewrite Int.unsigned_repr in Heqb0. discriminate.
      simplify; lia.
      unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
      auto.
      rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_true; try lia.
      simplify. inv INSTR. clear H5.  apply H in H4. rewrite H3 in H4. inv H4. auto.
    - econstructor; econstructor; [eapply Verilog.erun_Vternary_false|idtac]; repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
      repeat (simplify; eval_correct_tac).
      inv INSTR. clear H5. apply H in H4. rewrite H3 in H4.
      inv H4.
      unfold Int.lt in *. rewrite zlt_false in Heqb0. simplify.
      rewrite Int.unsigned_repr in Heqb0. lia.
      simplify; lia.
      unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
      auto.
      rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_false; try lia.
      simplify. inv INSTR. apply H in H4. unfold valueToInt in *. rewrite H3 in H4. inv H4. auto.
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
      match_states (GiblePar.State stk f sp pc rs pr m) (DHTL.State res ml st asr asa) ->
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
    - inv H1. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - inv H1. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - inv H1. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
      do 2 econstructor; eauto. repeat econstructor. unfold binop_run.
      rewrite Heqb. auto. constructor; auto.
    - inv H1. rewrite Heqv0 in HPLE. inv HPLE. rewrite Heqv1 in HPLE0. inv HPLE0. unfold valueToInt in *.
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
    - inv H1. rewrite Heqv0 in HPLE. inv HPLE. 
      assert (0 <= 31 <= Int.max_unsigned). 
      { pose proof Int.two_wordsize_max_unsigned as Y. 
        unfold Int.zwordsize, Int.wordsize, Wordsize_32.wordsize in Y. lia. }
      assert (Int.unsigned n <= 30).
      { unfold Int.ltu in Heqb. destruct_match; try discriminate.
        clear Heqs. rewrite Int.unsigned_repr in l by auto. lia. }
      rewrite IntExtra.shrx_shrx_alt_equiv by auto.
      case_eq (Int.lt (asr # p) (ZToValue 0)); intros HLT.
      + assert ((if zlt (Int.signed (valueToInt asr # p)) 0 then true else false) = true).
        { destruct_match; auto; unfold valueToInt in *. exfalso.
          assert (Int.signed asr # p < 0 -> False) by auto. apply H2. unfold Int.lt in HLT.
          destruct_match; try discriminate. auto. }
        destruct_match; try discriminate.
        do 2 econstructor; eauto. repeat econstructor. now rewrite HLT.
        constructor; cbn. unfold IntExtra.shrx_alt. rewrite Heqs. auto.
      + assert ((if zlt (Int.signed (valueToInt asr # p)) 0 then true else false) = false).
        { destruct_match; auto; unfold valueToInt in *. exfalso.
          assert (Int.signed asr # p >= 0 -> False) by auto. apply H2. unfold Int.lt in HLT.
          destruct_match; try discriminate. auto. }
        destruct_match; try discriminate.
        do 2 econstructor; eauto. eapply erun_Vternary_false; repeat econstructor. 
        now rewrite HLT.
        constructor; cbn. unfold IntExtra.shrx_alt. rewrite Heqs. auto.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shru.
    - do 2 econstructor; eauto. repeat econstructor. now apply eval_correct_shru'.
    - unfold translate_eff_addressing in H1. 
      repeat (destruct_match; try discriminate); unfold boplitz in *; simplify;
          repeat (apply Forall_cons_iff in INSTR; destruct INSTR as (?HPLE & INSTR));
      try (apply H in HPLE); try (apply H in HPLE0).
      + inv H1. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        now apply eval_correct_add'.
      + inv H1. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        apply eval_correct_add; auto. apply eval_correct_add; auto.
        constructor; auto.
      + inv H1. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        apply eval_correct_add; try constructor; auto. 
        apply eval_correct_mul; try constructor; auto. 
      + inv H1. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        apply eval_correct_add; try constructor; auto.
        apply eval_correct_add; try constructor; auto. 
        apply eval_correct_mul; try constructor; auto. 
      + inv H1. do 2 econstructor; eauto. repeat econstructor. unfold ZToValue.
        assert (X: Archi.ptr64 = false) by auto.
        rewrite X in H2. inv H2.
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
      unfold Errors.bind in *. destruct_match; try discriminate; []. inv H1.
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
