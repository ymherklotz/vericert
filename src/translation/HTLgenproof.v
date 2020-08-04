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

From compcert Require RTL Registers AST.
From compcert Require Import Integers Globalenvs Memory Linking.
From vericert Require Import Vericertlib HTLgenspec HTLgen ValueInt AssocMap Array IntegerExtra ZExtra.
From vericert Require HTL Verilog.

Require Import Lia.

Local Open Scope assocmap.

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
  forall st asa asr res,
  s = HTL.State res m st asa asr ->
  asa!(m.(HTL.mod_st)) = Some (posToValue st).
Hint Unfold state_st_wf : htlproof.

Inductive match_arrs (m : HTL.module) (f : RTL.function) (sp : Values.val) (mem : mem) :
  Verilog.assocmap_arr -> Prop :=
| match_arr : forall asa stack,
    asa ! (m.(HTL.mod_stk)) = Some stack /\
    stack.(arr_length) = Z.to_nat (f.(RTL.fn_stacksize) / 4) /\
    (forall ptr,
        0 <= ptr < Z.of_nat m.(HTL.mod_stk_len) ->
        opt_val_value_lessdef (Mem.loadv AST.Mint32 mem
                                         (Values.Val.offset_ptr sp (Integers.Ptrofs.repr (4 * ptr))))
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
                              (Values.Val.offset_ptr sp (Integers.Ptrofs.repr (4 * ptr)))))
                spb.

Definition stack_bounds (sp : Values.val) (hi : Z) (m : mem) : Prop :=
  forall ptr v,
    hi <= ptr <= Integers.Ptrofs.max_unsigned ->
    Z.modulo ptr 4 = 0 ->
    Mem.loadv AST.Mint32 m (Values.Val.offset_ptr sp (Integers.Ptrofs.repr ptr )) = None /\
    Mem.storev AST.Mint32 m (Values.Val.offset_ptr sp (Integers.Ptrofs.repr ptr )) v = None.

Inductive match_frames : list RTL.stackframe -> list HTL.stackframe -> Prop :=
| match_frames_nil :
    match_frames nil nil.

Inductive match_constants : HTL.module -> assocmap -> Prop :=
  match_constant :
    forall m asr,
      asr!(HTL.mod_reset m) = Some (ZToValue 0) ->
      asr!(HTL.mod_finish m) = Some (ZToValue 0) ->
      match_constants m asr.

Inductive match_states : RTL.state -> HTL.state -> Prop :=
| match_state : forall asa asr sf f sp sp' rs mem m st res
    (MASSOC : match_assocmaps f rs asr)
    (TF : tr_module f m)
    (WF : state_st_wf m (HTL.State res m st asr asa))
    (MF : match_frames sf res)
    (MARR : match_arrs m f sp mem asa)
    (SP : sp = Values.Vptr sp' (Integers.Ptrofs.repr 0))
    (RSBP : reg_stack_based_pointers sp' rs)
    (ASBP : arr_stack_based_pointers sp' mem (f.(RTL.fn_stacksize)) sp)
    (BOUNDS : stack_bounds sp (f.(RTL.fn_stacksize)) mem)
    (CONST : match_constants m asr),
    match_states (RTL.State sf f sp st rs mem)
                 (HTL.State res m st asr asa)
| match_returnstate :
    forall
      v v' stack mem res
      (MF : match_frames stack res),
      val_value_lessdef v v' ->
      match_states (RTL.Returnstate stack v mem) (HTL.Returnstate res v')
| match_initial_call :
    forall f m m0
    (TF : tr_module f m),
      match_states (RTL.Callstate nil (AST.Internal f) nil m0) (HTL.Callstate nil m nil).
Hint Constructors match_states : htlproof.

Definition match_prog (p: RTL.program) (tp: HTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp /\
  main_is_internal p = true.

Instance TransfHTLLink (tr_fun: RTL.program -> Errors.res HTL.program):
  TransfLink (fun (p1: RTL.program) (p2: HTL.program) => match_prog p1 p2).
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

Definition match_prog' (p: RTL.program) (tp: HTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Lemma match_prog_matches :
  forall p tp, match_prog p tp -> match_prog' p tp.
Proof. unfold match_prog. tauto. Qed.

Lemma transf_program_match:
  forall p tp, HTLgen.transl_program p = Errors.OK tp -> match_prog p tp.
Proof.
  intros. unfold transl_program in H.
  destruct (main_is_internal p) eqn:?; try discriminate.
  unfold match_prog. split.
  apply Linking.match_transform_partial_program; auto.
  assumption.
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
  simpl in H. invert H.
  destruct n; simpl in *.
  invert H0. simpl. reflexivity.
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
  simpl in H. invert H.
  destruct n; simpl in *.
  invert H0. simpl. reflexivity.
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

Ltac inv_state :=
  match goal with
    MSTATE : match_states _ _ |- _ =>
    inversion MSTATE;
    match goal with
      TF : tr_module _ _ |- _ =>
      inversion TF;
      match goal with
        TC : forall _ _,
          Maps.PTree.get _ _ = Some _ -> tr_code _ _ _ _ _ _ _ _ _,
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

Lemma init_reg_assoc_empty :
  forall f l,
    match_assocmaps f (RTL.init_regs nil l) (HTL.init_regs nil l).
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
Hint Resolve arr_lookup_some : htlproof.

Section CORRECTNESS.

  Variable prog : RTL.program.
  Variable tprog : HTL.program.

  Hypothesis TRANSL : match_prog prog tprog.

  Lemma TRANSL' :
    Linking.match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.
  Proof. intros; apply match_prog_matches; assumption. Qed.

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : HTL.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. intros. eapply (Genv.find_symbol_match TRANSL'). Qed.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: RTL.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL'); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: RTL.fundef),
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
  Hint Resolve senv_preserved : htlproof.

  Lemma ptrofs_inj :
    forall a b,
      Ptrofs.unsigned a = Ptrofs.unsigned b -> a = b.
  Proof.
    intros. rewrite <- Ptrofs.repr_unsigned. symmetry. rewrite <- Ptrofs.repr_unsigned.
    rewrite H. auto.
  Qed.

  Lemma op_stack_based :
    forall F V sp v m args rs op ge pc' res0 pc f e fin rtrn st stk,
      tr_instr fin rtrn st stk (RTL.Iop op args res0 pc')
               (Verilog.Vnonblock (Verilog.Vvar res0) e)
               (state_goto st pc') ->
      reg_stack_based_pointers sp rs ->
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res0 pc') ->
      @Op.eval_operation F V ge (Values.Vptr sp Ptrofs.zero) op
                        (map (fun r : positive => Registers.Regmap.get r rs) args) m = Some v ->
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
      | H: match _ with _ => _ end = Some _ |- _ => repeat (unfold_match H)
      | H: match _ with _ => _ end = OK _ _ _ |- _ => repeat (unfold_match H)
      | |- context[match ?g with _ => _ end] => destruct g; try discriminate
      | |- _ => simplify; solve [auto]
      end.
    intros F V sp v m args rs op g pc' res0 pc f e fin rtrn st stk INSTR RSBP SEL EVAL.
    inv INSTR. unfold translate_instr in H5.
    unfold_match H5; repeat (unfold_match H5); repeat (simplify; solve_no_ptr).
  Qed.

  Lemma int_inj :
    forall x y,
      Int.unsigned x = Int.unsigned y ->
      x = y.
  Proof.
    intros. rewrite <- Int.repr_unsigned at 1. rewrite <- Int.repr_unsigned.
    rewrite <- H. trivial.
  Qed.

  Lemma eval_correct :
    forall s sp op rs m v e asr asa f f' stk s' i pc res0 pc' args res ml st,
      match_states (RTL.State stk f sp pc rs m) (HTL.State res ml st asr asa) ->
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res0 pc') ->
      Op.eval_operation ge sp op
                        (List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some v ->
      translate_instr op args s = OK e s' i ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
  Proof.
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
      | H : context[RTL.max_reg_function ?f]
        |- context[_ (Registers.Regmap.get ?r ?rs) (Registers.Regmap.get ?r0 ?rs)] =>
        let HPle1 := fresh "HPle" in
        let HPle2 := fresh "HPle" in
        assert (HPle1 : Ple r (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        assert (HPle2 : Ple r0 (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H in HPle1; apply H in HPle2; eexists; split;
        [econstructor; eauto; constructor; trivial | inv HPle1; inv HPle2; try (constructor; auto)]
      | H : context[RTL.max_reg_function ?f]
        |- context[_ (Registers.Regmap.get ?r ?rs) _] =>
        let HPle1 := fresh "HPle" in
        assert (HPle1 : Ple r (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H in HPle1; eexists; split;
        [econstructor; eauto; constructor; trivial | inv HPle1; try (constructor; auto)]
      | H : _ :: _ = _ :: _ |- _ => inv H
      | |- context[match ?d with _ => _ end] => destruct d eqn:?; try discriminate
      | H : match ?d with _ => _ end = _ |- _ => repeat unfold_match H
      | H : match ?d with _ => _ end _ = _ |- _ => repeat unfold_match H
      | |- Verilog.expr_runp _ _ _ _ _ => econstructor
      | |- val_value_lessdef (?f _ _) _ => unfold f
      | |- val_value_lessdef (?f _) _ => unfold f
      | H : ?f (Registers.Regmap.get _ _) _ = Some _ |- _ =>
        unfold f in H; repeat (unfold_match H)
      | H1 : Registers.Regmap.get ?r ?rs = Values.Vint _, H2 : val_value_lessdef (Registers.Regmap.get ?r ?rs) _
        |- _ => rewrite H1 in H2; inv H2
      | |- _ => eexists; split; try constructor; solve [eauto]
      | H : context[RTL.max_reg_function ?f] |- context[_ (Verilog.Vvar ?r) (Verilog.Vvar ?r0)] =>
        let HPle1 := fresh "H" in
        let HPle2 := fresh "H" in
        assert (HPle1 : Ple r (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        assert (HPle2 : Ple r0 (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H in HPle1; apply H in HPle2; eexists; split; try constructor; eauto
      | H : context[RTL.max_reg_function ?f] |- context[Verilog.Vvar ?r] =>
        let HPle := fresh "H" in
        assert (HPle : Ple r (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H in HPle; eexists; split; try constructor; eauto
      | |- context[if ?c then _ else _] => destruct c eqn:?; try discriminate
      | H : ?b = _ |- _ = boolToValue ?b => rewrite H
      end.
      Ltac inv_lessdef := lazymatch goal with
      | H2 : context[RTL.max_reg_function ?f], H : Registers.Regmap.get ?r ?rs = _,
                                                   H1 : Registers.Regmap.get ?r0 ?rs = _ |- _ =>
        let HPle1 := fresh "HPle" in
        assert (HPle1 : Ple r (RTL.max_reg_function f))
          by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H2 in HPle1; inv HPle1;
        let HPle2 := fresh "HPle" in
        assert (HPle2 : Ple r0 (RTL.max_reg_function f))
          by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H2 in HPle2; inv HPle2
      | H2 : context[RTL.max_reg_function ?f], H : Registers.Regmap.get ?r ?rs = _ |- _ =>
        let HPle1 := fresh "HPle" in
        assert (HPle1 : Ple r (RTL.max_reg_function f))
          by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
        apply H2 in HPle1; inv HPle1
      end.
      Ltac solve_cond :=
        match goal with
        | H : context[match _ with _ => _ end] |- _ => repeat (unfold_merge H)
        | H : ?f = _ |- context[boolToValue ?f] => rewrite H; solve [auto]
        | H : Values.Vptr _ _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vint _ |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vundef = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vint _ |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vint _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vundef |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vint _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vptr _ _ |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vundef = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vptr _ _ |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vptr _ _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vundef |- _ =>
          rewrite H2 in H; discriminate
        | |- context[val_value_lessdef Values.Vundef _] =>
          econstructor; split; econstructor; econstructor; auto; solve [constructor]
        | H1 : Registers.Regmap.get ?r ?rs = Values.Vint _,
          H2 : Values.Vint _ = Registers.Regmap.get ?r ?rs,
          H3 : Registers.Regmap.get ?r0 ?rs = Values.Vint _,
          H4 : Values.Vint _ = Registers.Regmap.get ?r0 ?rs|- _ =>
          rewrite H1 in H2; rewrite H3 in H4; inv H2; inv H4; unfold valueToInt in *; constructor
        | H1 : Registers.Regmap.get ?r ?rs = Values.Vptr _ _,
          H2 : Values.Vptr _ _ = Registers.Regmap.get ?r ?rs,
          H3 : Registers.Regmap.get ?r0 ?rs = Values.Vptr _ _,
          H4 : Values.Vptr _ _ = Registers.Regmap.get ?r0 ?rs|- _ =>
          rewrite H1 in H2; rewrite H3 in H4; inv H2; inv H4; unfold valueToInt in *; constructor;
          unfold Ptrofs.ltu, Int.ltu in *; unfold Ptrofs.of_int in *;
          repeat (rewrite Ptrofs.unsigned_repr in *; auto using Int.unsigned_range_2)
        | H : _ :: _ = _ :: _ |- _ => inv H
        | H : ret _ _ = OK _ _ _ |- _ => inv H
        | |- _ =>
          eexists; split; [ econstructor; econstructor; auto
                          | simplify; inv_lessdef; repeat (unfold valueToPtr, valueToInt in *; solve_cond);
                            unfold valueToPtr in *
                          ]
        end.
    intros s sp op rs m v e asr asa f f' stk s' i pc pc' res0 args res ml st MSTATE INSTR EVAL TR_INSTR.
    inv MSTATE. inv MASSOC. unfold translate_instr in TR_INSTR; repeat (unfold_match TR_INSTR); inv TR_INSTR;
    unfold Op.eval_operation in EVAL; repeat (unfold_match EVAL); inv EVAL;
    repeat (simplify; eval_correct_tac; unfold valueToInt in *).
    - pose proof Integers.Ptrofs.agree32_sub as H2; unfold Integers.Ptrofs.agree32 in H2.
      unfold Ptrofs.of_int. simpl.
      apply ptrofs_inj. assert (Archi.ptr64 = false) by auto. eapply H2 in H3.
      rewrite Ptrofs.unsigned_repr. apply H3. replace Ptrofs.max_unsigned with Int.max_unsigned; auto.
      apply Int.unsigned_range_2.
      auto. rewrite Ptrofs.unsigned_repr. replace Ptrofs.max_unsigned with Int.max_unsigned; auto.
      apply Int.unsigned_range_2. rewrite Ptrofs.unsigned_repr. auto.
      replace Ptrofs.max_unsigned with Int.max_unsigned; auto.
      apply Int.unsigned_range_2.
    - pose proof Integers.Ptrofs.agree32_sub as AGR; unfold Integers.Ptrofs.agree32 in AGR.
      assert (ARCH: Archi.ptr64 = false) by auto. eapply AGR in ARCH.
      apply int_inj. unfold Ptrofs.to_int. rewrite Int.unsigned_repr.
      apply ARCH. pose proof Ptrofs.unsigned_range_2.
      replace Ptrofs.max_unsigned with Int.max_unsigned; auto.
      pose proof Ptrofs.agree32_of_int. unfold Ptrofs.agree32 in H2.
      eapply H2 in ARCH. apply ARCH.
      pose proof Ptrofs.agree32_of_int. unfold Ptrofs.agree32 in H2.
      eapply H2 in ARCH. apply ARCH.
    - rewrite H0 in Heqb. rewrite H1 in Heqb. discriminate.
    - rewrite Heqb in Heqb0. discriminate.
    - rewrite H0 in Heqb. rewrite H1 in Heqb. discriminate.
    - rewrite Heqb in Heqb0. discriminate.
    (*- unfold Int.ror. unfold Int.or. unfold Int.shru, Int.shl, Int.sub. unfold intToValue. unfold Int.modu,
      Search Int.repr.
      repeat (rewrite Int.unsigned_repr). auto.*)
    - unfold Op.eval_addressing32 in *. repeat (unfold_match H2); inv H2.
      + unfold translate_eff_addressing in *. repeat (unfold_match H1).
        destruct v0; inv Heql; rewrite H2; inv H1; repeat eval_correct_tac.
        pose proof Integers.Ptrofs.agree32_add as AGR; unfold Integers.Ptrofs.agree32 in AGR. unfold ZToValue.
        apply ptrofs_inj. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr.
        apply AGR. auto. rewrite H2 in H0. inv H0. unfold valueToPtr. unfold Ptrofs.of_int.
        rewrite Ptrofs.unsigned_repr. auto. replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
        apply Int.unsigned_range_2.
        rewrite Ptrofs.unsigned_repr. auto. replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
        apply Int.unsigned_range_2.
        replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
        apply Int.unsigned_range_2.
      + unfold translate_eff_addressing in *. repeat (unfold_match H1). inv H1.
        inv Heql. unfold boplitz. repeat (simplify; eval_correct_tac).
        all: repeat (unfold_match Heqv).
        * inv Heqv. unfold valueToInt in *. inv H2. inv H0. unfold valueToInt in *. trivial.
        * constructor. unfold valueToPtr, ZToValue in *.
          pose proof Integers.Ptrofs.agree32_add as AGR; unfold Integers.Ptrofs.agree32 in AGR. unfold ZToValue.
          apply ptrofs_inj. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr.
          apply AGR. auto. inv Heqv. rewrite Int.add_commut.
          apply AGR. auto. inv H1. inv H0. unfold valueToPtr. unfold Ptrofs.of_int.
          rewrite Ptrofs.unsigned_repr. auto. replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
          apply Int.unsigned_range_2.
          unfold Ptrofs.of_int.
          rewrite Ptrofs.unsigned_repr. inv H0. auto. replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
          apply Int.unsigned_range_2.
          rewrite Ptrofs.unsigned_repr. auto. replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
          apply Int.unsigned_range_2.
          apply Int.unsigned_range_2.
        * constructor. unfold valueToPtr, ZToValue in *.
          pose proof Integers.Ptrofs.agree32_add as AGR; unfold Integers.Ptrofs.agree32 in AGR. unfold ZToValue.
          apply ptrofs_inj. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr.
          apply AGR. auto. inv Heqv.
          apply AGR. auto. inv H0. unfold valueToPtr, Ptrofs.of_int. rewrite Ptrofs.unsigned_repr. auto.
          replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
          apply Int.unsigned_range_2.
          inv H1. unfold valueToPtr, Ptrofs.of_int. rewrite Ptrofs.unsigned_repr. auto.
          replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
          apply Int.unsigned_range_2.
          rewrite Ptrofs.unsigned_repr. auto.
          replace Ptrofs.max_unsigned with Int.max_unsigned by auto.
          apply Int.unsigned_range_2. apply Int.unsigned_range_2.
      + unfold translate_eff_addressing in *. repeat (unfold_match H1). inv H1.
        inv Heql. unfold boplitz. repeat (simplify; eval_correct_tac).
        all: repeat (unfold_match Heqv).
        * unfold Values.Val.mul in Heqv. repeat (unfold_match Heqv). inv Heqv. inv H3.
          unfold valueToInt, ZToValue. auto.
        * unfold Values.Val.mul in Heqv. repeat (unfold_match Heqv).
        * unfold Values.Val.mul in Heqv. repeat (unfold_match Heqv).
        * constructor. unfold valueToPtr, ZToValue. unfold Values.Val.mul in Heqv. repeat (unfold_match Heqv).
      + unfold translate_eff_addressing in *. repeat (unfold_match H1). inv H1.
        inv Heql. unfold boplitz. repeat (simplify; eval_correct_tac).
        all: repeat (unfold_match Heqv).
        unfold valueToPtr, ZToValue.
        repeat unfold_match Heqv0. unfold Values.Val.mul in Heqv1. repeat unfold_match Heqv1.
        inv Heqv1. inv Heqv0. unfold valueToInt in *.
        assert (HPle1 : Ple r0 (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
        apply H in HPle1. inv HPle1. unfold valueToInt in *. rewrite Heqv2 in H2. inv H2. auto.
        rewrite Heqv2 in H2. inv H2.
        rewrite Heqv2 in H3. discriminate.
        repeat unfold_match Heqv0. unfold Values.Val.mul in Heqv1. repeat unfold_match Heqv1.
        repeat unfold_match Heqv0. unfold Values.Val.mul in Heqv1. repeat unfold_match Heqv1.
        constructor. unfold valueToPtr, ZToValue. inv Heqv0. inv Heqv1.
        assert (HPle1 : Ple r0 (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
        apply H in HPle1. inv HPle1. unfold valueToInt in *. rewrite Heqv2 in H3. inv H3.

        pose proof Integers.Ptrofs.agree32_add as AGR; unfold Integers.Ptrofs.agree32 in AGR. unfold ZToValue.
        apply ptrofs_inj. unfold Ptrofs.of_int. rewrite Ptrofs.unsigned_repr.
        apply AGR. auto. inv H2. unfold valueToPtr, Ptrofs.of_int. rewrite Ptrofs.unsigned_repr. auto.
        replace Ptrofs.max_unsigned with Int.max_unsigned by auto. apply Int.unsigned_range_2.
        apply Ptrofs.unsigned_repr. apply Int.unsigned_range_2. apply Int.unsigned_range_2.

        rewrite Heqv2 in H3. inv H3.

        rewrite Heqv2 in H4. inv H4.
      + unfold translate_eff_addressing in *. repeat (unfold_match H1). inv H1.
        inv Heql. unfold boplitz. repeat (simplify; eval_correct_tac).
        all: repeat (unfold_match Heqv).
        eexists. split. constructor.
        constructor. unfold valueToPtr, ZToValue. rewrite Ptrofs.add_zero_l. unfold Ptrofs.of_int.
        rewrite Int.unsigned_repr. symmetry. apply Ptrofs.repr_unsigned.
        unfold check_address_parameter_unsigned in *. apply Ptrofs.unsigned_range_2.
    - unfold translate_condition in *; repeat unfold_match H1;
      unfold translate_comparison in *; repeat unfold_match H1; inv H1;
      unfold translate_comparisonu, translate_comparison_imm, translate_comparison_immu in *;
      unfold Op.eval_condition, Values.Val.of_optbool, Values.Val.cmp_bool, Values.Val.cmpu_bool, bop in *;
      simplify;
      repeat (match goal with |- context[match ?d with _ => _ end] => destruct d eqn:? end;
      match goal with H : context[match ?d with _ => _ end] |- _ => repeat unfold_match H end);
      try (match goal with |- context[if ?d then _ else _] => destruct d eqn:? end);
      simplify; repeat solve_cond;
      try (match goal with H : ?f = _ |- context[boolToValue ?f] => rewrite H; solve [auto] end);
      try (match goal with H : context[match ?d with _ => _ end] |- _ => repeat unfold_match H end);
      simplify; repeat solve_cond.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
      + rewrite H3 in H0. inv H0. constructor. unfold valueToInt, intToValue in *. rewrite H1. auto.
    - admit. (* select *)
            Admitted.

  Lemma eval_cond_correct :
    forall e asa asr f' m args rs cond,
    exists v' : value,
      Verilog.expr_runp f' asr asa e v' /\
      val_value_lessdef
        (Values.Val.of_optbool
           (Op.eval_condition cond
                              (map (fun r : positive => Registers.Regmap.get r rs) args) m)) v'.
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
    forall m asr asa fin rtrn st stmt trans res,
      tr_instr fin rtrn st (m.(HTL.mod_stk)) instr stmt trans ->
      exists asr' asa',
        HTL.step tge (HTL.State res m st asr asa) Events.E0 (HTL.State res m st asr' asa').

  Opaque combine.

  Ltac tac0 :=
    match goal with
    | [ |- context[Verilog.merge_arrs _ _] ] => unfold Verilog.merge_arrs
    | [ |- context[Verilog.merge_arr] ] => unfold Verilog.merge_arr
    | [ |- context[Verilog.merge_regs _ _] ] => unfold Verilog.merge_regs; crush; unfold_merge
    | [ |- context[reg_stack_based_pointers] ] => unfold reg_stack_based_pointers; intros
    | [ |- context[Verilog.arr_assocmap_set _ _ _ _] ] => unfold Verilog.arr_assocmap_set

    | [ |- context[HTL.empty_stack] ] => unfold HTL.empty_stack

    | [ |- context[_ # ?d <- _ ! ?d] ] => rewrite AssocMap.gss
    | [ |- context[_ # ?d <- _ ! ?s] ] => rewrite AssocMap.gso
    | [ |- context[(AssocMap.empty _) ! _] ] => rewrite AssocMap.gempty

    | [ |- context[array_get_error _ (combine Verilog.merge_cell (arr_repeat None _) _)] ] =>
      rewrite combine_lookup_first

    | [ |- state_st_wf _ _ ] => unfold state_st_wf; inversion 1
    | [ |- context[match_states _ _] ] => econstructor; auto
    | [ |- match_arrs _ _ _ _ _ ] => econstructor; auto
    | [ |- match_assocmaps _ _ _ # _ <- (posToValue _) ] =>
      apply regs_lessdef_add_greater; [> unfold Plt; lia | assumption]

    | [ H : ?asa ! ?r = Some _ |- Verilog.arr_assocmap_lookup ?asa ?r _ = Some _ ] =>
      unfold Verilog.arr_assocmap_lookup; setoid_rewrite H; f_equal
    | [ |- context[(AssocMap.combine _ _ _) ! _] ] =>
      try (rewrite AssocMap.gcombine; [> | reflexivity])

    | [ |- context[Registers.Regmap.get ?d (Registers.Regmap.set ?d _ _)] ] =>
      rewrite Registers.Regmap.gss
    | [ |- context[Registers.Regmap.get ?s (Registers.Regmap.set ?d _ _)] ] =>
      destruct (Pos.eq_dec s d) as [EQ|EQ];
      [> rewrite EQ | rewrite Registers.Regmap.gso; auto]

    | [ H : opt_val_value_lessdef _ _ |- _ ] => invert H
    | [ H : context[Z.of_nat (Z.to_nat _)] |- _ ] => rewrite Z2Nat.id in H; [> solve crush |]
    | [ H : _ ! _ = Some _ |- _] => setoid_rewrite H
    end.

  Ltac small_tac := repeat (crush_val; try array; try ptrofs); crush_val; auto.
  Ltac big_tac := repeat (crush_val; try array; try ptrofs; try tac0); crush_val; auto.

  Lemma transl_inop_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : RTL.regset) (m : mem) (pc' : RTL.node),
      (RTL.fn_code f) ! pc = Some (RTL.Inop pc') ->
      forall R1 : HTL.state,
        match_states (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states (RTL.State s f sp pc' rs m) R2.
  Proof.
    intros s f sp pc rs m pc' H R1 MSTATE.
    inv_state.

    unfold match_prog in TRANSL.
    econstructor.
    split.
    apply Smallstep.plus_one.
    eapply HTL.step_module; eauto.
    inv CONST; assumption.
    inv CONST; assumption. 
    (* processing of state *)
    econstructor.
    crush.
    econstructor.
    econstructor.
    econstructor.

    all: invert MARR; big_tac.

    inv CONST; constructor; simplify; rewrite AssocMap.gso; auto; lia.

    Unshelve. exact tt.
  Qed.
  Hint Resolve transl_inop_correct : htlproof.

  Lemma transl_iop_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (op : Op.operation) (args : list Registers.reg)
      (res0 : Registers.reg) (pc' : RTL.node) (v : Values.val),
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res0 pc') ->
      Op.eval_operation ge sp op (map (fun r : positive => Registers.Regmap.get r rs) args) m = Some v ->
      forall R1 : HTL.state,
        match_states (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states (RTL.State s f sp pc' (Registers.Regmap.set res0 v rs) m) R2.
  Proof.
    intros s f sp pc rs m op args res0 pc' v H H0 R1 MSTATE.
    inv_state. inv MARR.
    exploit eval_correct; eauto. intros. inversion H1. inversion H2.
    econstructor. split.
    apply Smallstep.plus_one.
    eapply HTL.step_module; eauto.
    inv CONST. assumption.
    inv CONST. assumption.
    econstructor; simpl; trivial.
    constructor; trivial.
    econstructor; simpl; eauto.
    simpl. econstructor. econstructor.
    apply H5. simplify.

    all: big_tac.

    assert (HPle: Ple res0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).

    unfold Ple in HPle. lia.
    apply regs_lessdef_add_match. assumption.
    apply regs_lessdef_add_greater. unfold Plt; lia. assumption.
    assert (HPle: Ple res0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
    unfold Ple in HPle; lia.
    eapply op_stack_based; eauto.
    inv CONST. constructor; simplify. rewrite AssocMap.gso. rewrite AssocMap.gso.
    assumption. lia.
    assert (HPle: Ple res0 (RTL.max_reg_function f))
      by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
    unfold Ple in HPle. lia.
    rewrite AssocMap.gso. rewrite AssocMap.gso.
    assumption. lia.
    assert (HPle: Ple res0 (RTL.max_reg_function f))
      by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
    unfold Ple in HPle. lia.
    Unshelve. exact tt.
  Qed.
  Hint Resolve transl_iop_correct : htlproof.

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
           | [ H : ret _ _ = _  |- _ ] => invert H
           | [ _ : context[match ?x with | _ => _ end] |- _ ] => destruct x
           end.

  Ltac inv_arr_access :=
    match goal with
    | [ _ : translate_arr_access ?chunk ?addr ?args _ _ = OK ?c _ _ |- _] =>
      destruct c, chunk, addr, args; crush; tac; crush
    end.

  Lemma transl_iload_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (chunk : AST.memory_chunk)
      (addr : Op.addressing) (args : list Registers.reg) (dst : Registers.reg)
      (pc' : RTL.node) (a v : Values.val),
      (RTL.fn_code f) ! pc = Some (RTL.Iload chunk addr args dst pc') ->
      Op.eval_addressing ge sp addr (map (fun r : positive => Registers.Regmap.get r rs) args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      forall R1 : HTL.state,
        match_states (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states (RTL.State s f sp pc' (Registers.Regmap.set dst v rs) m) R2.
  Proof.
    intros s f sp pc rs m chunk addr args dst pc' a v H H0 H1 R1 MSTATE.
    inv_state. inv_arr_access.

    + (** Preamble *)
      invert MARR. inv CONST. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.

      unfold reg_stack_based_pointers in RSBP.
      pose proof (RSBP r0) as RSBPr0.

      destruct (Registers.Regmap.get r0 rs) eqn:EQr0; crush.

      rewrite ARCHI in H1. crush.
      subst.

      pose proof MASSOC as MASSOC'.
      invert MASSOC'.
      pose proof (H0 r0).
      assert (HPler0 : Ple r0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; crush; eauto).
      apply H0 in HPler0.
      invert HPler0; try congruence.
      rewrite EQr0 in H11.
      invert H11.

      unfold check_address_parameter_signed in *;
      unfold check_address_parameter_unsigned in *; crush.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int (Integers.Int.repr z))) as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { apply Mem.load_valid_access in H1. unfold Mem.valid_access in *. simplify.
        apply Zdivide_mod. assumption. }

      (** Read bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as READ_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET)); auto.
        split; try lia; apply Integers.Ptrofs.unsigned_range_2.
        small_tac. }

      (** Normalisation proof *)
      assert (Integers.Ptrofs.repr
                (4 * Integers.Ptrofs.unsigned
                       (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4))) = OFFSET)
        as NORMALISE.
      { replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) at 1 by reflexivity.
        rewrite <- PtrofsExtra.mul_unsigned.
        apply PtrofsExtra.mul_divu; crush; auto. }

      (** Normalised bounds proof *)
      assert (0 <=
              Integers.Ptrofs.unsigned (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4))
              < (RTL.fn_stacksize f / 4))
        as NORMALISE_BOUND.
      { split.
        apply Integers.Ptrofs.unsigned_range_2.
        assert (HDIV: forall x y, Integers.Ptrofs.divu x y = Integers.Ptrofs.divu x y ) by reflexivity.
        unfold Integers.Ptrofs.divu at 2 in HDIV.
        rewrite HDIV. clear HDIV.
        rewrite Integers.Ptrofs.unsigned_repr; crush.
        apply Zmult_lt_reg_r with (p := 4); try lia.
        repeat rewrite ZLib.div_mul_undo; try lia.
        apply Z.div_pos; small_tac.
        apply Z.div_le_upper_bound; small_tac. }

      inversion NORMALISE_BOUND as [ NORMALISE_BOUND_LOW NORMALISE_BOUND_HIGH ];
      clear NORMALISE_BOUND.

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor.

      all: big_tac.

      1: {
        assert (HPle : Ple dst (RTL.max_reg_function f)).
        eapply RTL.max_reg_function_def. eassumption. auto.
        apply ZExtra.Pge_not_eq. apply ZExtra.Ple_Plt_Succ. assumption.
      }

      2: {
        assert (HPle : Ple dst (RTL.max_reg_function f)).
        eapply RTL.max_reg_function_def. eassumption. auto.
        apply ZExtra.Pge_not_eq. apply ZExtra.Ple_Plt_Succ. assumption.
      }

      (** Match assocmaps *)
      apply regs_lessdef_add_match; big_tac.

      (** Equality proof *)
      match goal with
      | [ |- context [valueToNat ?x] ] =>
        assert (Z.to_nat
                  (Integers.Ptrofs.unsigned
                     (Integers.Ptrofs.divu
                        OFFSET
                        (Integers.Ptrofs.repr 4)))
                =
                valueToNat x)
          as EXPR_OK by admit
      end.
      rewrite <- EXPR_OK.

      specialize (H9 (Integers.Ptrofs.unsigned
                        (Integers.Ptrofs.divu
                           OFFSET
                           (Integers.Ptrofs.repr 4)))).
      exploit H9; big_tac.

      (** RSBP preservation *)
      unfold arr_stack_based_pointers in ASBP.
      specialize (ASBP (Integers.Ptrofs.unsigned
                          (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4)))).
      exploit ASBP; big_tac.
      rewrite NORMALISE in H11. rewrite HeqOFFSET in H11. rewrite H1 in H11. assumption.
      constructor; simplify. rewrite AssocMap.gso. rewrite AssocMap.gso.
      assumption. lia.
      assert (HPle: Ple dst (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
      unfold Ple in HPle. lia.
      rewrite AssocMap.gso. rewrite AssocMap.gso.
      assumption. lia.
      assert (HPle: Ple dst (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
      unfold Ple in HPle. lia.
    + (** Preamble *)
      invert MARR. inv CONST. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.

      unfold reg_stack_based_pointers in RSBP.
      pose proof (RSBP r0) as RSBPr0.
      pose proof (RSBP r1) as RSBPr1.

      destruct (Registers.Regmap.get r0 rs) eqn:EQr0;
      destruct (Registers.Regmap.get r1 rs) eqn:EQr1; crush.

      rewrite ARCHI in H1. crush.
      subst.
      clear RSBPr1.

      pose proof MASSOC as MASSOC'.
      invert MASSOC'.
      pose proof (H0 r0).
      pose proof (H0 r1).
      assert (HPler0 : Ple r0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; crush; eauto).
      assert (HPler1 : Ple r1 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
      apply H8 in HPler0.
      apply H11 in HPler1.
      invert HPler0; invert HPler1; try congruence.
      rewrite EQr0 in H13.
      rewrite EQr1 in H14.
      invert H13. invert H14.
      clear H0. clear H8. clear H11.

      unfold check_address_parameter_signed in *;
      unfold check_address_parameter_unsigned in *; crush.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add (Integers.Int.mul (valueToInt asr # r1) (Integers.Int.repr z))
                                                         (Integers.Int.repr z0)))) as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { apply Mem.load_valid_access in H1. unfold Mem.valid_access in *. simplify.
        apply Zdivide_mod. assumption. }

      (** Read bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as READ_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET)); auto.
        split; try lia; apply Integers.Ptrofs.unsigned_range_2.
        small_tac. }

      (** Normalisation proof *)
      assert (Integers.Ptrofs.repr
                (4 * Integers.Ptrofs.unsigned
                       (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4))) = OFFSET)
        as NORMALISE.
      { replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) at 1 by reflexivity.
        rewrite <- PtrofsExtra.mul_unsigned.
        apply PtrofsExtra.mul_divu; crush. }

      (** Normalised bounds proof *)
      assert (0 <=
              Integers.Ptrofs.unsigned (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4))
              < (RTL.fn_stacksize f / 4))
        as NORMALISE_BOUND.
      { split.
        apply Integers.Ptrofs.unsigned_range_2.
        assert (forall x y, Integers.Ptrofs.divu x y = Integers.Ptrofs.divu x y ) by reflexivity.
        unfold Integers.Ptrofs.divu at 2 in H0.
        rewrite H0. clear H0.
        rewrite Integers.Ptrofs.unsigned_repr; crush.
        apply Zmult_lt_reg_r with (p := 4); try lia.
        repeat rewrite ZLib.div_mul_undo; try lia.
        apply Z.div_pos; small_tac.
        apply Z.div_le_upper_bound; lia. }

      inversion NORMALISE_BOUND as [ NORMALISE_BOUND_LOW NORMALISE_BOUND_HIGH ];
      clear NORMALISE_BOUND.

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. auto. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      all: big_tac.

      1: { assert (HPle : Ple dst (RTL.max_reg_function f)).
           eapply RTL.max_reg_function_def. eassumption. auto.
           apply ZExtra.Pge_not_eq. apply ZExtra.Ple_Plt_Succ. assumption. }

      2: { assert (HPle : Ple dst (RTL.max_reg_function f)).
           eapply RTL.max_reg_function_def. eassumption. auto.
           apply ZExtra.Pge_not_eq. apply ZExtra.Ple_Plt_Succ. assumption. }

      (** Match assocmaps *)
      apply regs_lessdef_add_match; big_tac.

      (** Equality proof *)
      match goal with
      | [ |- context [valueToNat ?x] ] =>
        assert (Z.to_nat
                  (Integers.Ptrofs.unsigned
                     (Integers.Ptrofs.divu
                        OFFSET
                        (Integers.Ptrofs.repr 4)))
                =
                valueToNat x)
          as EXPR_OK by admit
      end.
      rewrite <- EXPR_OK.

      specialize (H9 (Integers.Ptrofs.unsigned
                        (Integers.Ptrofs.divu
                           OFFSET
                           (Integers.Ptrofs.repr 4)))).
      exploit H9; big_tac.

      (** RSBP preservation *)
      unfold arr_stack_based_pointers in ASBP.
      specialize (ASBP (Integers.Ptrofs.unsigned
                          (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4)))).
      exploit ASBP; big_tac.
      rewrite NORMALISE in H0. rewrite HeqOFFSET in H0. rewrite H1 in H0. assumption.

      constructor; simplify. rewrite AssocMap.gso. rewrite AssocMap.gso.
      assumption. lia.
      assert (HPle: Ple dst (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
      unfold Ple in HPle. lia.
      rewrite AssocMap.gso. rewrite AssocMap.gso.
      assumption. lia.
      assert (HPle: Ple dst (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
      unfold Ple in HPle. lia.

    + invert MARR. inv CONST. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.
      rewrite ARCHI in H0. crush.

      unfold check_address_parameter_unsigned in *;
      unfold check_address_parameter_signed in *; crush.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      rewrite ZERO in H1. clear ZERO.
      rewrite Integers.Ptrofs.add_zero_l in H1.

      remember i0 as OFFSET.

      (** Modular preservation proof *)
      rename H0 into MOD_PRESERVE.

      (** Read bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as READ_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET)); big_tac. }

      (** Normalisation proof *)
      assert (Integers.Ptrofs.repr
                (4 * Integers.Ptrofs.unsigned
                       (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4))) = OFFSET)
        as NORMALISE.
      { replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) at 1 by reflexivity.
        rewrite <- PtrofsExtra.mul_unsigned.
        apply PtrofsExtra.mul_divu; crush. }

      (** Normalised bounds proof *)
      assert (0 <=
              Integers.Ptrofs.unsigned (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4))
              < (RTL.fn_stacksize f / 4))
        as NORMALISE_BOUND.
      { split.
        apply Integers.Ptrofs.unsigned_range_2.
        assert (forall x y, Integers.Ptrofs.divu x y = Integers.Ptrofs.divu x y ) by reflexivity.
        unfold Integers.Ptrofs.divu at 2 in H0.
        rewrite H0. clear H0.
        rewrite Integers.Ptrofs.unsigned_repr; crush.
        apply Zmult_lt_reg_r with (p := 4); try lia.
        repeat rewrite ZLib.div_mul_undo; try lia.
        apply Z.div_pos; small_tac.
        apply Z.div_le_upper_bound; lia. }

      inversion NORMALISE_BOUND as [ NORMALISE_BOUND_LOW NORMALISE_BOUND_HIGH ];
      clear NORMALISE_BOUND.

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor. econstructor. crush.

      all: big_tac.

      1: { assert (HPle : Ple dst (RTL.max_reg_function f)).
           eapply RTL.max_reg_function_def. eassumption. auto.
           apply ZExtra.Pge_not_eq. apply ZExtra.Ple_Plt_Succ. assumption. }

      2: { assert (HPle : Ple dst (RTL.max_reg_function f)).
           eapply RTL.max_reg_function_def. eassumption. auto.
           apply ZExtra.Pge_not_eq. apply ZExtra.Ple_Plt_Succ. assumption. }

      (** Match assocmaps *)
      apply regs_lessdef_add_match; big_tac.

      (** Equality proof *)
      match goal with (* Prevents issues with evars *)
      | [ |- context [valueToNat ?x] ] =>
        assert (Z.to_nat
                  (Integers.Ptrofs.unsigned
                     (Integers.Ptrofs.divu
                        OFFSET
                        (Integers.Ptrofs.repr 4)))
                =
                valueToNat x)
          as EXPR_OK by admit
      end.
      rewrite <- EXPR_OK.

      specialize (H9 (Integers.Ptrofs.unsigned
                        (Integers.Ptrofs.divu
                           OFFSET
                           (Integers.Ptrofs.repr 4)))).
      exploit H9; big_tac.

      (** RSBP preservation *)
      unfold arr_stack_based_pointers in ASBP.
      specialize (ASBP (Integers.Ptrofs.unsigned
                          (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4)))).
      exploit ASBP; big_tac.
      rewrite NORMALISE in H0. rewrite H1 in H0. assumption.
  Admitted.
  Hint Resolve transl_iload_correct : htlproof.

  Lemma transl_istore_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (chunk : AST.memory_chunk)
      (addr : Op.addressing) (args : list Registers.reg) (src : Registers.reg)
      (pc' : RTL.node) (a : Values.val) (m' : mem),
      (RTL.fn_code f) ! pc = Some (RTL.Istore chunk addr args src pc') ->
      Op.eval_addressing ge sp addr (map (fun r : positive => Registers.Regmap.get r rs) args) = Some a ->
      Mem.storev chunk m a (Registers.Regmap.get src rs) = Some m' ->
      forall R1 : HTL.state,
        match_states (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states (RTL.State s f sp pc' rs m') R2.
  Proof.
    intros s f sp pc rs m chunk addr args src pc' a m' H H0 H1 R1 MSTATES.
    inv_state. inv_arr_access.

    + (** Preamble *)
      invert MARR. inv CONST. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.

      unfold reg_stack_based_pointers in RSBP.
      pose proof (RSBP r0) as RSBPr0.

      destruct (Registers.Regmap.get r0 rs) eqn:EQr0; crush.

      rewrite ARCHI in H1. crush.
      subst.

      pose proof MASSOC as MASSOC'.
      invert MASSOC'.
      pose proof (H0 r0).
      assert (HPler0 : Ple r0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; crush; eauto).
      apply H8 in HPler0.
      invert HPler0; try congruence.
      rewrite EQr0 in H11.
      invert H11.
      clear H0. clear H8.

      unfold check_address_parameter_unsigned in *;
      unfold check_address_parameter_signed in *; crush.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int (Integers.Int.repr z))) as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { apply Mem.store_valid_access_3 in H1. unfold Mem.valid_access in *. simplify.
        apply Zdivide_mod. assumption. }

      (** Write bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as WRITE_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET) (Registers.Regmap.get src rs)); big_tac.
        apply Integers.Ptrofs.unsigned_range_2. }

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      econstructor. econstructor. econstructor.
      eapply Verilog.stmnt_runp_Vnonblock_arr. crush.
      econstructor.
      econstructor.
      econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.

      all: crush.

      (** State Lookup *)
      unfold Verilog.merge_regs.
      crush.
      unfold_merge.
      apply AssocMap.gss.

      (** Match states *)
      econstructor; eauto.

      (** Match assocmaps *)
      unfold Verilog.merge_regs. crush. unfold_merge.
      apply regs_lessdef_add_greater.
      unfold Plt; lia.
      assumption.

      (** States well formed *)
      unfold state_st_wf. inversion 1. crush.
      unfold Verilog.merge_regs.
      unfold_merge.
      apply AssocMap.gss.

      (** Equality proof *)
      match goal with
      | [ |- context [valueToNat ?x] ] =>
        assert (Z.to_nat
                  (Integers.Ptrofs.unsigned
                     (Integers.Ptrofs.divu
                        OFFSET
                        (Integers.Ptrofs.repr 4)))
                =
                valueToNat x)
          as EXPR_OK by admit
      end.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      inversion MASSOC; revert HeqOFFSET; subst; clear MASSOC; intros HeqOFFSET.

      econstructor.
      repeat split; crush.
      unfold HTL.empty_stack.
      crush.
      unfold Verilog.merge_arrs.

      rewrite AssocMap.gcombine.
      2: { reflexivity. }
      unfold Verilog.arr_assocmap_set.
      rewrite AssocMap.gss.
      unfold Verilog.merge_arr.
      rewrite AssocMap.gss.
      setoid_rewrite H7.
      reflexivity.

      rewrite combine_length.
      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      apply list_repeat_len.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len.
      rewrite H4. reflexivity.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int (Integers.Int.repr z))) as OFFSET.

      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      erewrite Mem.load_store_same.
      2: { rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           rewrite HeqOFFSET.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      constructor.
      erewrite combine_lookup_second.
      simplify.
      assert (HPle : Ple src (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
      apply H0 in HPle.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; constructor; invert HPle; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.

      assert (HMul : 4 * ptr / 4 = Integers.Ptrofs.unsigned OFFSET / 4) by (f_equal; assumption).
      rewrite Z.mul_comm in HMul.
      rewrite Z_div_mult in HMul; try lia.
      replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) in HMul by reflexivity.
      rewrite <- PtrofsExtra.divu_unsigned in HMul; unfold_constants; try lia.
      rewrite HMul. rewrite EXPR_OK.
      rewrite array_get_error_set_bound.
      reflexivity.
      unfold arr_length, arr_repeat. simpl.
      rewrite list_repeat_len. lia.

      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           rewrite HeqOFFSET in *. simplify_val.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           rewrite HeqOFFSET in *. simplify_val.
           left; auto.
           rewrite HeqOFFSET in *. simplify_val.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           rewrite Z2Nat.id in H16; try lia.
           apply Zmult_lt_compat_r with (p := 4) in H16; try lia.
           rewrite ZLib.div_mul_undo in H16; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }

      rewrite <- EXPR_OK.
      rewrite PtrofsExtra.divu_unsigned; auto; try (unfold_constants; lia).
      destruct (ptr ==Z Integers.Ptrofs.unsigned OFFSET / 4).
      apply Z.mul_cancel_r with (p := 4) in e; try lia.
      rewrite ZLib.div_mul_undo in e; try lia.
      rewrite combine_lookup_first.
      eapply H9; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.
      rewrite array_gso.
      unfold array_get_error.
      unfold arr_repeat.
      crush.
      apply list_repeat_lookup.
      lia.
      unfold_constants.
      intro.
      apply Z2Nat.inj_iff in H14; try lia.
      apply Z.div_pos; try lia.
      apply Integers.Ptrofs.unsigned_range.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      unfold arr_stack_based_pointers.
      intros.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      crush.
      erewrite Mem.load_store_same.
      2: { rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      crush.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; try constructor.
      destruct (Archi.ptr64); try discriminate.
      pose proof (RSBP src). rewrite EQ_SRC in H0.
      assumption.

      simpl.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { (*right.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           invert H0.
           apply Zmult_lt_compat_r with (p := 4) in H15; try lia.
           rewrite ZLib.div_mul_undo in H15; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.*)
        admit.
      }
      apply ASBP; assumption.

      unfold stack_bounds in *. intros.
      simpl.
      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right. right. simpl.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr; crush; try lia.
           apply ZExtra.mod_0_bounds; crush; try lia. admit. admit. }
      crush.
      exploit (BOUNDS ptr); try lia. intros. crush.
      exploit (BOUNDS ptr v); try lia. intros.
      invert H0.
      match goal with | |- ?x = _ => destruct x eqn:EQ end; try reflexivity.
      assert (Mem.valid_access m AST.Mint32 sp'
                               (Integers.Ptrofs.unsigned
                                  (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                       (Integers.Ptrofs.repr ptr))) Writable).
      { pose proof H1. eapply Mem.store_valid_access_2 in H0.
        exact H0. eapply Mem.store_valid_access_3. eassumption. }
      pose proof (Mem.valid_access_store m AST.Mint32 sp'
                                         (Integers.Ptrofs.unsigned
                                            (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                                 (Integers.Ptrofs.repr ptr))) v).
      apply X in H0. invert H0. congruence.

      constructor; simplify. unfold Verilog.merge_regs. unfold_merge.
      rewrite AssocMap.gso.
      assumption. lia.
      unfold Verilog.merge_regs. unfold_merge.
      rewrite AssocMap.gso.
      assumption. lia.

    + (** Preamble *)
      invert MARR. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.

      unfold reg_stack_based_pointers in RSBP.
      pose proof (RSBP r0) as RSBPr0.
      pose proof (RSBP r1) as RSBPr1.

      destruct (Registers.Regmap.get r0 rs) eqn:EQr0;
      destruct (Registers.Regmap.get r1 rs) eqn:EQr1; crush.

      rewrite ARCHI in H1. crush.
      subst.
      clear RSBPr1.

      pose proof MASSOC as MASSOC'.
      invert MASSOC'.
      pose proof (H0 r0).
      pose proof (H0 r1).
      assert (HPler0 : Ple r0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; crush; eauto).
      assert (HPler1 : Ple r1 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
      apply H6 in HPler0.
      apply H8 in HPler1.
      invert HPler0; invert HPler1; try congruence.
      rewrite EQr0 in H9.
      rewrite EQr1 in H11.
      invert H9. invert H11.
      clear H0. clear H6. clear H8.

      unfold check_address_parameter_signed in *;
      unfold check_address_parameter_unsigned in *; crush.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add (Integers.Int.mul (valueToInt asr # r1) (Integers.Int.repr z))
                                                         (Integers.Int.repr z0)))) as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { rewrite HeqOFFSET.
        apply PtrofsExtra.add_mod; crush; try lia.
        rewrite Integers.Ptrofs.unsigned_repr_eq.
        rewrite <- Zmod_div_mod; crush.
        apply PtrofsExtra.of_int_mod.
        apply IntExtra.add_mod; crush.
        apply IntExtra.mul_mod2; crush.
        rewrite Integers.Int.unsigned_repr_eq.
        rewrite <- Zmod_div_mod; crush.
        rewrite Integers.Int.unsigned_repr_eq.
        rewrite <- Zmod_div_mod; crush. }

      (** Write bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as WRITE_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET) (Registers.Regmap.get src rs)); auto.
        split; try lia; apply Integers.Ptrofs.unsigned_range_2.
        small_tac. }

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      apply assumption_32bit.
      econstructor. econstructor. econstructor.
      eapply Verilog.stmnt_runp_Vnonblock_arr. crush.
      econstructor.
      eapply Verilog.erun_Vbinop with (EQ := ?[EQ9]).
      eapply Verilog.erun_Vbinop with (EQ := ?[EQ10]).
      eapply Verilog.erun_Vbinop with (EQ := ?[EQ11]).
      econstructor. econstructor. econstructor. econstructor.
      econstructor.
      eapply Verilog.erun_Vbinop with (EQ := ?[EQ12]).
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.

      all: crush.

      (** State Lookup *)
      unfold Verilog.merge_regs.
      crush.
      unfold_merge.
      apply AssocMap.gss.

      (** Match states *)
      rewrite assumption_32bit.
      econstructor; eauto.

      (** Match assocmaps *)
      unfold Verilog.merge_regs. crush. unfold_merge.
      apply regs_lessdef_add_greater.
      unfold Plt; lia.
      assumption.

      (** States well formed *)
      unfold state_st_wf. inversion 1. crush.
      unfold Verilog.merge_regs.
      unfold_merge.
      apply AssocMap.gss.

      (** Equality proof *)
      assert (Z.to_nat
                (Integers.Ptrofs.unsigned
                   (Integers.Ptrofs.divu
                      OFFSET
                      (Integers.Ptrofs.repr 4)))
              =
              valueToNat (vdiv
                            (vplus (vplus asr # r0 (ZToValue 32 z0) ?EQ11) (vmul asr # r1 (ZToValue 32 z) ?EQ12)
                                   ?EQ10) (ZToValue 32 4) ?EQ9))
        as EXPR_OK by admit.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      inversion MASSOC; revert HeqOFFSET; subst; clear MASSOC; intros HeqOFFSET.

      econstructor.
      repeat split; crush.
      unfold HTL.empty_stack.
      crush.
      unfold Verilog.merge_arrs.

      rewrite AssocMap.gcombine.
      2: { reflexivity. }
      unfold Verilog.arr_assocmap_set.
      rewrite AssocMap.gss.
      unfold Verilog.merge_arr.
      rewrite AssocMap.gss.
      setoid_rewrite H5.
      reflexivity.

      rewrite combine_length.
      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      apply list_repeat_len.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len.
      rewrite H4. reflexivity.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add (Integers.Int.mul (valueToInt asr # r1) (Integers.Int.repr z))
                                                         (Integers.Int.repr z0)))) as OFFSET.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      erewrite Mem.load_store_same.
      2: { rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      constructor.
      erewrite combine_lookup_second.
      simpl.
      assert (Ple src (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
      apply H0 in H16.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; constructor; invert H16; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.

      assert (4 * ptr / 4 = Integers.Ptrofs.unsigned OFFSET / 4) by (f_equal; assumption).
      rewrite Z.mul_comm in H16.
      rewrite Z_div_mult in H16; try lia.
      replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) in H16 by reflexivity.
      rewrite <- PtrofsExtra.divu_unsigned in H16; unfold_constants; try lia.
      rewrite H16. rewrite EXPR_OK.
      rewrite array_get_error_set_bound.
      reflexivity.
      unfold arr_length, arr_repeat. simpl.
      rewrite list_repeat_len. lia.

      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           rewrite Z2Nat.id in H18; try lia.
           apply Zmult_lt_compat_r with (p := 4) in H18; try lia.
           rewrite ZLib.div_mul_undo in H18; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }

      rewrite <- EXPR_OK.
      rewrite PtrofsExtra.divu_unsigned; auto; try (unfold_constants; lia).
      destruct (ptr ==Z Integers.Ptrofs.unsigned OFFSET / 4).
      apply Z.mul_cancel_r with (p := 4) in e; try lia.
      rewrite ZLib.div_mul_undo in e; try lia.
      rewrite combine_lookup_first.
      eapply H7; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.
      rewrite array_gso.
      unfold array_get_error.
      unfold arr_repeat.
      crush.
      apply list_repeat_lookup.
      lia.
      unfold_constants.
      intro.
      apply Z2Nat.inj_iff in H16; try lia.
      apply Z.div_pos; try lia.
      apply Integers.Ptrofs.unsigned_range.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      unfold arr_stack_based_pointers.
      intros.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      crush.
      erewrite Mem.load_store_same.
      2: { rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      crush.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; try constructor.
      destruct (Archi.ptr64); try discriminate.
      pose proof (RSBP src). rewrite EQ_SRC in H0.
      assumption.

      simpl.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           invert H0.
           apply Zmult_lt_compat_r with (p := 4) in H17; try lia.
           rewrite ZLib.div_mul_undo in H17; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }
      apply ASBP; assumption.

      unfold stack_bounds in *. intros.
      simpl.
      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right. right. simpl.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr; crush; try lia.
           apply ZExtra.mod_0_bounds; crush; try lia. }
      crush.
      exploit (BOUNDS ptr); try lia. intros. crush.
      exploit (BOUNDS ptr v); try lia. intros.
      invert H0.
      match goal with | |- ?x = _ => destruct x eqn:EQ end; try reflexivity.
      assert (Mem.valid_access m AST.Mint32 sp'
                               (Integers.Ptrofs.unsigned
                                  (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                       (Integers.Ptrofs.repr ptr))) Writable).
      { pose proof H1. eapply Mem.store_valid_access_2 in H0.
        exact H0. eapply Mem.store_valid_access_3. eassumption. }
      pose proof (Mem.valid_access_store m AST.Mint32 sp'
                                         (Integers.Ptrofs.unsigned
                                            (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                                 (Integers.Ptrofs.repr ptr))) v).
      apply X in H0. invert H0. congruence.

    + invert MARR. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.
      rewrite ARCHI in H0. crush.

      unfold check_address_parameter_unsigned in *;
      unfold check_address_parameter_signed in *; crush.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      rewrite ZERO in H1. clear ZERO.
      rewrite Integers.Ptrofs.add_zero_l in H1.

      remember i0 as OFFSET.

      (** Modular preservation proof *)
      rename H0 into MOD_PRESERVE.

      (** Write bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as WRITE_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET) (Registers.Regmap.get src rs)); auto.
        crush.
        replace (Integers.Ptrofs.repr 0) with (Integers.Ptrofs.zero) by reflexivity.
        small_tac. }

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      apply assumption_32bit.
      econstructor. econstructor. econstructor.
      eapply Verilog.stmnt_runp_Vnonblock_arr. crush.
      econstructor. econstructor. econstructor. econstructor.

      all: crush.

      (** State Lookup *)
      unfold Verilog.merge_regs.
      crush.
      unfold_merge.
      apply AssocMap.gss.

      (** Match states *)
      rewrite assumption_32bit.
      econstructor; eauto.

      (** Match assocmaps *)
      unfold Verilog.merge_regs. crush. unfold_merge.
      apply regs_lessdef_add_greater.
      unfold Plt; lia.
      assumption.

      (** States well formed *)
      unfold state_st_wf. inversion 1. crush.
      unfold Verilog.merge_regs.
      unfold_merge.
      apply AssocMap.gss.

      (** Equality proof *)
      assert (Z.to_nat
                (Integers.Ptrofs.unsigned
                   (Integers.Ptrofs.divu
                      OFFSET
                      (Integers.Ptrofs.repr 4)))
              =
              valueToNat (ZToValue 32 (Integers.Ptrofs.unsigned OFFSET / 4)))
        as EXPR_OK by admit.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      inversion MASSOC; revert HeqOFFSET; subst; clear MASSOC; intros HeqOFFSET.

      econstructor.
      repeat split; crush.
      unfold HTL.empty_stack.
      crush.
      unfold Verilog.merge_arrs.

      rewrite AssocMap.gcombine.
      2: { reflexivity. }
      unfold Verilog.arr_assocmap_set.
      rewrite AssocMap.gss.
      unfold Verilog.merge_arr.
      rewrite AssocMap.gss.
      setoid_rewrite H5.
      reflexivity.

      rewrite combine_length.
      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      apply list_repeat_len.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len.
      rewrite H4. reflexivity.

      remember i0 as OFFSET.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      erewrite Mem.load_store_same.
      2: { rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      constructor.
      erewrite combine_lookup_second.
      simpl.
      assert (Ple src (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; simpl; auto);
      apply H0 in H8.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; constructor; invert H8; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.

      assert (4 * ptr / 4 = Integers.Ptrofs.unsigned OFFSET / 4) by (f_equal; assumption).
      rewrite Z.mul_comm in H8.
      rewrite Z_div_mult in H8; try lia.
      replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) in H8 by reflexivity.
      rewrite <- PtrofsExtra.divu_unsigned in H8; unfold_constants; try lia.
      rewrite H8. rewrite EXPR_OK.
      rewrite array_get_error_set_bound.
      reflexivity.
      unfold arr_length, arr_repeat. simpl.
      rewrite list_repeat_len. lia.

      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           rewrite Z2Nat.id in H11; try lia.
           apply Zmult_lt_compat_r with (p := 4) in H11; try lia.
           rewrite ZLib.div_mul_undo in H11; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }

      rewrite <- EXPR_OK.
      rewrite PtrofsExtra.divu_unsigned; auto; try (unfold_constants; lia).
      destruct (ptr ==Z Integers.Ptrofs.unsigned OFFSET / 4).
      apply Z.mul_cancel_r with (p := 4) in e; try lia.
      rewrite ZLib.div_mul_undo in e; try lia.
      rewrite combine_lookup_first.
      eapply H7; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.
      rewrite array_gso.
      unfold array_get_error.
      unfold arr_repeat.
      crush.
      apply list_repeat_lookup.
      lia.
      unfold_constants.
      intro.
      apply Z2Nat.inj_iff in H8; try lia.
      apply Z.div_pos; try lia.
      apply Integers.Ptrofs.unsigned_range.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      unfold arr_stack_based_pointers.
      intros.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      crush.
      erewrite Mem.load_store_same.
      2: { rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      crush.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; try constructor.
      destruct (Archi.ptr64); try discriminate.
      pose proof (RSBP src). rewrite EQ_SRC in H0.
      assumption.

      simpl.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           invert H0.
           apply Zmult_lt_compat_r with (p := 4) in H9; try lia.
           rewrite ZLib.div_mul_undo in H9; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }
      apply ASBP; assumption.

      unfold stack_bounds in *. intros.
      simpl.
      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right. right. simpl.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr; crush; try lia.
           apply ZExtra.mod_0_bounds; crush; try lia. }
      crush.
      exploit (BOUNDS ptr); try lia. intros. crush.
      exploit (BOUNDS ptr v); try lia. intros.
      invert H0.
      match goal with | |- ?x = _ => destruct x eqn:EQ end; try reflexivity.
      assert (Mem.valid_access m AST.Mint32 sp'
                               (Integers.Ptrofs.unsigned
                                  (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                       (Integers.Ptrofs.repr ptr))) Writable).
      { pose proof H1. eapply Mem.store_valid_access_2 in H0.
        exact H0. eapply Mem.store_valid_access_3. eassumption. }
      pose proof (Mem.valid_access_store m AST.Mint32 sp'
                                         (Integers.Ptrofs.unsigned
                                            (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                                 (Integers.Ptrofs.repr ptr))) v).
      apply X in H0. invert H0. congruence.*)
  Admitted.
  Hint Resolve transl_istore_correct : htlproof.

  Lemma transl_icond_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (cond : Op.condition) (args : list Registers.reg)
      (ifso ifnot : RTL.node) (b : bool) (pc' : RTL.node),
      (RTL.fn_code f) ! pc = Some (RTL.Icond cond args ifso ifnot) ->
      Op.eval_condition cond (map (fun r : positive => Registers.Regmap.get r rs) args) m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      forall R1 : HTL.state,
        match_states (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states (RTL.State s f sp pc' rs m) R2.
  Proof.
    intros s f sp pc rs m cond args ifso ifnot b pc' H H0 H1 R1 MSTATE.
    inv_state.

    eexists. split. apply Smallstep.plus_one.
    eapply HTL.step_module; eauto.
    inv CONST; assumption.
    inv CONST; assumption.
(*    eapply Verilog.stmnt_runp_Vnonblock_reg with
        (rhsval := if b then posToValue 32 ifso else posToValue 32 ifnot).
    constructor.

    simpl.
    destruct b.
    eapply Verilog.erun_Vternary_true.
    eapply eval_cond_correct; eauto.
    constructor.
    apply boolToValue_ValueToBool.
    eapply Verilog.erun_Vternary_false.
    eapply eval_cond_correct; eauto.
    constructor.
    apply boolToValue_ValueToBool.
    constructor.

    big_tac.

    invert MARR.
    destruct b; rewrite assumption_32bit; big_tac.

    Unshelve.
    constructor.
  Qed.*)
  Admitted.
  Hint Resolve transl_icond_correct : htlproof.

  Lemma transl_ijumptable_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (arg : Registers.reg) (tbl : list RTL.node)
      (n : Integers.Int.int) (pc' : RTL.node),
      (RTL.fn_code f) ! pc = Some (RTL.Ijumptable arg tbl) ->
      Registers.Regmap.get arg rs = Values.Vint n ->
      list_nth_z tbl (Integers.Int.unsigned n) = Some pc' ->
      forall R1 : HTL.state,
        match_states (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states (RTL.State s f sp pc' rs m) R2.
  Proof.
    intros s f sp pc rs m arg tbl n pc' H H0 H1 R1 MSTATE.
  Admitted.
  Hint Resolve transl_ijumptable_correct : htlproof.

  Lemma transl_ireturn_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (stk : Values.block)
      (pc : positive) (rs : RTL.regset) (m : mem) (or : option Registers.reg)
      (m' : mem),
      (RTL.fn_code f) ! pc = Some (RTL.Ireturn or) ->
      Mem.free m stk 0 (RTL.fn_stacksize f) = Some m' ->
      forall R1 : HTL.state,
        match_states (RTL.State s f (Values.Vptr stk Integers.Ptrofs.zero) pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states (RTL.Returnstate s (Registers.regmap_optget or Values.Vundef rs) m') R2.
  Proof.
    intros s f stk pc rs m or m' H H0 R1 MSTATE.
    inv_state.

    - econstructor. split.
      eapply Smallstep.plus_two.

      eapply HTL.step_module; eauto.
      inv CONST; assumption.
      inv CONST; assumption.
      constructor.
      econstructor; simpl; trivial.
      econstructor; simpl; trivial.
      constructor.
      econstructor; simpl; trivial.
      constructor.

      constructor. constructor.

      unfold state_st_wf in WF; big_tac; eauto.
      destruct wf as [HCTRL HDATA]. apply HCTRL.
      apply AssocMapExt.elements_iff. eexists.
      match goal with H: control ! pc = Some _ |- _ => apply H end.

      apply HTL.step_finish.
      unfold Verilog.merge_regs.
      unfold_merge; simpl.
      rewrite AssocMap.gso.
      apply AssocMap.gss. lia.
      apply AssocMap.gss.
      rewrite Events.E0_left. reflexivity.

      constructor; auto.
      constructor.

    (* FIXME: Duplication *)
    - econstructor. split.
      eapply Smallstep.plus_two.
      eapply HTL.step_module; eauto.
      inv CONST; assumption.
      inv CONST; assumption.
      constructor.
      econstructor; simpl; trivial.
      econstructor; simpl; trivial.
      constructor. constructor. constructor.
      constructor. constructor. constructor.

      unfold state_st_wf in WF; big_tac; eauto.

      destruct wf as [HCTRL HDATA]. apply HCTRL.
      apply AssocMapExt.elements_iff. eexists.
      match goal with H: control ! pc = Some _ |- _ => apply H end.

      apply HTL.step_finish.
      unfold Verilog.merge_regs.
      unfold_merge.
      rewrite AssocMap.gso.
      apply AssocMap.gss. simpl; lia.
      apply AssocMap.gss.
      rewrite Events.E0_left. trivial.

      constructor; auto.

      simpl. inversion MASSOC. subst.
      unfold find_assocmap, AssocMapExt.get_default. rewrite AssocMap.gso.
      apply H1. eapply RTL.max_reg_function_use. eauto. simpl; tauto.
      assert (HPle : Ple r (RTL.max_reg_function f)).
      eapply RTL.max_reg_function_use. eassumption. simpl; auto.
      apply ZExtra.Ple_not_eq. apply ZExtra.Ple_Plt_Succ. assumption.

      Unshelve.
      all: constructor.
  Qed.
  Hint Resolve transl_ireturn_correct : htlproof.

  Lemma transl_callstate_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (args : list Values.val)
      (m : mem) (m' : Mem.mem') (stk : Values.block),
      Mem.alloc m 0 (RTL.fn_stacksize f) = (m', stk) ->
      forall R1 : HTL.state,
        match_states (RTL.Callstate s (AST.Internal f) args m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states
            (RTL.State s f (Values.Vptr stk Integers.Ptrofs.zero) (RTL.fn_entrypoint f)
                       (RTL.init_regs args (RTL.fn_params f)) m') R2.
  Proof.
    intros s f args m m' stk H R1 MSTATE.

    inversion MSTATE; subst. inversion TF; subst.
    econstructor. split. apply Smallstep.plus_one.
    eapply HTL.step_call. crush.

    apply match_state with (sp' := stk); eauto.

    all: big_tac.

    apply regs_lessdef_add_greater. unfold Plt; lia.
    apply regs_lessdef_add_greater. unfold Plt; lia.
    apply regs_lessdef_add_greater. unfold Plt; lia.
    apply init_reg_assoc_empty.

    constructor.

    destruct (Mem.load AST.Mint32 m' stk
                       (Integers.Ptrofs.unsigned (Integers.Ptrofs.add
                                                    Integers.Ptrofs.zero
                                                    (Integers.Ptrofs.repr (4 * ptr))))) eqn:LOAD.
    pose proof Mem.load_alloc_same as LOAD_ALLOC.
    pose proof H as ALLOC.
    eapply LOAD_ALLOC in ALLOC.
    2: { exact LOAD. }
    ptrofs. rewrite LOAD.
    rewrite ALLOC.
    repeat constructor.

    ptrofs. rewrite LOAD.
    repeat constructor.

    unfold reg_stack_based_pointers. intros.
    unfold RTL.init_regs; crush.
    destruct (RTL.fn_params f);
    rewrite Registers.Regmap.gi; constructor.

    unfold arr_stack_based_pointers. intros.
    crush.
    destruct (Mem.load AST.Mint32 m' stk
                       (Integers.Ptrofs.unsigned (Integers.Ptrofs.add
                                                    Integers.Ptrofs.zero
                                                    (Integers.Ptrofs.repr (4 * ptr))))) eqn:LOAD.
    pose proof Mem.load_alloc_same as LOAD_ALLOC.
    pose proof H as ALLOC.
    eapply LOAD_ALLOC in ALLOC.
    2: { exact LOAD. }
    rewrite ALLOC.
    repeat constructor.
    constructor.

    Transparent Mem.alloc. (* TODO: Since there are opaque there's probably a lemma. *)
    Transparent Mem.load.
    Transparent Mem.store.
    unfold stack_bounds.
    split.

    unfold Mem.alloc in H.
    invert H.
    crush.
    unfold Mem.load.
    intros.
    match goal with | |- context[if ?x then _ else _] => destruct x end; try congruence.
    invert v0. unfold Mem.range_perm in H4.
    unfold Mem.perm in H4. crush.
    unfold Mem.perm_order' in H4.
    small_tac.
    exploit (H4 ptr). rewrite Integers.Ptrofs.unsigned_repr; small_tac. intros.
    rewrite Maps.PMap.gss in H8.
    match goal with | H8 : context[if ?x then _ else _] |- _ => destruct x eqn:EQ end; try contradiction.
    crush.
    apply proj_sumbool_true in H10. lia.

    unfold Mem.alloc in H.
    invert H.
    crush.
    unfold Mem.store.
    intros.
    match goal with | |- context[if ?x then _ else _] => destruct x end; try congruence.
    invert v0. unfold Mem.range_perm in H4.
    unfold Mem.perm in H4. crush.
    unfold Mem.perm_order' in H4.
    small_tac.
    exploit (H4 ptr). rewrite Integers.Ptrofs.unsigned_repr; small_tac. intros.
    rewrite Maps.PMap.gss in H8.
    match goal with | H8 : context[if ?x then _ else _] |- _ => destruct x eqn:EQ end; try contradiction.
    crush.
    apply proj_sumbool_true in H10. lia.
    constructor. simplify. rewrite AssocMap.gss.
    simplify. rewrite AssocMap.gso. apply AssocMap.gss. simplify. lia.
    Opaque Mem.alloc.
    Opaque Mem.load.
    Opaque Mem.store.
  Qed.
  Hint Resolve transl_callstate_correct : htlproof.

  Lemma transl_returnstate_correct:
    forall (res0 : Registers.reg) (f : RTL.function) (sp : Values.val) (pc : RTL.node)
      (rs : RTL.regset) (s : list RTL.stackframe) (vres : Values.val) (m : mem)
      (R1 : HTL.state),
      match_states (RTL.Returnstate (RTL.Stackframe res0 f sp pc rs :: s) vres m) R1 ->
      exists R2 : HTL.state,
        Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
        match_states (RTL.State s f sp pc (Registers.Regmap.set res0 vres rs) m) R2.
  Proof.
    intros res0 f sp pc rs s vres m R1 MSTATE.
    inversion MSTATE. inversion MF.
  Qed.
  Hint Resolve transl_returnstate_correct : htlproof.

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
    forall s1 : Smallstep.state (RTL.semantics prog),
      Smallstep.initial_state (RTL.semantics prog) s1 ->
      exists s2 : Smallstep.state (HTL.semantics tprog),
        Smallstep.initial_state (HTL.semantics tprog) s2 /\ match_states s1 s2.
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

    constructor.
    apply transl_module_correct.
    assert (Some (AST.Internal x) = Some (AST.Internal m)).
    replace (AST.fundef HTL.module) with (HTL.fundef).
    rewrite <- H6. setoid_rewrite <- A. trivial.
    trivial. inv H7. assumption.
  Qed.
  Hint Resolve transl_initial_states : htlproof.

  Lemma transl_final_states :
    forall (s1 : Smallstep.state (RTL.semantics prog))
           (s2 : Smallstep.state (HTL.semantics tprog))
           (r : Integers.Int.int),
      match_states s1 s2 ->
      Smallstep.final_state (RTL.semantics prog) s1 r ->
      Smallstep.final_state (HTL.semantics tprog) s2 r.
  Proof.
    intros. inv H0. inv H. inv H4. invert MF. constructor. reflexivity.
  Qed.
  Hint Resolve transl_final_states : htlproof.

  Theorem transl_step_correct:
    forall (S1 : RTL.state) t S2,
      RTL.step ge S1 t S2 ->
      forall (R1 : HTL.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus HTL.step tge R1 t R2 /\ match_states S2 R2.
  Proof.
    induction 1; eauto with htlproof; (intros; inv_state).
  Qed.
  Hint Resolve transl_step_correct : htlproof.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog) (HTL.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus; eauto with htlproof.
    apply senv_preserved.
  Qed.

End CORRECTNESS.
