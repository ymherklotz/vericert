 (*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *               2020 James Pollard <j@mes.dev>
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

Require compcert.backend.RTL.
Require compcert.backend.Registers.
Require compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Linking.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import vericert.common.IntegerExtra.
Require Import vericert.common.Vericertlib.
Require Import vericert.common.ZExtra.
Require Import vericert.hls.Array.
Require Import vericert.hls.AssocMap.
Require vericert.hls.HTL.
Require Import vericert.hls.HTLgen.
Require Import vericert.hls.HTLgenspec.
Require Import vericert.hls.ValueInt.
Require vericert.hls.Verilog.

Require Import Lia.

Local Open Scope assocmap.

Hint Resolve Smallstep.forward_simulation_plus : htlproof.
Hint Resolve AssocMap.gss : htlproof.
Hint Resolve AssocMap.gso : htlproof.

Hint Unfold find_assocmap AssocMapExt.get_default : htlproof.

Hint Constructors val_value_lessdef : htlproof.

Inductive match_assocmaps : RTL.function -> RTL.regset -> assocmap -> Prop :=
  match_assocmap : forall f rs am,
    (forall r, Ple r (RTL.max_reg_function f) ->
               val_value_lessdef (Registers.Regmap.get r rs) am#r) ->
    match_assocmaps f rs am.
Hint Constructors match_assocmaps : htlproof.

Definition state_st_wf (m : HTL.module) (s : HTL.state) :=
  forall mid st asa asr res,
  s = HTL.State res mid m st asa asr ->
  asa!(m.(HTL.mod_st)) = Some (posToValue st).
Hint Unfold state_st_wf : htlproof.

Inductive match_arrs (m : HTL.module) (f : RTL.function) (sp : Values.val) (mem : Memory.mem) :
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

Definition not_pointer (v : Values.val) : Prop :=
   match v with
   | Values.Vptr _ _ => False
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

Inductive match_constants : HTL.module -> assocmap -> Prop :=
  match_constant :
    forall m asr,
      asr!(HTL.mod_reset m) = Some (ZToValue 0) ->
      asr!(HTL.mod_finish m) = Some (ZToValue 0) ->
      match_constants m asr.

(** The caller needs to have externctrl signals for the current module *)
Definition has_externctrl (caller : HTL.module) (current_id : HTL.ident) (ret rst fin : HTL.reg) :=
  (HTL.mod_externctrl caller)!ret = Some (current_id, HTL.ctrl_return) /\
  (HTL.mod_externctrl caller)!rst = Some (current_id, HTL.ctrl_reset) /\
  (HTL.mod_externctrl caller)!fin = Some (current_id, HTL.ctrl_finish).

Inductive match_frames (ge : RTL.genv) (current_id : HTL.ident) (mem : Memory.mem)
  : (list RTL.stackframe) -> (list HTL.stackframe) -> Prop :=
| match_frames_nil :
    match_frames ge current_id mem nil nil
| match_frames_cons :
    forall dst f sp sp' rs mid m pc st asr asa rtl_tl htl_tl ret rst fin
      (MASSOC : match_assocmaps f rs asr)
      (TF : tr_module ge f m)
      (MARR : match_arrs m f sp mem asa)
      (SP : sp = Values.Vptr sp' (Integers.Ptrofs.repr 0))
      (RSBP : reg_stack_based_pointers sp' rs)
      (ASBP : arr_stack_based_pointers sp' mem (f.(RTL.fn_stacksize)) sp)
      (BOUNDS : stack_bounds sp (f.(RTL.fn_stacksize)) mem)
      (CONST : match_constants m asr)
      (EXTERN_CALLER : has_externctrl m current_id ret rst fin)
      (JOIN_CTRL : (HTL.mod_controllogic m)!st = Some (state_wait (HTL.mod_st m) fin pc))
      (JOIN_DATA : (HTL.mod_datapath m)!st = Some (join ret rst dst))
      (TAILS : match_frames ge mid mem rtl_tl htl_tl)
      (DST : Ple dst (RTL.max_reg_function f))
      (PC : (Z.pos pc <= Int.max_unsigned)),
      match_frames ge current_id mem
                   ((RTL.Stackframe dst f sp pc rs) :: rtl_tl)
                   ((HTL.Stackframe mid m st asr asa) :: htl_tl).

Inductive match_states (ge : RTL.genv) : RTL.state -> HTL.state -> Prop :=
| match_state : forall asa asr sf f sp sp' rs mem mid m st res
    (MASSOC : match_assocmaps f rs asr)
    (TF : tr_module ge f m)
    (WF : state_st_wf m (HTL.State res mid m st asr asa))
    (MF : match_frames ge mid mem sf res)
    (MARR : match_arrs m f sp mem asa)
    (SP : sp = Values.Vptr sp' (Integers.Ptrofs.repr 0))
    (RSBP : reg_stack_based_pointers sp' rs)
    (ASBP : arr_stack_based_pointers sp' mem (f.(RTL.fn_stacksize)) sp)
    (BOUNDS : stack_bounds sp (f.(RTL.fn_stacksize)) mem)
    (CONST : match_constants m asr),
    match_states ge
                 (RTL.State sf f sp st rs mem)
                 (HTL.State res mid m st asr asa)
| match_returnstate :
    forall v v' rtl_stk htl_stk mem mid
      (MF : match_frames ge mid mem rtl_stk htl_stk)
      (MV : val_value_lessdef v v')
      (NP : not_pointer v),
      match_states ge
                   (RTL.Returnstate rtl_stk v mem)
                   (HTL.Returnstate htl_stk mid v')
| match_call :
    forall f m rtl_args htl_args mid mem rtl_stk htl_stk
    (TF : tr_module ge f m)
    (MF : match_frames ge mid mem rtl_stk htl_stk)
    (NP : Forall not_pointer rtl_args)
    (MARGS : list_forall2 val_value_lessdef rtl_args htl_args),
      match_states ge
                   (RTL.Callstate rtl_stk (AST.Internal f) rtl_args mem)
                   (HTL.Callstate htl_stk mid m htl_args).
Hint Constructors match_states : htlproof.

Definition match_prog (p: RTL.program) (tp: HTL.program) :=
  Linking.match_program (fun cu f tf => transl_fundef p f = Errors.OK tf) eq p tp /\
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
  Linking.match_program (fun cu f tf => transl_fundef p f = Errors.OK tf) eq p tp.

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

Lemma regs_lessdef_empty : forall f, match_assocmaps f (Registers.Regmap.init Values.Vundef) empty_assocmap.
Proof.
  constructor. intros.
  unfold Registers.Regmap.init, "_ !! _", "_ # _", empty_assocmap, AssocMapExt.get_default.
  repeat rewrite PTree.gempty.
  constructor.
Qed.
Hint Resolve regs_lessdef_empty : htlproof.

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

Lemma option_inv :
  forall A x y,
    @Some A x = Some y -> x = y.
Proof. intros. inversion H. trivial. Qed.

Ltac inv_state :=
  match goal with
    MSTATE : match_states _ _ _ |- _ =>
    inversion MSTATE;
    match goal with
      TF : tr_module _ _ _ |- _ =>
      inversion TF;
      match goal with
        TC : forall _ _,
          Maps.PTree.get _ _ = Some _ -> tr_code _ _ _ _ _ _ _ _ _ _ _,
        H : Maps.PTree.get _ _ = Some _ |- _ =>
        apply TC in H; inversion H;
        try match goal with
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

Ltac not_control_reg :=
  solve [
      unfold Ple, Plt in *;
      try multimatch goal with
          | [ H : forall r, (exists x, _ ! r = Some x) -> (_ < r < _)%positive
                       |- context[?r']
            ] => destruct (H r' ltac:(eauto))
          end;
      lia
    ].

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

  Let ge : RTL.genv := Globalenvs.Genv.globalenv prog.
  Let tge : HTL.genv := Globalenvs.Genv.globalenv tprog.

  Hypothesis TRANSL : match_prog prog tprog.

  Axiom no_pointer_return : forall (rs : RTL.regset) r s (f : RTL.function) sp pc rs mem f S,
      (RTL.fn_code f) ! pc = Some (RTL.Ireturn (Some r)) ->
      match_states ge (RTL.State s f sp pc rs mem) S ->
      (not_pointer rs !! r).

  (** The following are assumed to be guaranteed by an inlining pass previous to
      this translation. [ only_main_stores ] should be a direct result of that
      inlining.

      [ no_stack_functions ] and [ no_stack_calls ] might be provable as
      corollaries of [ only_main_stores ]
   *)
  Axiom only_main_stores : forall rtl_stk f sp pc pc' rs mem htl_stk mid m asr asa a b c d,
      match_states ge (RTL.State rtl_stk f sp pc rs mem) (HTL.State htl_stk mid m pc asr asa) ->
      (RTL.fn_code f) ! pc = Some (RTL.Istore a b c d pc') ->
      (rtl_stk = nil /\ htl_stk = nil).

  Axiom no_stack_functions : forall f sp rs mem st rtl_stk S,
      match_states ge (RTL.State rtl_stk f sp st rs mem) S ->
      (RTL.fn_stacksize f) = 0 \/ rtl_stk = nil.

  Axiom no_stack_calls : forall f mem args rtl_stk S,
      match_states ge (RTL.Callstate rtl_stk (AST.Internal f) args mem) S ->
      (RTL.fn_stacksize f) = 0 \/ rtl_stk = nil.

  (** The following admitted lemmas should be provable *)
  Lemma mem_free_zero : forall mem blk, Mem.free mem blk 0 0 = Some mem.
  Admitted.

  Lemma mem_alloc_zero : forall mem, exists blk, Mem.alloc mem 0 0 = (mem, blk).
  Admitted.

  Lemma match_arrs_empty : forall m f sp mem asa,
      match_arrs m f sp mem asa ->
      match_arrs m f sp mem (Verilog.merge_arrs (HTL.empty_stack m) asa).
  Admitted.

  Lemma TRANSL' :
    Linking.match_program (fun cu f tf => transl_fundef prog f = Errors.OK tf) eq prog tprog.
  Proof. intros; apply match_prog_matches; assumption. Qed.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof. intros. eapply (Genv.find_symbol_match TRANSL'). Qed.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: RTL.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef prog f = Errors.OK tf.
  Proof.
    intros. exploit (Genv.find_funct_ptr_match TRANSL'); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: RTL.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef prog f = Errors.OK tf.
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
      | H2 : context[RTL.max_reg_function ?f],
        H : Registers.Regmap.get ?r ?rs = _,
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
              H2 : Registers.Regmap.get ?r ?rs = Values.Vtrue |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vint _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vfalse |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vint _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vptr _ _ |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vundef = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vptr _ _ |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vundef = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vtrue |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vundef = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vfalse |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vptr _ _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vundef |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vptr _ _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vtrue |- _ =>
          rewrite H2 in H; discriminate
        | H : Values.Vptr _ _ = Registers.Regmap.get ?r ?rs,
              H2 : Registers.Regmap.get ?r ?rs = Values.Vfalse |- _ =>
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

  Lemma eval_cond_correct :
    forall stk f sp pc rs mid m res ml st asr asa e b f' s s' args i cond,
      match_states ge (RTL.State stk f sp pc rs m) (HTL.State res mid ml st asr asa) ->
      (forall v, In v args -> Ple v (RTL.max_reg_function f)) ->
      Op.eval_condition cond (map (fun r : positive => Registers.Regmap.get r rs) args) m = Some b ->
      translate_condition cond args s = OK e s' i ->
      Verilog.expr_runp f' asr asa e (boolToValue b).
  Proof.
    intros * MSTATE MAX_FUN EVAL TR_INSTR.
    pose proof MSTATE as MSTATE_2. inv MSTATE.
    inv MASSOC. unfold translate_condition, translate_comparison,
                translate_comparisonu, translate_comparison_imm,
                translate_comparison_immu in TR_INSTR;
                repeat unfold_match TR_INSTR; try inv TR_INSTR; simplify_val;
                unfold Values.Val.cmp_bool, Values.Val.of_optbool, bop, Values.Val.cmpu_bool,
                  Int.cmpu in *;
                repeat unfold_match EVAL.
    - repeat econstructor. repeat unfold_match Heqo. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo; simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; solve_cond.
    - repeat econstructor. repeat unfold_match Heqo; simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; try solve_cond. simplify_val.
      rewrite Heqv0 in H3. rewrite Heqv in H2. inv H2. inv H3.
      unfold Ptrofs.ltu. unfold Int.ltu.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2. auto.
    - repeat econstructor.  unfold Verilog.binop_run.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; simplify_val; solve_cond.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; try solve_cond. simplify_val.
      rewrite Heqv0 in H3. rewrite Heqv in H2. inv H2. inv H3.
      unfold Ptrofs.ltu. unfold Int.ltu.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2. auto.
    - repeat econstructor.  unfold Verilog.binop_run.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; simplify_val; solve_cond.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; try solve_cond. simplify_val.
      rewrite Heqv0 in H3. rewrite Heqv in H2. inv H2. inv H3.
      unfold Ptrofs.ltu. unfold Int.ltu.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2. auto.
    - repeat econstructor.  unfold Verilog.binop_run.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; simplify_val; solve_cond.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      pose proof (MAX_FUN p0) as MAX_FUN_P0. apply H in MAX_FUN_P0; auto.
      inv MAX_FUN_P; inv MAX_FUN_P0; try solve_cond. simplify_val.
      rewrite Heqv0 in H3. rewrite Heqv in H2. inv H2. inv H3.
      unfold Ptrofs.ltu. unfold Int.ltu.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2.
      rewrite Ptrofs.unsigned_repr by apply Int.unsigned_range_2. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
    - repeat econstructor. simplify_val.
      pose proof (MAX_FUN p) as MAX_FUN_P. apply H in MAX_FUN_P; auto.
      inv MAX_FUN_P; simplify_val; try solve_cond.
      rewrite Heqv in H0. inv H0. auto.
  Qed.

  Lemma eval_cond_correct' :
    forall e stk f sp pc rs m res mid ml st asr asa v f' s s' args i cond,
      match_states ge (RTL.State stk f sp pc rs m) (HTL.State res mid ml st asr asa) ->
      (forall v, In v args -> Ple v (RTL.max_reg_function f)) ->
      Values.Val.of_optbool None = v ->
      translate_condition cond args s = OK e s' i ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
    intros * MSTATE MAX_FUN EVAL TR_INSTR.
    unfold translate_condition, translate_comparison, translate_comparisonu,
    translate_comparison_imm, translate_comparison_immu, bop, boplit in *.
    repeat unfold_match TR_INSTR; inv TR_INSTR; repeat econstructor.
  Qed.

  Lemma eval_correct_Oshrximm :
    forall s sp rs m v e asr asa f f' stk s' i pc res0 pc' args res mid ml st n,
      match_states ge (RTL.State stk f sp pc rs m) (HTL.State res mid ml st asr asa) ->
      (RTL.fn_code f) ! pc = Some (RTL.Iop (Op.Oshrximm n) args res0 pc') ->
      Op.eval_operation ge sp (Op.Oshrximm n)
                        (List.map (fun r : BinNums.positive =>
                                     Registers.Regmap.get r rs) args) m = Some v ->
      translate_instr (Op.Oshrximm n) args s = OK e s' i ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
  Proof.
    intros * MSTATE INSTR EVAL TR_INSTR.
    pose proof MSTATE as MSTATE_2. inv MSTATE.
    inv MASSOC. unfold translate_instr in TR_INSTR; repeat (unfold_match TR_INSTR); inv TR_INSTR;
    unfold Op.eval_operation in EVAL; repeat (unfold_match EVAL); inv EVAL.
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
    destruct (zlt (Int.signed i0) 0).
    - repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
      repeat (simplify; eval_correct_tac).
      inv_lessdef. unfold valueToInt in *. rewrite H3 in H1.
      inv H1.
      unfold Int.lt in *. rewrite zlt_true in Heqb0. simplify.
      rewrite Int.unsigned_repr in Heqb0. discriminate.
      simplify; lia.
      unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
      auto.
      rewrite H3 in H1; discriminate.
      rewrite H3 in H2; discriminate.
      rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_true; try lia.
      simplify. inv_lessdef. unfold valueToInt in *.
      rewrite H3 in H1. auto. inv H1. auto.
      rewrite H3 in H1. discriminate.
      rewrite H3 in H2. discriminate.
    - econstructor; econstructor; [eapply Verilog.erun_Vternary_false|idtac]; repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
      repeat (simplify; eval_correct_tac).
      inv_lessdef. unfold valueToInt in *. rewrite H3 in H1.
      inv H1.
      unfold Int.lt in *. rewrite zlt_false in Heqb0. simplify.
      rewrite Int.unsigned_repr in Heqb0. lia.
      simplify; lia.
      unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
      auto.
      rewrite H3 in H1; discriminate.
      rewrite H3 in H2; discriminate.
      rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_false; try lia.
      simplify. inv_lessdef. unfold valueToInt in *.
      rewrite H3 in H1. auto. inv H1. auto.
      rewrite H3 in H1. discriminate.
      rewrite H3 in H2. discriminate.
  Qed.

  Lemma eval_correct :
    forall s sp op rs m v e asr asa f f' stk s' i pc res0 pc' args res mid ml st ,
      match_states ge (RTL.State stk f sp pc rs m) (HTL.State res mid ml st asr asa) ->
      (RTL.fn_code f) ! pc = Some (RTL.Iop op args res0 pc') ->
      Op.eval_operation ge sp op
                        (List.map (fun r : BinNums.positive => Registers.Regmap.get r rs) args) m = Some v ->
      translate_instr op args s = OK e s' i ->
      exists v', Verilog.expr_runp f' asr asa e v' /\ val_value_lessdef v v'.
  Proof.
    intros * MSTATE INSTR EVAL TR_INSTR.
    pose proof MSTATE as MSTATE_2. inv MSTATE.
    inv MASSOC. unfold translate_instr in TR_INSTR; repeat (unfold_match TR_INSTR); inv TR_INSTR;
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
    - assert (Int.unsigned n <= 30).
      { unfold Int.ltu in *. destruct (zlt (Int.unsigned n) (Int.unsigned (Int.repr 31))); try discriminate.
        rewrite Int.unsigned_repr in l by (simplify; lia).
        replace 31 with (Z.succ 30) in l by auto.
        apply Zlt_succ_le in l.
        auto.
      }
      destruct (zlt (Int.signed i0) 0).
      + repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
        repeat (simplify; eval_correct_tac).
        rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_true; try lia.
        simplify. inv_lessdef. unfold valueToInt in *.
        rewrite Heqv0 in H0. auto. inv H0. auto.
        rewrite Heqv0 in H2. discriminate.
        unfold valueToInt in l. auto.
        inv_lessdef. unfold valueToInt in *. rewrite Heqv0 in H0.
        inv H0.
        unfold Int.lt in *. rewrite zlt_true in Heqb0. simplify.
        rewrite Int.unsigned_repr in Heqb0. discriminate.
        simplify; lia.
        unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
        auto.
        rewrite Heqv0 in H0; discriminate.
        rewrite Heqv0 in H2; discriminate.
      + eapply Verilog.erun_Vternary_false; repeat econstructor; unfold valueToBool, boolToValue, uvalueToZ, natToValue;
        repeat (simplify; eval_correct_tac).
        rewrite IntExtra.shrx_shrx_alt_equiv; auto. unfold IntExtra.shrx_alt. rewrite zlt_false; try lia.
        simplify. inv_lessdef. unfold valueToInt in *.
        rewrite Heqv0 in H0. auto. inv H0. auto.
        rewrite Heqv0 in H2. discriminate.
        unfold valueToInt in *. auto.
        inv_lessdef. unfold valueToInt in *.
        rewrite Heqv0 in H0.
        inv H0.
        unfold Int.lt in *. rewrite zlt_false in Heqb0. simplify.
        rewrite Int.unsigned_repr in Heqb0. lia.
        simplify; lia.
        unfold ZToValue. rewrite Int.signed_repr by (simplify; lia).
        auto.
        rewrite Heqv0 in H0; discriminate.
        rewrite Heqv0 in H2; discriminate.
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
    - destruct (Op.eval_condition cond (map (fun r : positive => Registers.Regmap.get r rs) args) m) eqn:EQ.
      + exploit eval_cond_correct; eauto. intros. eapply RTL.max_reg_function_use. apply INSTR. auto.
        intros. econstructor. econstructor. eassumption. unfold boolToValue, Values.Val.of_optbool.
        destruct b; constructor; auto.
      + eapply eval_cond_correct'; eauto. intros. eapply RTL.max_reg_function_use. apply INSTR. auto.
    - monadInv H1.
      destruct (Op.eval_condition c (map (fun r1 : positive => Registers.Regmap.get r1 rs) l0) m) eqn:EQN;
      simplify. destruct b eqn:B.
      + exploit eval_cond_correct; eauto. intros. eapply RTL.max_reg_function_use. apply INSTR.
        simplify; tauto. intros.
        econstructor. econstructor. eapply Verilog.erun_Vternary_true. eassumption. econstructor. auto.
        auto. unfold Values.Val.normalize.
        destruct (Registers.Regmap.get r rs) eqn:EQN2; constructor.
        * assert (HPle1 : Ple r (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
          apply H in HPle1. inv HPle1. unfold valueToInt in H1. rewrite EQN2 in H1. inv H1. auto.
          rewrite EQN2 in H1. discriminate. rewrite EQN2 in H2. discriminate.
        * assert (HPle1 : Ple r (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
          apply H in HPle1. inv HPle1. rewrite EQN2 in H1. inv H1. rewrite EQN2 in H1. inv H1. auto.
          rewrite EQN2 in H2. discriminate.
      + exploit eval_cond_correct; eauto. intros. eapply RTL.max_reg_function_use. apply INSTR.
        simplify; tauto. intros.
        econstructor. econstructor. eapply Verilog.erun_Vternary_false. eassumption. econstructor. auto.
        auto. unfold Values.Val.normalize.
        destruct (Registers.Regmap.get r0 rs) eqn:EQN2; constructor.
        * assert (HPle1 : Ple r0 (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
          apply H in HPle1. inv HPle1. unfold valueToInt in H1. rewrite EQN2 in H1. inv H1. auto.
          rewrite EQN2 in H1. discriminate. rewrite EQN2 in H2. discriminate.
        * assert (HPle1 : Ple r0 (RTL.max_reg_function f)) by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
          apply H in HPle1. inv HPle1. rewrite EQN2 in H1. inv H1. rewrite EQN2 in H1. inv H1. auto.
          rewrite EQN2 in H2. discriminate.
      + exploit eval_cond_correct'; eauto. intros. eapply RTL.max_reg_function_use. apply INSTR.
        simplify; tauto. intros. inv H0. inv H1. destruct (Int.eq_dec x0 Int.zero).
        econstructor. econstructor. eapply Verilog.erun_Vternary_false.
        eassumption. econstructor. auto. subst. auto. constructor.
        econstructor. econstructor. eapply Verilog.erun_Vternary_true.
        eassumption. econstructor. auto. unfold valueToBool. pose proof n. apply Int.eq_false in n.
        unfold uvalueToZ. unfold Int.eq in n. unfold zeq in *.
        destruct (Int.unsigned x0 ==Z Int.unsigned Int.zero); try discriminate.
        rewrite <- Z.eqb_neq in n0. rewrite Int.unsigned_zero in n0. rewrite n0. auto.
        constructor.
  Qed.

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
    forall mid m asr asa fin rtrn st stmt trans res,
      tr_instr fin rtrn st (m.(HTL.mod_stk)) instr stmt trans ->
      exists asr' asa',
        HTL.step tge (HTL.State res mid m st asr asa) Events.E0 (HTL.State res mid m st asr' asa').

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
      let EQ := fresh "EQ" in
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
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states ge (RTL.State s f sp pc' rs m) R2.
  Proof.
    intros * H R1 MSTATE.
    inv_state.

    unfold match_prog in TRANSL.
    eexists.
    split.
    - apply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
      + inv CONST; assumption.
      + inv CONST; assumption.
      + repeat constructor.
      + repeat constructor.
      + big_tac.
    - inv CONST. inv MARR. simplify. big_tac.
      constructor; rewrite AssocMap.gso; crush.
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
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states ge (RTL.State s f sp pc' (Registers.Regmap.set res0 v rs) m) R2.
  Proof.
    intros * H H0 R1 MSTATE.
    inv_state. inv MARR.
    exploit eval_correct; eauto. intros. inversion H1. inversion H2.
    eexists. split.
    apply Smallstep.plus_one.
    eapply HTL.step_module; eauto.
    - inv CONST. assumption.
    - inv CONST. assumption.
    - repeat econstructor.
    - repeat econstructor. intuition eauto.
    - big_tac.
      assert (Ple res0 (RTL.max_reg_function f))
        by eauto using RTL.max_reg_function_def.
      xomega.
    - big_tac.
      + apply regs_lessdef_add_match. assumption.
        apply regs_lessdef_add_greater. unfold Plt; lia. assumption.
      + assert (HPle: Ple res0 (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
        unfold Ple in HPle; lia.
      + eapply op_stack_based; eauto.
      + inv CONST. constructor; simplify.
        * rewrite AssocMap.gso. rewrite AssocMap.gso.
          assumption. lia.
          assert (HPle: Ple res0 (RTL.max_reg_function f))
            by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
          unfold Ple in HPle. lia.
        * rewrite AssocMap.gso. rewrite AssocMap.gso.
          assumption. lia.
          assert (HPle: Ple res0 (RTL.max_reg_function f))
            by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
          unfold Ple in HPle. lia.
      Unshelve. exact tt.
  Qed.
  Hint Resolve transl_iop_correct : htlproof.

  Lemma match_args : forall rtl_args htl_args params f,
      list_forall2 val_value_lessdef rtl_args htl_args ->
      match_assocmaps f (RTL.init_regs rtl_args params) (HTL.init_regs htl_args params).
  Proof.
    induction rtl_args; intros * H; inv H.
    - destruct params; eauto with htlproof.
    - destruct params; eauto using regs_lessdef_add_match with htlproof.
  Qed.

  Lemma stack_based_set : forall sp r v rs,
      stack_based v sp ->
      reg_stack_based_pointers sp rs ->
      reg_stack_based_pointers sp (Registers.Regmap.set r v rs).
  Proof.
    unfold reg_stack_based_pointers, Registers.Regmap.set, "_ !! _".
    intros * ? ? r0.
    simpl.
    destruct (peq r r0); subst.
    - rewrite AssocMap.gss; auto.
    - rewrite AssocMap.gso; auto.
  Qed.

  Lemma stack_based_non_pointers : forall args params stk,
      Forall not_pointer args ->
      reg_stack_based_pointers stk (RTL.init_regs args params).
  Proof.
    unfold reg_stack_based_pointers.
    induction args; intros * NP *.
    + destruct params;
      simpl;
      unfold "_ !! _";
      rewrite PTree.gempty;
      crush.
    + destruct params; simpl.
      * unfold "_ !! _". rewrite PTree.gempty. crush.
      * inv NP.
        apply stack_based_set;
        [ destruct a; crush
        | unfold reg_stack_based_pointers; auto
        ].
  Qed.

  Lemma transl_callstate_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (args : list Values.val)
      (m : mem) (m' : Mem.mem') (stk : Values.block),
      Mem.alloc m 0 (RTL.fn_stacksize f) = (m', stk) ->
      forall R1 : HTL.state,
        match_states ge (RTL.Callstate s (AST.Internal f) args m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states ge
            (RTL.State s f (Values.Vptr stk Integers.Ptrofs.zero) (RTL.fn_entrypoint f)
                       (RTL.init_regs args (RTL.fn_params f)) m') R2.
  Proof.
    intros * ? * MSTATE.
    inversion MSTATE.
    inversion TF.
    simplify.
    eexists. split.
    apply Smallstep.plus_one. constructor.

    simplify.
    econstructor; try solve [big_tac].
    - repeat apply regs_lessdef_add_greater; try not_control_reg.
      eauto using match_args.
    - edestruct no_stack_calls; eauto.
      + replace (RTL.fn_stacksize f) with 0 in *
          by assumption.
        replace m' with m
          by (destruct (mem_alloc_zero m); crush).
        assumption.
      + subst. inv MF. constructor.
    - big_tac.
      admit.
    - eauto using stack_based_non_pointers.
    - (* Stack based stack pointer *)
      unfold arr_stack_based_pointers; intros.
      admit.
    - (* Stack bounds *)
      admit.
    - constructor; simplify.
      + rewrite AssocMap.gss; crush.
      + rewrite AssocMap.gso by not_control_reg.
        rewrite AssocMap.gss. crush.
  Admitted.
  Hint Resolve transl_callstate_correct : htlproof.

  Lemma only_internal_calls : forall fd fn rs,
      RTL.find_function ge (inr fn) rs = Some fd ->
      (exists f : RTL.function, rtl_find_func ge fn = Some (AST.Internal f)) ->
      (exists f, fd = AST.Internal f).
  Proof.
    intros * ? [? ?].
    unfold rtl_find_func in *.
    unfold RTL.find_function in *.
    destruct (Genv.find_symbol ge fn); try discriminate.
    exists x. crush.
  Qed.

  Fixpoint assign_all acc (rs : list reg) (vals : list value) :=
    match rs, vals with
    | r::rs', val::vals' => assign_all (acc # r <- val) rs' vals'
    | _, _ => acc
    end.

  Notation "a ## b '<-' c" := (assign_all a b c) (at level 1, b at next level) : assocmap.

  Lemma assign_all_nil : forall a rs, a ## rs <- nil = a.
  Proof. destruct rs; crush. Qed.

  Lemma assign_all_out : forall rs vs a r, (forall v, ~ In (r, v) (List.combine rs vs)) -> (a ## rs <- vs) ! r = a ! r.
  Proof.
    induction rs; intros * H.
    - trivial.
    - destruct vs.
      + rewrite assign_all_nil.
        trivial.
      + simpl.
        rewrite IHrs.
        rewrite AssocMap.gso.
        crush.
        * simpl (List.combine _ _) in *.
          specialize (H v).
          rewrite not_in_cons in H.
          inv H.
          crush.
        * intros v0.
          specialize (H v0).
          simpl (List.combine _ _) in *.
          rewrite not_in_cons in H.
          crush.
  Qed.

  Lemma nonblock_all_exec : forall from_regs to_regs f basr nasr basa nasa,
      Verilog.stmnt_runp
        f
        {| Verilog.assoc_blocking := basr; Verilog.assoc_nonblocking := nasr |}
        {| Verilog.assoc_blocking := basa; Verilog.assoc_nonblocking := nasa |}
        (nonblock_all (List.combine to_regs from_regs))
        {| Verilog.assoc_blocking := basr; Verilog.assoc_nonblocking := nasr ## to_regs <- (basr##from_regs) |}
        {| Verilog.assoc_blocking := basa; Verilog.assoc_nonblocking := nasa |}.
  Proof.
    induction from_regs; intros.
    - rewrite combine_nil, assign_all_nil.
      constructor.
    - destruct to_regs; try solve [ constructor ].
      simpl.
      econstructor.
      + repeat econstructor.
      + eapply IHfrom_regs.
  Qed.

  Lemma fork_exec : forall f basr nasr basa nasa rst to_regs from_regs,
      Verilog.stmnt_runp
        f
        {| Verilog.assoc_blocking := basr; Verilog.assoc_nonblocking := nasr |}
        {| Verilog.assoc_blocking := basa; Verilog.assoc_nonblocking := nasa |}
        (fork rst (List.combine to_regs from_regs))
        {| Verilog.assoc_blocking := basr; Verilog.assoc_nonblocking := (nasr # rst <- (ZToValue 1)) ## to_regs <- (basr##from_regs) |}
        {| Verilog.assoc_blocking := basa; Verilog.assoc_nonblocking := nasa |}.
  Proof.
    intros.
    unfold fork.
    econstructor.
    - repeat econstructor.
    - unfold Verilog.nonblock_reg; simpl.
      eapply nonblock_all_exec.
  Qed.

  Lemma transl_icall_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val)
      (pc : positive) (rs : RTL.regset) (m : mem) sig fn fd args dst pc',
      (RTL.fn_code f) ! pc = Some (RTL.Icall sig fn args dst pc') ->
      RTL.find_function ge fn rs = Some fd ->
      forall R1 : HTL.state,
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states ge (RTL.Callstate (RTL.Stackframe dst f sp pc' rs :: s) fd
                                         (List.map (fun r => Registers.Regmap.get r rs) args) m)
                       R2.
  Proof.
    intros * H Hfunc * MSTATE.
    inv_state.
    edestruct (only_internal_calls fd); eauto; subst fd.
    simpl in *.
    eexists. split.
    - inv CONST.
      simplify.
      eapply Smallstep.plus_three; simpl in *.
      + eapply HTL.step_module; simpl.
        * repeat econstructor; auto.
        * repeat econstructor; auto.
        * repeat econstructor; eauto.
        * repeat econstructor; eauto.
        * repeat econstructor; eauto.
        * repeat econstructor; auto.
        * repeat econstructor; eauto.
        * eapply fork_exec.
        * trivial.
        * trivial.
        * eapply AssocMapExt.merge_correct_1.
          rewrite assign_all_out.
          big_tac.
          -- not_control_reg.
          -- simpl.
             insterU H6.
             simplify.
             admit.
        * admit.
      + eapply HTL.step_module; trivial.
        * simpl.
          apply AssocMapExt.merge_correct_2; auto.
          rewrite assign_all_out by admit.
          rewrite AssocMap.gso by not_control_reg.
          rewrite AssocMap.gso by lia.
          apply AssocMap.gempty.
        * simpl.
          apply AssocMapExt.merge_correct_2; auto.
          rewrite assign_all_out by admit.
          rewrite AssocMap.gso by not_control_reg.
          rewrite AssocMap.gso by lia.
          apply AssocMap.gempty.
        * simpl.
          apply AssocMapExt.merge_correct_1; auto.
          rewrite assign_all_out by admit.
          rewrite AssocMap.gso by not_control_reg.
          apply AssocMap.gss.
        * eauto.
        * eauto.
        * unfold state_wait.
          eapply Verilog.stmnt_runp_Vcond_false.
          -- simpl. econstructor; econstructor; simpl.
             replace (Verilog.merge_regs ((empty_assocmap # st1 <- (posToValue x0)) # x1 <- (ZToValue 1)) ## x4 <- (asr ## args) asr) # x3
               with (ZToValue 0) by admit.
             trivial.
          -- auto.
          -- econstructor.
        * simpl.
          apply AssocMapExt.merge_correct_1; auto.
          rewrite assign_all_out by admit.
          rewrite AssocMap.gso by not_control_reg.
          apply AssocMap.gss.
        * repeat econstructor.
        * simpl.
          apply AssocMapExt.merge_correct_2.
          big_tac.
          apply AssocMap.gempty.
          not_control_reg.
          assert (Ple dst (RTL.max_reg_function f))
                 by eauto using RTL.max_reg_function_def.
          xomega.
          apply AssocMapExt.merge_correct_1.
          rewrite assign_all_out by admit.
          rewrite AssocMap.gso by not_control_reg.
          apply AssocMap.gss.
        * admit.
      + eapply HTL.step_initcall.
        * (* find called module *) admit.
        * (* callee reset mapped *) admit.
        * (* params mapped *) admit.
        * (* callee reset unset *) admit.
        * (* params set *) admit.
      + eauto with htlproof.
    - econstructor; try solve [repeat econstructor; eauto with htlproof ].
      + (* Called module is translated *) admit.
      + (* Match stackframes *) admit.
      + (* Argument values match *) admit.
  Admitted.
  Hint Resolve transl_icall_correct : htlproof.
  Close Scope rtl.

  Lemma return_val_exec_spec : forall f or asr asa,
      Verilog.expr_runp f asr asa (return_val or)
                        (match or with
                         | Some r => asr#r
                         | None => ZToValue 0
                         end).
  Proof. destruct or; repeat econstructor. Qed.

  Lemma transl_ireturn_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (stk : Values.block)
      (pc : positive) (rs : RTL.regset) (m : mem) (or : option Registers.reg)
      (m' : mem),
      (RTL.fn_code f) ! pc = Some (RTL.Ireturn or) ->
      Mem.free m stk 0 (RTL.fn_stacksize f) = Some m' ->
      forall R1 : HTL.state,
        match_states ge (RTL.State s f (Values.Vptr stk Integers.Ptrofs.zero) pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states ge (RTL.Returnstate s (Registers.regmap_optget or Values.Vundef rs) m') R2.
  Proof.
    intros * H H0 * MSTATE.
    inv_state.
    inv CONST. simplify.
    eexists. split.
    - eapply Smallstep.plus_two.
      + eapply HTL.step_module; try solve [ repeat econstructor; eauto ].
        * repeat econstructor. apply return_val_exec_spec.
        * big_tac.
        * inversion wf.
          eapply H10.
          eapply AssocMapExt.elements_iff.
          eauto.
      + eapply HTL.step_finish; big_tac.
      + eauto with htlproof.
   - constructor; eauto with htlproof.
     + edestruct no_stack_functions; eauto.
       * replace (RTL.fn_stacksize f) in *.
         replace m' with m by
             (pose proof (mem_free_zero m ltac:(auto)); crush).
         subst.
         assumption.
       * subst. inv MF. constructor.
     + destruct or.
       * rewrite fso. (* Return value is not fin *)
         {
           big_tac.
           inv MASSOC.
           apply H10.
           eapply RTL.max_reg_function_use.
           simpl; eauto.
           simpl; eauto.
         }
         assert (Ple r (RTL.max_reg_function f))
           by (eapply RTL.max_reg_function_use; eauto; crush).
         xomega.
       * simpl. eauto with htlproof.
     + destruct or; simpl; eauto using no_pointer_return.
  Unshelve. try exact tt; eauto.
  Qed.
  Hint Resolve transl_ireturn_correct : htlproof.

  Lemma transl_returnstate_correct:
    forall (res0 : Registers.reg) (f : RTL.function) (sp : Values.val) (pc : RTL.node)
      (rs : RTL.regset) (s : list RTL.stackframe) (vres : Values.val) (m : mem)
      (R1 : HTL.state),
      match_states ge (RTL.Returnstate (RTL.Stackframe res0 f sp pc rs :: s) vres m) R1 ->
      exists R2 : HTL.state,
        Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
        match_states ge (RTL.State s f sp pc (Registers.Regmap.set res0 vres rs) m) R2.
  Proof.
    intros * MSTATE.
    inv MSTATE.
    inversion MF.
    inversion EXTERN_CALLER.
    simplify.
    eexists; split.
    - eapply Smallstep.plus_two.
      + (* Return to caller *)
        repeat econstructor; eauto.
      + (* Join *)
        inv CONST.
        econstructor; eauto.
        * big_tac; inv TF; simplify; not_control_reg.
        * big_tac; inv TF; simplify; not_control_reg.
        * big_tac; inv TF; simplify; not_control_reg.
        * (* control logic *)
          repeat econstructor. big_tac. simpl.
          rewrite fso by crush.
          rewrite fss. crush.
        * big_tac; inv TF; simplify; not_control_reg.
        * repeat econstructor.
        * big_tac; inv TF; simplify; not_control_reg.
      + eauto with htlproof.
    - simpl.
      eapply match_state; simpl; eauto.
      + big_tac.
        inv TF. simplify.
        eapply regs_lessdef_add_match. rewrite fss; eauto.
        repeat eapply regs_lessdef_add_greater; eauto; not_control_reg.
      + unfold state_st_wf.
        intros * Hwf.
        inv Hwf.
        inv TF.
        big_tac.
        not_control_reg.
      + auto using match_arrs_empty.
      + eapply stack_based_set; eauto.
        unfold not_pointer in *.
        destruct vres; crush.
      + (* match_constants *)
        inv CONST.
        inv TF.
        big_tac.
        constructor.
        * simplify.
          rewrite AssocMap.fss.
          repeat rewrite AssocMap.gso; auto; not_control_reg.
        * simplify.
          repeat rewrite AssocMap.gso; auto; not_control_reg.
      Unshelve. all: try exact tt; eauto.
  Qed.
  Hint Resolve transl_returnstate_correct : htlproof.

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

  Lemma transl_iload_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (chunk : AST.memory_chunk)
      (addr : Op.addressing) (args : list Registers.reg) (dst : Registers.reg)
      (pc' : RTL.node) (a v : Values.val),
      (RTL.fn_code f) ! pc = Some (RTL.Iload chunk addr args dst pc') ->
      Op.eval_addressing ge sp addr (map (fun r : positive => Registers.Regmap.get r rs) args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      forall R1 : HTL.state,
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\
          match_states ge (RTL.State s f sp pc' (Registers.Regmap.set dst v rs) m) R2.
  Proof.
    intros s f sp pc rs m chunk addr args dst pc' a v H H0 H1 R1 MSTATE.
    inv_state.

    inv_arr_access.

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
      econstructor. econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor.

      all: big_tac.

      1: {
        assert (HPle : (dst <= (RTL.max_reg_function f))%positive)
               by (eapply RTL.max_reg_function_def; eauto).
        lia.
      }

      2: {
        assert (HPle : (dst <= (RTL.max_reg_function f))%positive)
               by (eapply RTL.max_reg_function_def; eauto).
        lia.
      }

      (** Match assocmaps *)
      apply regs_lessdef_add_match; big_tac.

      (** Equality proof *)
      rewrite <- offset_expr_ok.

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
      match goal with
      | [ H: context[stack_based] |- _ ] => rewrite NORMALISE in H; rewrite HeqOFFSET in H; rewrite H1 in H
      end.
      assumption.
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
      rewrite EQr1 in H22.
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
        apply Zdivide_mod. unfold valueToPtr in *. unfold uvalueToZ in *. unfold Ptrofs.of_int in *. unfold valueToInt in *.
        inversion H22. subst. assumption. }

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
        unfold Integers.Ptrofs.divu at 2 in H14.
        rewrite H14. clear H14.
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
      econstructor. econstructor. econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor. crush.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. auto. econstructor.
      econstructor. econstructor. econstructor.
      all: big_tac.

      1: {
        assert (HPle : Ple dst (RTL.max_reg_function f))
               by (eapply RTL.max_reg_function_def; eauto).
        rewrite Pcompare_eq_Gt in *.
        xomega.
      }

      2: {
        assert (HPle : Ple dst (RTL.max_reg_function f))
               by (eapply RTL.max_reg_function_def; eauto).
        rewrite Pcompare_eq_Gt in *.
        xomega.
      }

      (** Match assocmaps *)
      apply regs_lessdef_add_match; big_tac.

      (** Equality proof *)
      rewrite <- offset_expr_ok_2.

      specialize (H9 (Integers.Ptrofs.unsigned
                        (Integers.Ptrofs.divu
                           OFFSET
                           (Integers.Ptrofs.repr 4)))).
      exploit H9; big_tac.

      (* This should have been solved somewhere above here *)
      match goal with
      | [ |- match_assocmaps _ _ _ ] => admit
      end.

      (** RSBP preservation *)
      unfold arr_stack_based_pointers in ASBP.
      specialize (ASBP (Integers.Ptrofs.unsigned
                          (Integers.Ptrofs.divu OFFSET (Integers.Ptrofs.repr 4)))).
      exploit ASBP; big_tac.
      rewrite NORMALISE in H14. rewrite HeqOFFSET in H14.
      inversion H22. replace (asr # r1) in *. rewrite H1 in *. assumption.

      rewrite Pcompare_eq_Gt in *.
      constructor; simplify. rewrite AssocMap.gso. rewrite AssocMap.gso.
      assumption. lia.
      assert (HPle: Ple dst (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto).
      xomega.
      rewrite AssocMap.gso. rewrite AssocMap.gso.
      assumption. lia.
      assert (HPle: Ple dst (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_def; eauto; simpl; auto).
      xomega.

    + invert MARR. inv CONST. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.
      rewrite ARCHI in H0. crush.

      unfold check_address_parameter_unsigned in *;
      unfold check_address_parameter_signed in *; crush.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      rewrite ZERO in H1. clear ZERO.
      rewrite Integers.Ptrofs.add_zero_l in H1.

      remember i as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { apply Mem.load_valid_access in H1. unfold Mem.valid_access in *. simplify.
        apply Zdivide_mod. assumption. }

      (** Read bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as READ_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:?EQ; crush; auto.
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
      repeat econstructor. crush.
      repeat econstructor. crush.

      all: big_tac.

      1: {
        assert (HPle : Ple dst (RTL.max_reg_function f)) by (eauto using RTL.max_reg_function_def).
        xomega.
      }

      2: {
        assert (HPle : Ple dst (RTL.max_reg_function f)) by (eauto using RTL.max_reg_function_def).
        xomega.
      }

      (** Match assocmaps *)
      apply regs_lessdef_add_match; big_tac.

      (** Equality proof *)
      rewrite <- offset_expr_ok_3.

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

      Unshelve.
      all: try (exact tt); auto.
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
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states ge (RTL.State s f sp pc' rs m') R2.
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

      edestruct only_main_stores; eauto; subst; constructor.

      (** Equality proof *)

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
      apply H11 in HPle.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; constructor; invert HPle; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.

      assert (HMul : 4 * ptr / 4 = Integers.Ptrofs.unsigned OFFSET / 4) by (f_equal; assumption).
      rewrite Z.mul_comm in HMul.
      rewrite Z_div_mult in HMul; try lia.
      replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) in HMul by reflexivity.
      rewrite <- PtrofsExtra.divu_unsigned in HMul; unfold_constants; try lia.
      rewrite HMul. rewrite <- offset_expr_ok.
      rewrite HeqOFFSET.
      rewrite array_get_error_set_bound.
      reflexivity.
      unfold arr_length, arr_repeat. simpl.
      rewrite list_repeat_len. rewrite HeqOFFSET in HMul. lia.

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
           rewrite Z2Nat.id in *; try lia.
           apply Zmult_lt_compat_r with (p := 4) in H27; try lia.
           rewrite ZLib.div_mul_undo in *; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }

      rewrite <- offset_expr_ok.
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
      apply Z2Nat.inj_iff in H13; rewrite HeqOFFSET in n0; try lia.
      apply Z.div_pos; try lia.
      apply Integers.Ptrofs.unsigned_range.
      apply Integers.Ptrofs.unsigned_range_2.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO1 by reflexivity.
      unfold arr_stack_based_pointers.
      intros.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      crush.
      erewrite Mem.load_store_same.
      2: { rewrite ZERO1.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      crush.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; try constructor.
      destruct (Archi.ptr64); try discriminate.
      pose proof (RSBP src). rewrite EQ_SRC in H11.
      assumption.

      simpl.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO1.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           rewrite HeqOFFSET in *. simplify_val.
           left; auto.
           rewrite HeqOFFSET in *. simplify_val.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           invert H11.
           apply Zmult_lt_compat_r with (p := 4) in H22; try lia.
           rewrite ZLib.div_mul_undo in *; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }
      apply ASBP; assumption.

      unfold stack_bounds in *. intros.
      simpl.
      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { rewrite HeqOFFSET in *. simplify_val.
        right. right. simpl.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr; crush; try lia.
           apply ZExtra.mod_0_bounds; crush; try lia. }
      crush.
      exploit (BOUNDS ptr); try lia. intros. crush.
      exploit (BOUNDS ptr v); try lia. intros.
      invert H11.
      match goal with | |- ?x = _ => destruct x eqn:EQ end; try reflexivity.
      assert (Mem.valid_access m AST.Mint32 sp'
                               (Integers.Ptrofs.unsigned
                                  (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                       (Integers.Ptrofs.repr ptr))) Writable).
      { pose proof H1. eapply Mem.store_valid_access_2 in H11.
        exact H11. eapply Mem.store_valid_access_3. eassumption. }
      pose proof (Mem.valid_access_store m AST.Mint32 sp'
                                         (Integers.Ptrofs.unsigned
                                            (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                                 (Integers.Ptrofs.repr ptr))) v).
      apply X in H11. invert H11. congruence.

      constructor; simplify. unfold Verilog.merge_regs. unfold_merge.
      rewrite AssocMap.gso.
      assumption. lia.
      unfold Verilog.merge_regs. unfold_merge.
      rewrite AssocMap.gso.
      assumption. lia.

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
      rewrite EQr1 in H22.
      invert H13. invert H22.
      clear H0. clear H8. clear H11.

      unfold check_address_parameter_signed in *;
      unfold check_address_parameter_unsigned in *; crush.

      remember (Integers.Ptrofs.add (Integers.Ptrofs.repr (uvalueToZ asr # r0))
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add (Integers.Int.mul (valueToInt asr # r1) (Integers.Int.repr z))
                                                         (Integers.Int.repr z0)))) as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { apply Mem.store_valid_access_3 in H1. unfold Mem.valid_access in *. simplify.
        apply Zdivide_mod. assumption. }

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
      econstructor. econstructor. econstructor.
      eapply Verilog.stmnt_runp_Vnonblock_arr. crush.
      econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor.
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

      edestruct only_main_stores; eauto; subst; constructor.

      (** Equality proof *)
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
                                    (Integers.Ptrofs.of_int
                                       (Integers.Int.add (Integers.Int.mul (valueToInt asr # r1) (Integers.Int.repr z))
                                                         (Integers.Int.repr z0)))) as OFFSET.
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
      simpl.
      assert (Ple src (RTL.max_reg_function f))
        by (eapply RTL.max_reg_function_use; eauto; simpl; auto).
      apply H22 in H27.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; constructor; invert H27; eauto.

      rewrite <- array_set_len.
      unfold arr_repeat. crush.
      rewrite list_repeat_len. auto.

      assert (4 * ptr / 4 = Integers.Ptrofs.unsigned OFFSET / 4) by (f_equal; assumption).
      rewrite Z.mul_comm in H27.
      rewrite Z_div_mult in H27; try lia.
      replace 4 with (Integers.Ptrofs.unsigned (Integers.Ptrofs.repr 4)) in H27 by reflexivity.
      rewrite <- PtrofsExtra.divu_unsigned in H27; unfold_constants; try lia.
      rewrite H27. rewrite <- offset_expr_ok_2.
      rewrite HeqOFFSET in *.
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
           rewrite HeqOFFSET in *. simplify_val.
           left; auto.
           rewrite HeqOFFSET in *. simplify_val.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           rewrite Z2Nat.id in *; try lia.
           apply Zmult_lt_compat_r with (p := 4) in H29; try lia.
           rewrite ZLib.div_mul_undo in H29; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }

      rewrite <- offset_expr_ok_2.
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
      rewrite HeqOFFSET in *.
      apply Z2Nat.inj_iff in H27; try lia.
      apply Z.div_pos; try lia.
      apply Integers.Ptrofs.unsigned_range.
      apply Integers.Ptrofs.unsigned_range_2.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO1 by reflexivity.
      unfold arr_stack_based_pointers.
      intros.
      destruct (4 * ptr ==Z Integers.Ptrofs.unsigned OFFSET).

      crush.
      erewrite Mem.load_store_same.
      2: { rewrite ZERO1.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite e.
           rewrite Integers.Ptrofs.unsigned_repr.
           exact H1.
           apply Integers.Ptrofs.unsigned_range_2. }
      crush.
      destruct (Registers.Regmap.get src rs) eqn:EQ_SRC; try constructor.
      destruct (Archi.ptr64); try discriminate.
      pose proof (RSBP src). rewrite EQ_SRC in H22.
      assumption.

      simpl.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { right.
           rewrite ZERO1.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr.
           simpl.
           destruct (Z_le_gt_dec (4 * ptr + 4) (Integers.Ptrofs.unsigned OFFSET)); eauto.
           rewrite HeqOFFSET in *. simplify_val.
           left; auto.
           rewrite HeqOFFSET in *. simplify_val.
           right.
           apply ZExtra.mod_0_bounds; try lia.
           apply ZLib.Z_mod_mult'.
           invert H22.
           apply Zmult_lt_compat_r with (p := 4) in H28; try lia.
           rewrite ZLib.div_mul_undo in H28; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }
      apply ASBP; assumption.

      unfold stack_bounds in *. intros.
      simpl.
      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      erewrite Mem.load_store_other with (m1 := m).
      2: { exact H1. }
      2: { rewrite HeqOFFSET in *. simplify_val.
           right. right. simpl.
           rewrite ZERO.
           rewrite Integers.Ptrofs.add_zero_l.
           rewrite Integers.Ptrofs.unsigned_repr; crush; try lia.
           apply ZExtra.mod_0_bounds; crush; try lia. }
      crush.
      exploit (BOUNDS ptr); try lia. intros. crush.
      exploit (BOUNDS ptr v); try lia. intros.
      simplify.
      match goal with | |- ?x = _ => destruct x eqn:EQ end; try reflexivity.
      assert (Mem.valid_access m AST.Mint32 sp'
                               (Integers.Ptrofs.unsigned
                                  (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                       (Integers.Ptrofs.repr ptr))) Writable).
      { pose proof H1. eapply Mem.store_valid_access_2 in H22.
        exact H22. eapply Mem.store_valid_access_3. eassumption. }
      pose proof (Mem.valid_access_store m AST.Mint32 sp'
                                         (Integers.Ptrofs.unsigned
                                            (Integers.Ptrofs.add (Integers.Ptrofs.repr 0)
                                                                 (Integers.Ptrofs.repr ptr))) v).
      apply X in H22. invert H22. congruence.

      constructor; simplify. unfold Verilog.merge_regs. unfold_merge. rewrite AssocMap.gso.
      assumption. lia.
      unfold Verilog.merge_regs. unfold_merge. rewrite AssocMap.gso.
      assumption. lia.

    + invert MARR. inv CONST. crush.

      unfold Op.eval_addressing in H0.
      destruct (Archi.ptr64) eqn:ARCHI; crush.
      rewrite ARCHI in H0. crush.

      unfold check_address_parameter_unsigned in *;
      unfold check_address_parameter_signed in *; crush.

      assert (Integers.Ptrofs.repr 0 = Integers.Ptrofs.zero) as ZERO by reflexivity.
      rewrite ZERO in H1. clear ZERO.
      rewrite Integers.Ptrofs.add_zero_l in H1.

      remember i as OFFSET.

      (** Modular preservation proof *)
      assert (Integers.Ptrofs.unsigned OFFSET mod 4 = 0) as MOD_PRESERVE.
      { apply Mem.store_valid_access_3 in H1. unfold Mem.valid_access in *. simplify.
        apply Zdivide_mod. assumption. }

      (** Write bounds proof *)
      assert (Integers.Ptrofs.unsigned OFFSET < f.(RTL.fn_stacksize)) as WRITE_BOUND_HIGH.
      { destruct (Integers.Ptrofs.unsigned OFFSET <? f.(RTL.fn_stacksize)) eqn:?EQ; crush; auto.
        unfold stack_bounds in BOUNDS.
        exploit (BOUNDS (Integers.Ptrofs.unsigned OFFSET) (Registers.Regmap.get src rs)); auto.
        crush.
        replace (Integers.Ptrofs.repr 0) with (Integers.Ptrofs.zero) by reflexivity.
        small_tac. }

      (** Start of proof proper *)
      eexists. split.
      eapply Smallstep.plus_one.
      eapply HTL.step_module; eauto.
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

      (** Match frames *)
      edestruct only_main_stores; eauto; subst; constructor.

      (** Equality proof *)

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

      remember i as OFFSET.
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
      rewrite H8. rewrite <- offset_expr_ok_3.
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
           rewrite Z2Nat.id in H13; try lia.
           apply Zmult_lt_compat_r with (p := 4) in H13; try lia.
           rewrite ZLib.div_mul_undo in H13; try lia.
           split; try lia.
           apply Z.le_trans with (m := RTL.fn_stacksize f); crush; lia.
      }

      rewrite <- offset_expr_ok_3.
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
           apply Zmult_lt_compat_r with (p := 4) in H11; try lia.
           rewrite ZLib.div_mul_undo in H11; try lia.
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
      match goal with | |- ?x = _ => destruct x eqn:?EQ end; try reflexivity.
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

      constructor; simplify. unfold Verilog.merge_regs. unfold_merge. rewrite AssocMap.gso.
      assumption. lia.
      unfold Verilog.merge_regs. unfold_merge. rewrite AssocMap.gso.
      assumption. lia.

      Unshelve.
      all: try (exact tt); auto.
  Qed.
  Hint Resolve transl_istore_correct : htlproof.

  Lemma transl_icond_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (cond : Op.condition) (args : list Registers.reg)
      (ifso ifnot : RTL.node) (b : bool) (pc' : RTL.node),
      (RTL.fn_code f) ! pc = Some (RTL.Icond cond args ifso ifnot) ->
      Op.eval_condition cond (map (fun r : positive => Registers.Regmap.get r rs) args) m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      forall R1 : HTL.state,
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states ge (RTL.State s f sp pc' rs m) R2.
  Proof.
    intros s f sp pc rs m cond args ifso ifnot b pc' H H0 H1 R1 MSTATE.
    inv_state.
    destruct b.
    - eexists. split. apply Smallstep.plus_one.
      match goal with
      | [H : Z.pos ifnot <= Int.max_unsigned |- _] => clear H
      end.
      eapply HTL.step_module; eauto.
      inv CONST; assumption.
      inv CONST; assumption.
      econstructor; simpl; trivial.
      constructor; trivial.
      eapply Verilog.erun_Vternary_true; simpl; eauto.
      eapply eval_cond_correct; eauto. intros.
      intros. eapply RTL.max_reg_function_use. eauto. auto.
      econstructor. auto.
      simpl. econstructor. unfold Verilog.merge_regs. unfold_merge. simpl.
      apply AssocMap.gss.

      inv MARR. inv CONST.
      big_tac.
      constructor; rewrite AssocMap.gso; simplify; try assumption; lia.

    - eexists. split. apply Smallstep.plus_one.
      match goal with
      | [H : Z.pos ifso <= Int.max_unsigned |- _] => clear H
      end.
      eapply HTL.step_module; eauto.
      inv CONST; assumption.
      inv CONST; assumption.
      econstructor; simpl; trivial.
      constructor; trivial.
      eapply Verilog.erun_Vternary_false; simpl; eauto.
      eapply eval_cond_correct; eauto. intros.
      intros. eapply RTL.max_reg_function_use. eauto. auto.
      econstructor. auto.
      simpl. econstructor. unfold Verilog.merge_regs. unfold_merge. simpl.
      apply AssocMap.gss.

      inv MARR. inv CONST.
      big_tac.
      constructor; rewrite AssocMap.gso; simplify; try assumption; lia.

      Unshelve. all: exact tt.
  Qed.
  Hint Resolve transl_icond_correct : htlproof.

  (*Lemma transl_ijumptable_correct:
    forall (s : list RTL.stackframe) (f : RTL.function) (sp : Values.val) (pc : positive)
      (rs : Registers.Regmap.t Values.val) (m : mem) (arg : Registers.reg) (tbl : list RTL.node)
      (n : Integers.Int.int) (pc' : RTL.node),
      (RTL.fn_code f) ! pc = Some (RTL.Ijumptable arg tbl) ->
      Registers.Regmap.get arg rs = Values.Vint n ->
      list_nth_z tbl (Integers.Int.unsigned n) = Some pc' ->
      forall R1 : HTL.state,
        match_states ge (RTL.State s f sp pc rs m) R1 ->
        exists R2 : HTL.state,
          Smallstep.plus HTL.step tge R1 Events.E0 R2 /\ match_states ge (RTL.State s f sp pc' rs m) R2.
  Proof.
    intros s f sp pc rs m arg tbl n pc' H H0 H1 R1 MSTATE.
  
  Hint Resolve transl_ijumptable_correct : htlproof.*)

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

  Hint Constructors list_forall2 : htlproof.
  Hint Constructors match_frames : htlproof.

  Lemma transl_initial_states :
    forall s1 : Smallstep.state (RTL.semantics prog),
      Smallstep.initial_state (RTL.semantics prog) s1 ->
      exists s2 : Smallstep.state (HTL.semantics tprog),
        Smallstep.initial_state (HTL.semantics tprog) s2 /\ match_states ge s1 s2.
  Proof.
    induction 1.
    destruct TRANSL.
    unfold main_is_internal in H4. repeat (unfold_match H4).
    assert (f = AST.Internal f1).
    {
      apply option_inv.
      rewrite <- Heqo0. rewrite <- H1. replace b with b0.
      auto. apply option_inv. rewrite <- H0. rewrite <- Heqo.
      trivial.
    }

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
    - apply (Genv.init_mem_transf_partial TRANSL'); eauto.
    - replace (AST.prog_main tprog) with (AST.prog_main prog)
        by (symmetry; eapply Linking.match_program_main; eauto).
      rewrite symbols_preserved; eauto.
    - eauto.
    - constructor; auto with htlproof.
      apply transl_module_correct.
      assert (Some (AST.Internal x) = Some (AST.Internal m)) as Heqm.
      { rewrite <- H6. setoid_rewrite <- A. trivial. }
      inv Heqm.
      assumption.
  Qed.
  Hint Resolve transl_initial_states : htlproof.

  Lemma transl_final_states :
    forall (s1 : Smallstep.state (RTL.semantics prog))
           (s2 : Smallstep.state (HTL.semantics tprog))
           (r : Integers.Int.int),
      match_states ge s1 s2 ->
      Smallstep.final_state (RTL.semantics prog) s1 r ->
      Smallstep.final_state (HTL.semantics tprog) s2 r.
  Proof.
    intros.
    repeat match goal with [ H : _ |- _ ] => try inv H end.
    repeat constructor; auto.
  Qed.
  Hint Resolve transl_final_states : htlproof.

  Theorem transl_step_correct:
    forall (S1 : RTL.state) t S2,
      RTL.step ge S1 t S2 ->
      forall (R1 : HTL.state),
        match_states ge S1 R1 ->
        exists R2, Smallstep.plus HTL.step tge R1 t R2 /\ match_states ge S2 R2.
  Proof.
    induction 1; eauto with htlproof; try solve [ intros; inv_state ].
  Qed.

  Hint Resolve transl_step_correct : htlproof.

  Theorem transf_program_correct:
    Smallstep.forward_simulation (RTL.semantics prog) (HTL.semantics tprog).
  Proof.
    eapply Smallstep.forward_simulation_plus; eauto with htlproof.
    apply senv_preserved.
  Qed.

End CORRECTNESS.
