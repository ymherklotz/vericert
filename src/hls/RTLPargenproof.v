(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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

(*Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Linking.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPargen.

Definition match_prog (prog : RTLBlock.program) (tprog : RTLPar.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq prog tprog.

Inductive match_stackframes: RTLBlock.stackframe -> RTLPar.stackframe -> Prop :=
| match_stackframe:
    forall f tf res sp pc rs rs',
      transl_function f = OK tf ->
      regs_lessdef rs rs' ->
      match_stackframes (Stackframe res f sp pc rs)
                        (Stackframe res tf sp pc rs').

Inductive match_states: RTLBlock.state -> RTLPar.state -> Prop :=
| match_state:
    forall sf f sp pc rs rs' m m' sf' tf
      (TRANSL: transl_function f = OK tf)
      (STACKS: list_forall2 match_stackframes sf sf')
      (REG: regs_lessdef rs rs')
      (MEM: Mem.extends m m'),
      match_states (State sf f sp pc rs m)
                   (State sf' tf sp pc rs' m')
| match_returnstate:
    forall stack stack' v v' m m'
      (STACKS: list_forall2 match_stackframes stack stack')
      (MEM: Mem.extends m m')
      (LD: Val.lessdef v v'),
      match_states (Returnstate stack v m)
                   (Returnstate stack' v' m')
| match_callstate:
    forall stack stack' f tf args args' m m'
      (TRANSL: transl_fundef f = OK tf)
      (STACKS: list_forall2 match_stackframes stack stack')
      (LD: Val.lessdef_list args args')
      (MEM: Mem.extends m m'),
      match_states (Callstate stack f args m)
                   (Callstate stack' tf args' m').

Section CORRECTNESS.

  Context (prog: RTLBlock.program) (tprog : RTLPar.program).
  Context (TRANSL: match_prog prog tprog).

  Let ge : RTLBlock.genv := Globalenvs.Genv.globalenv prog.
  Let tge : RTLPar.genv := Globalenvs.Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof using TRANSL. intros. eapply (Genv.find_symbol_match TRANSL). Qed.
  Hint Resolve symbols_preserved : rtlgp.

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: RTLBlock.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma functions_translated:
    forall (v: Values.val) (f: RTLBlock.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
  Proof using TRANSL.
    intros. exploit (Genv.find_funct_match TRANSL); eauto.
    intros (cu & tf & P & Q & R); exists tf; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof (Genv.senv_transf_partial TRANSL).
  Hint Resolve senv_preserved : rtlgp.

  Lemma sig_transl_function:
    forall (f: RTLBlock.fundef) (tf: RTLPar.fundef),
      transl_fundef f = OK tf ->
      funsig tf = funsig f.
  Proof using .
    unfold transl_fundef, transf_partial_fundef, transl_function; intros;
    repeat destruct_match; crush;
    match goal with H: OK _ = OK _ |- _ => inv H end; auto.
  Qed.
  Hint Resolve sig_transl_function : rtlgp.

  Hint Resolve Val.lessdef_same : rtlgp.
  Hint Resolve regs_lessdef_regs : rtlgp.

  Lemma find_function_translated:
    forall ros rs rs' f,
      regs_lessdef rs rs' ->
      find_function ge ros rs = Some f ->
      exists tf, find_function tge ros rs' = Some tf
                 /\ transl_fundef f = OK tf.
  Proof using TRANSL.
    Ltac ffts := match goal with
                 | [ H: forall _, Val.lessdef _ _, r: Registers.reg |- _ ] =>
                   specialize (H r); inv H
                 | [ H: Vundef = ?r, H1: Genv.find_funct _ ?r = Some _ |- _ ] =>
                   rewrite <- H in H1
                 | [ H: Genv.find_funct _ Vundef = Some _ |- _] => solve [inv H]
                 | _ => solve [exploit functions_translated; eauto]
                 end.
    unfold regs_lessdef; destruct ros; simplify; try rewrite <- H;
    [| rewrite symbols_preserved; destruct_match;
      try (apply function_ptr_translated); crush ];
    intros;
    repeat ffts.
  Qed.

  Lemma schedule_oracle_nil:
    forall bb cfi,
      schedule_oracle {| bb_body := nil; bb_exit := cfi |} bb = true ->
      bb_body bb = nil /\ bb_exit bb = cfi.
  Proof using .
    unfold schedule_oracle, check_control_flow_instr.
    simplify; repeat destruct_match; crush.
  Qed.

  Lemma schedule_oracle_nil2:
    forall cfi,
      schedule_oracle {| bb_body := nil; bb_exit := cfi |}
                      {| bb_body := nil; bb_exit := cfi |} = true.
  Proof using .
    unfold schedule_oracle, check_control_flow_instr.
    simplify; repeat destruct_match; crush.
  Qed.

  Lemma eval_op_eq:
    forall (sp0 : Values.val) (op : Op.operation) (vl : list Values.val),
      Op.eval_operation ge sp0 op vl = Op.eval_operation tge sp0 op vl.
  Proof using TRANSL.
    intros.
    destruct op; auto; unfold Op.eval_operation, Genv.symbol_address, Op.eval_addressing32;
    [| destruct a; unfold Genv.symbol_address ];
    try rewrite symbols_preserved; auto.
  Qed.
  Hint Resolve eval_op_eq : rtlgp.

  Lemma eval_addressing_eq:
    forall sp addr vl,
      Op.eval_addressing ge sp addr vl = Op.eval_addressing tge sp addr vl.
  Proof using TRANSL.
    intros.
    destruct addr;
    unfold Op.eval_addressing, Op.eval_addressing32;
    unfold Genv.symbol_address;
    try rewrite symbols_preserved; auto.
  Qed.
  Hint Resolve eval_addressing_eq : rtlgp.

  Lemma ge_preserved_lem:
    ge_preserved ge tge.
  Proof using TRANSL.
    unfold ge_preserved.
    eauto with rtlgp.
  Qed.
  Hint Resolve ge_preserved_lem : rtlgp.

  Lemma lessdef_regmap_optget:
    forall or rs rs',
      regs_lessdef rs rs' ->
      Val.lessdef (regmap_optget or Vundef rs) (regmap_optget or Vundef rs').
  Proof using. destruct or; crush. Qed.
  Hint Resolve lessdef_regmap_optget : rtlgp.

  Lemma int_lessdef:
    forall rs rs',
      regs_lessdef rs rs' ->
      (forall arg v,
          rs !! arg = Vint v ->
          rs' !! arg = Vint v).
  Proof using. intros ? ? H; intros; specialize (H arg); inv H; crush. Qed.
  Hint Resolve int_lessdef : rtlgp.

  Ltac semantics_simpl :=
    match goal with
    | [ H: match_states _ _ |- _ ] =>
      let H2 := fresh "H" in
      learn H as H2; inv H2
    | [ H: transl_function ?f = OK _ |- _ ] =>
      let H2 := fresh "TRANSL" in
      learn H as H2;
      unfold transl_function in H2;
      destruct (check_scheduled_trees
                  (@fn_code RTLBlock.bb f)
                  (@fn_code RTLPar.bb (schedule f))) eqn:?;
               [| discriminate ]; inv H2
    | [ H: context[check_scheduled_trees] |- _ ] =>
      let H2 := fresh "CHECK" in
      learn H as H2;
      eapply check_scheduled_trees_correct in H2; [| solve [eauto] ]
    | [ H: schedule_oracle {| bb_body := nil; bb_exit := _ |} ?bb = true |- _ ] =>
      let H2 := fresh "SCHED" in
      learn H as H2;
      apply schedule_oracle_nil in H2
    | [ H: find_function _ _ _ = Some _ |- _ ] =>
      learn H; exploit find_function_translated; eauto; inversion 1
    | [ H: Mem.free ?m _ _ _ = Some ?m', H2: Mem.extends ?m ?m'' |- _ ] =>
      learn H; exploit Mem.free_parallel_extends; eauto; intros
    | [ H: Events.eval_builtin_args _ _ _ _ _ _, H2: regs_lessdef ?rs ?rs' |- _ ] =>
      let H3 := fresh "H" in
      learn H; exploit Events.eval_builtin_args_lessdef; [apply H2 | | |];
      eauto with rtlgp; intro H3; learn H3
    | [ H: Events.external_call _ _ _ _ _ _ _ |- _ ] =>
      let H2 := fresh "H" in
      learn H; exploit Events.external_call_mem_extends;
      eauto; intro H2; learn H2
    | [ H: exists _, _ |- _ ] => inv H
    | _ => progress simplify
    end.

  Hint Resolve Events.eval_builtin_args_preserved : rtlgp.
  Hint Resolve Events.external_call_symbols_preserved : rtlgp.
  Hint Resolve set_res_lessdef : rtlgp.
  Hint Resolve set_reg_lessdef : rtlgp.
  Hint Resolve Op.eval_condition_lessdef : rtlgp.

  Lemma step_cf_instr_correct:
    forall cfi t s s',
      step_cf_instr ge s cfi t s' ->
      forall r,
        match_states s r ->
        exists r', step_cf_instr tge r cfi t r' /\ match_states s' r'.
  Proof using TRANSL.
    induction 1; repeat semantics_simpl;
    repeat (econstructor; eauto with rtlgp).
  Qed.

  Theorem transl_step_correct :
    forall (S1 : RTLBlock.state) t S2,
      RTLBlock.step ge S1 t S2 ->
      forall (R1 : RTLPar.state),
        match_states S1 R1 ->
        exists R2, Smallstep.plus RTLPar.step tge R1 t R2 /\ match_states S2 R2.
  Proof.

    induction 1; repeat semantics_simpl.
    Abort.

(*    { destruct bb as [bbc bbe]; destruct x as [bbc' bbe'].
      assert (bbe = bbe') by admit.
      rewrite H3 in H5.
      eapply abstract_execution_correct in H5; eauto with rtlgp.
      repeat econstructor; eauto with rtlgp. simplify.
      exploit step_cf_instr_correct. eauto.
      econstructor; eauto with rtlgp.
    }
    { unfold bind in *. destruct_match; try discriminate. repeat semantics_simpl. inv TRANSL0.
      repeat econstructor; eauto. }
    { inv TRANSL0. repeat econstructor; eauto using Events.external_call_symbols_preserved, symbols_preserved, senv_preserved, Events.E0_right. }
    { inv STACKS. inv H2. repeat econstructor; eauto. }
  Qed.*)

End CORRECTNESS.
*)
