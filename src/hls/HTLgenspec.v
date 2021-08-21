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

Require Import Coq.micromega.Lia.

Require compcert.backend.RTL.
Require compcert.common.Errors.
Require compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.common.ListExtra.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.HTL.
Require Import vericert.hls.HTLgen.
Require Import vericert.hls.AssocMap.

From Hammer Require Import Tactics.

(** * Relational specification of the translation *)

(** We now define inductive predicates that characterise the fact that the
statemachine that is created by the translation contains the correct
translations for each of the elements *)

(** [tr_instr] describes the translation of instructions that are directly translated into a single state *)
Inductive tr_instr (fin rtrn st stk : reg) : RTL.instruction -> datapath_stmnt -> control_stmnt -> Prop :=
| tr_instr_Inop :
    forall n,
      Z.pos n <= Int.max_unsigned ->
      tr_instr fin rtrn st stk (RTL.Inop n) Vskip (state_goto st n)
| tr_instr_Iop :
    forall n op args dst s s' e i,
      Z.pos n <= Int.max_unsigned ->
      translate_instr op args s = OK e s' i ->
      tr_instr fin rtrn st stk (RTL.Iop op args dst n) (Vnonblock (Vvar dst) e) (state_goto st n)
| tr_instr_Icond :
    forall n1 n2 cond args s s' i c,
      Z.pos n1 <= Int.max_unsigned ->
      Z.pos n2 <= Int.max_unsigned ->
      translate_condition cond args s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Icond cond args n1 n2) Vskip (state_cond st c n1 n2)
| tr_instr_Iload :
    forall mem addr args s s' i c dst n,
      Z.pos n <= Int.max_unsigned ->
      translate_arr_access mem addr args stk s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Iload mem addr args dst n) (Vnonblock (Vvar dst) c) (state_goto st n)
| tr_instr_Istore :
    forall mem addr args s s' i c src n,
      Z.pos n <= Int.max_unsigned ->
      translate_arr_access mem addr args stk s = OK c s' i ->
      tr_instr fin rtrn st stk (RTL.Istore mem addr args src n) (Vnonblock c (Vvar src))
               (state_goto st n).
(*| tr_instr_Ijumptable :
    forall cexpr tbl r,
    cexpr = tbl_to_case_expr st tbl ->
    tr_instr fin rtrn st stk (RTL.Ijumptable r tbl) (Vskip) (Vcase (Vvar r) cexpr (Some Vskip)).*)
Hint Constructors tr_instr : htlspec.

Inductive tr_code (ge : RTL.genv) (c : RTL.code) (pc : RTL.node) (stmnts : datapath) (trans : controllogic)
          (externctrl : AssocMap.t (ident * controlsignal)) (fin rtrn st stk : reg) : RTL.instruction -> Prop :=
| tr_code_single :
    forall i s t,
      c!pc = Some i ->
      stmnts!pc = Some s ->
      trans!pc = Some t ->
      tr_instr fin rtrn st stk i s t ->
      tr_code ge c pc stmnts trans externctrl fin rtrn st stk i
| tr_code_call :
    forall sig fn args dst n,
      c!pc = Some (RTL.Icall sig (inr fn) args dst n) ->
      (exists fd, find_func ge fn = Some (AST.Internal fd)) ->
      Z.pos n <= Int.max_unsigned ->

      (exists pc2 fn_rst fn_return fn_finish fn_params,
          externctrl ! fn_rst = Some (fn, ctrl_reset) /\
          externctrl ! fn_return = Some (fn, ctrl_return) /\
          externctrl ! fn_finish = Some (fn, ctrl_finish) /\
          length args = length fn_params /\
          (forall n arg, List.nth_error args n = Some arg ->
                    exists r, List.nth_error fn_params n = Some r /\
                         externctrl ! r = Some (fn, ctrl_param n)) /\
          Z.pos pc2 <= Int.max_unsigned /\
          stmnts!pc = Some (fork fn_rst (List.combine fn_params args)) /\
          trans!pc = Some (state_goto st pc2) /\
          stmnts!pc2 = Some (join fn_return fn_rst dst) /\
          trans!pc2 = Some (state_wait st fn_finish n)) ->

      tr_code ge c pc stmnts trans externctrl fin rtrn st stk (RTL.Icall sig (inr fn) args dst n)
| tr_code_return :
    forall r,
      c!pc = Some (RTL.Ireturn r) ->

      (exists pc2,
          stmnts!pc = Some (do_return fin rtrn r) /\
          trans!pc = Some (state_goto st pc2) /\
          stmnts!pc2 = Some (idle fin) /\
          trans!pc2 = Some Vskip) ->

      tr_code ge c pc stmnts trans externctrl fin rtrn st stk (RTL.Ireturn r).
Hint Constructors tr_code : htlspec.

Inductive tr_module (ge : RTL.genv) (f : RTL.function) : module -> Prop :=
  tr_module_intro :
    forall data control fin rtrn st stk stk_len m start rst clk scldecls arrdecls externctrl wf,
      m = (mkmodule f.(RTL.fn_params)
                        data
                        control
                        f.(RTL.fn_entrypoint)
                        st stk stk_len fin rtrn start rst clk scldecls arrdecls externctrl wf) ->
      (forall pc i, Maps.PTree.get pc f.(RTL.fn_code) = Some i ->
               tr_code ge f.(RTL.fn_code) pc data control externctrl fin rtrn st stk i) ->
      stk_len = Z.to_nat (f.(RTL.fn_stacksize) / 4) ->
      Z.modulo (f.(RTL.fn_stacksize)) 4 = 0 ->
      0 <= f.(RTL.fn_stacksize) < Integers.Ptrofs.modulus ->
      (st > (RTL.max_reg_function f))%positive ->
      (fin > st)%positive ->
      (rtrn > fin)%positive ->
      (stk > rtrn)%positive ->
      (start > stk)%positive ->
      (rst > start)%positive ->
      (clk > rst)%positive ->
      (forall n, (exists x, externctrl!n = Some x) -> (n > clk)%positive) ->
      tr_module ge f m.
Hint Constructors tr_module : htlspec.

Hint Resolve Maps.PTree.elements_keys_norepet : htlspec.
Hint Resolve Maps.PTree.elements_correct : htlspec.
Hint Resolve Maps.PTree.gss : htlspec.
Hint Resolve PTree.elements_complete : htlspec.
Hint Resolve -> Z.leb_le : htlspec.

Hint Unfold block : htlspec.
Hint Unfold nonblock : htlspec.

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: st) (i: st_incr s1 s3),
    bind f g s1 = OK y s3 i ->
    exists x, exists s2, exists i1, exists i2,
            f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof. unfold bind. sauto. Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: st) (i: st_incr s1 s3),
    bind2 f g s1 = OK z s3 i ->
    exists x, exists y, exists s2, exists i1, exists i2,
              f s1 = OK (x, y) s2 i1 /\ g x y s2 = OK z s3 i2.
Proof. sauto using bind_inversion. Qed.

Ltac monadInv1 H :=
  match type of H with
  | ((match ?x with | _ => _ end) = OK _ _ _) =>
    destruct x eqn:?; try discriminate; try monadInv1 H
  | (OK _ _ _ = OK _ _ _) =>
    inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
    discriminate
  | (ret _ _ = OK _ _ _) =>
    inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
    discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
    let x := fresh "x" in (
      let s := fresh "s" in (
        let i1 := fresh "INCR" in (
          let i2 := fresh "INCR" in (
            let EQ1 := fresh "EQ" in (
              let EQ2 := fresh "EQ" in (
                destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
                clear H;
                try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let s := fresh "s" in (
          let i1 := fresh "INCR" in (
            let i2 := fresh "INCR" in (
              let EQ1 := fresh "EQ" in (
                let EQ2 := fresh "EQ" in (
                  destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
                  clear H;
                  try (monadInv1 EQ2))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (OK _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _ _ _) =>
    ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Ltac rewrite_states :=
  match goal with
  | [ H: ?x ?s = ?x ?s' |- _ ] =>
    let c1 := fresh "c" in
    let c2 := fresh "c" in
    learn (?x ?s) as c1; learn (?x ?s') as c2; try subst
  end.

Ltac saturate_incr :=
  repeat match goal with
         | [INCR1 : st_prop ?s1 ?s2, INCR2 : st_prop ?s2 ?s3 |- _] =>
           let INCR3 := fresh "INCR" in
           learn (st_trans s1 s2 s3 INCR1 INCR2)
         end.

(** Used to solve goals that follow directly from a single monadic operation *)
Ltac intro_step :=
  match goal with
  | [ H : _ = OK _ _ _  |- _ ] => solve [ monadInv H; simplify; eauto with htlspec ]
  end.

(** Used to transfer a result about one of the maps in the state from one
      state to a latter one *)
Ltac trans_step s1 s2 :=
  saturate_incr;
  match goal with
  | [ INCR : st_prop s1 s2 |- _ ] => try solve [inversion INCR; crush]; destruct INCR
  end;
  solve [
      match goal with
      | [ MAP_INCR : HTLgen.map_incr ?map _ _ |- (?map _) ! ?idx = _ ] =>
        destruct MAP_INCR with idx; try crush_trans; crush
      end
    ].

(* FIXME: monad_crush can be slow when there are a lot of intermediate states. *)

(* Try to prove a goal about a state by first proving it for an earlier state and then transfering it to the final. *)
Ltac monad_crush :=
  match goal with
  | [ finalstate : st, prevstate : st |- _] =>
    match goal with
    | [ |- context f[finalstate]] =>
      let inter := context f[prevstate] in
      try solve [
            match inter with
            | context f[finalstate] =>
              let inter := context f[prevstate] in
              solve [assert inter by intro_step; trans_step prevstate finalstate]
            end
          ];
      solve [assert inter by intro_step; trans_step prevstate finalstate]
    end
  end.

Ltac full_split := repeat match goal with [ |- _ /\ _ ] => split end.

Ltac relevant_monad_inv :=
  multimatch goal with
  | [ EQ : _ ?s = OK ?x _ _ |- context[?x] ] => monadInv EQ
  | [ EQ : _ ?s = OK (?x, _) _ _ |- context[?x] ] => monadInv EQ
  | [ EQ : _ ?s = OK (_, ?x) _ _ |- context[?x] ] => monadInv EQ
  | [ EQ : _ ?s = OK (_, ?x) _ _ |- context[?x] ] => monadInv EQ
  end.

Ltac any_monad_inv :=
  relevant_monad_inv +
  multimatch goal with
  | [ EQ : _ ?s = OK _ _ _ |- _ ] => monadInv EQ
  end.

Ltac some_incr :=
  saturate_incr;
  multimatch goal with
  | [ INCR : st_prop _ _ |- _ ] => inversion INCR
  end.

Lemma helper__map_externctrl_params_args : forall args param_pairs fn s s' k i,
    xmap_externctrl_params k fn args s = OK param_pairs s' i ->
    snd (List.split param_pairs) = args.
Proof.
  induction args.
  - sauto.
  - intros. monadInv H. sauto.
Qed.

Lemma map_externctrl_params_args : forall args param_pairs fn s s' i,
    map_externctrl_params fn args s = OK param_pairs s' i ->
    snd (List.split param_pairs) = args.
Proof. sauto use: helper__map_externctrl_params_args. Qed.

Lemma helper__map_externctrl_params_spec : forall args n param_pairs k fn s s' i,
    xmap_externctrl_params k fn args s = OK param_pairs s' i ->
    (n < length args)%nat ->
    exists r, (List.nth_error (fst (List.split param_pairs)) n = Some r) /\
         (s'.(st_externctrl) ! r = Some (fn, ctrl_param (n+k))).
Proof.
  induction args.
  - sauto use: nth_error_nil.
  - intros.
    monadInv H.
    destruct n; simplify.
    + destruct (split x0). simpl.
      exists x. crush. monad_crush.
    + destruct (IHargs n _ _ _ _ _ _ EQ1 ltac:(lia)).
      destruct (split _). simpl in *.
      eexists. replace (S (n + k))%nat with (n + S k)%nat by lia.
      eassumption.
    Qed.

Lemma map_externctrl_params_spec : forall args n param_pairs fn s s' i,
    map_externctrl_params fn args s = OK param_pairs s' i ->
    (n < length args)%nat ->
    exists r, (List.nth_error (fst (List.split param_pairs)) n = Some r) /\
         (s'.(st_externctrl) ! r = Some (fn, ctrl_param n)).
Proof. sauto use: helper__map_externctrl_params_spec. Qed.
Hint Resolve map_externctrl_params_spec : htlspec.

Lemma iter_expand_instr_spec :
  forall l prog fin rtrn stack s s' i x c,
    HTLMonadExtra.collectlist (transf_instr (Globalenvs.Genv.globalenv prog) fin rtrn stack) l s = OK x s' i ->
    list_norepet (List.map fst l) ->
    (forall pc instr, In (pc, instr) l -> c!pc = Some instr) ->
    (forall pc instr, In (pc, instr) l -> c!pc = Some instr ->
                 tr_code (Globalenvs.Genv.globalenv prog) c pc s'.(st_datapath) s'.(st_controllogic) s'.(st_externctrl) fin rtrn s'.(st_st) stack instr).
Proof.
  (** Used to solve the simpler cases of tr_code: those involving tr_instr *)
  Ltac tr_code_simple_tac :=
    eapply tr_code_single;
    match goal with
    | [ H : (?pc, _) = (?pc, ?instr) \/ In (?pc, ?instr) _ |- _ ] =>
      inversion H;
      do 2
         match goal with
         | [ H' : In (_, _) _ |- _ ] => solve [ eapply in_map with (f:=fst) in H'; contradiction ]
         | [ H' : (pc, _) = (pc, instr) |- _ ] => inversion H'
         end;
      simplify; eauto with htlspec
    end;
    monad_crush.

  induction l; crush.
  destruct a as [pc1 instr1]; simplify. inv H0. monadInv H.
  destruct (peq pc pc1).
  - subst.
    destruct instr1 eqn:instr_eq;
      repeat destruct_match; try discriminate; try monadInv1 EQ.
    + (* Inop *) tr_code_simple_tac.
    + (* Iop *) tr_code_simple_tac.
    + (* Iload *) tr_code_simple_tac.
    + (* Istore *) tr_code_simple_tac.
    + (* Icall *)
      inversion H2; try solve [eapply in_map with (f:=fst) in H; contradiction].
      inversion H.

      eapply tr_code_call; eauto; crush.

      repeat (eapply ex_intro).

      repeat (apply conj).
      * monad_crush.
      * monad_crush.
      * monad_crush.
      * transitivity (length x1).
        replace l0 with (snd (List.split x1)).
        apply split_length_r.
        eapply map_externctrl_params_args; eassumption.
        auto using split_length_l.
      * intros.
        destruct (map_externctrl_params_args _ _ _ _ _ _ EQ1); eauto using nth_error_length.
        destruct (map_externctrl_params_spec _ n0 _ _ _ _ _ EQ1); eauto using nth_error_length.
        exists x8. simplify; eauto.
        monad_crush.
      * eapply create_state_max; eassumption.
      * replace x5 with (st_freshreg s6) in * by intro_step.
        replace l0 with (snd (split x1)) by
            eauto using map_externctrl_params_args.
        rewrite combine_split.
        monad_crush.
      * monad_crush.
      * replace x6 with (st_freshreg s7) in * by intro_step.
        replace x5 with (st_freshreg s6) in * by intro_step.
        monad_crush.
      * replace x4 with (st_freshreg s5) in * by intro_step.
        monad_crush.
    + (* Icond *) tr_code_simple_tac.
    + (* Ireturn *)
      inversion H2; try solve [eapply in_map with (f:=fst) in H; contradiction].
      inversion H.
      eapply tr_code_return; crush; eexists; simplify; monad_crush.
  - eapply IHl; eauto.
    intuition crush.
Qed.
Hint Resolve iter_expand_instr_spec : htlspec.

Lemma map_incr_some : forall {A} map (s s' : st) idx (x : A),
    (map s) ! idx = Some x ->
    map_incr map s s' ->
    (map s') ! idx = Some x.
Proof. intros * ? Hincr. destruct Hincr with idx; crush. Qed.
Hint Resolve map_incr_some : htlspec.

Lemma tr_code_trans : forall ge c pc instr fin rtrn stack s s',
  tr_code ge c pc (st_datapath s) (st_controllogic s) (st_externctrl s) fin rtrn (st_st s) stack instr ->
  st_prop s s' ->
  tr_code ge c pc (st_datapath s') (st_controllogic s') (st_externctrl s') fin rtrn (st_st s') stack instr.
Proof.
  intros * Htr Htrans.
  destruct Htr.
  + eapply tr_code_single.
    * trans_step s s'.
    * inversion Htrans.
      destruct H6 with pc. crush.
      replace ((st_datapath s') ! pc).
      eassumption.
    * inversion Htrans.
      destruct H7 with pc. crush.
      replace ((st_controllogic s') ! pc).
      eassumption.
    * inversion Htrans. crush.
  + eapply tr_code_call; eauto with htlspec.
    simplify.
    inversion Htrans.
    replace (st_st s').
    repeat (eapply ex_intro).
    repeat (apply conj).
    * eapply map_incr_some; inversion Htrans; eauto with htlspec.
    * eapply map_incr_some; inversion Htrans; eauto with htlspec.
    * eapply map_incr_some; inversion Htrans; eauto with htlspec.
    * eassumption.
    * intros.
      destruct (H6 n0 ltac:(auto) ltac:(auto)) as [r [? ?]].
      eexists. split; eauto with htlspec.
    * eauto with htlspec.
    * eauto with htlspec.
    * eauto with htlspec.
    * eauto with htlspec.
    * eauto with htlspec.
  + eapply tr_code_return; eauto with htlspec.
    inversion Htrans.
    simplify. eexists.
    replace (st_st s').
    repeat split; eauto with htlspec.
  Unshelve. all: eauto.
Qed.
Hint Resolve tr_code_trans : htlspec.

Lemma declare_params_freshreg_trans : forall params s s' x i,
    declare_params params s = OK x s' i ->
    st_freshreg s = st_freshreg s'.
Proof.
  induction params; unfold declare_params in *; intros * H.
  - inv H. trivial.
  - monadInv H.
    transitivity (st_freshreg s0).
    + monadInv EQ. auto.
    + eauto.
Qed.
Hint Resolve declare_params_freshreg_trans : htlspec.

Lemma declare_params_externctrl_trans : forall params s s' x i,
    declare_params params s = OK x s' i ->
    st_externctrl s = st_externctrl s'.
Proof.
  induction params; unfold declare_params in *; intros * H.
  - inv H. trivial.
  - monadInv H.
    transitivity (st_externctrl s0).
    + monadInv EQ. auto.
    + eauto.
Qed.
Hint Resolve declare_params_freshreg_trans : htlspec.

Theorem transl_module_correct :
  forall p f m,
    transl_module p f = Errors.OK m -> tr_module (Globalenvs.Genv.globalenv p) f m.
Proof.
  intros * H.
  unfold transl_module in *.
  unfold run_mon in *.
  unfold_match H.
  inv H.
  inversion s; subst.

  unfold transf_module in *.
  unfold stack_correct in *.
  destruct_match; simplify; crush.
  monadInv Heqr.

  repeat destruct_match; crush.
  repeat match goal with
         | [ EQ : ret _ _ = OK _ _ _ |- _ ] => monadInv EQ
         | [ EQ : OK _ _ _ = OK _ _ _ |- _ ] => monadInv EQ
         | [ EQ : get _ = OK _ _ _ |- _ ] => monadInv EQ
         end.

  econstructor;
    eauto with htlspec;
    try solve [ repeat relevant_monad_inv; crush ].
  - auto_apply declare_params_freshreg_trans.
    replace (st_st s').
    monadInv EQ1.
    inversion INCR.
    repeat match goal with
           | [ H : context[st_freshreg (max_state _)] |- _ ] => unfold max_state in H; simpl in H
           end.
    crush.
  - assert (forall n, (st_externctrl (max_state f)) ! n = None) by (simplify; eauto using AssocMap.gempty).
    assert (forall n, (st_externctrl s0) ! n = None) by (erewrite <- (declare_params_externctrl_trans); eauto).
    assert (forall n, (st_externctrl s1) ! n = None) by (any_monad_inv; simplify; auto).
    assert (forall n, (st_externctrl s2) ! n = None) by (any_monad_inv; simplify; auto).
    assert (forall n, (st_externctrl s3) ! n = None) by (any_monad_inv; simplify; auto).
    assert (forall n, (st_externctrl s4) ! n = None) by (any_monad_inv; simplify; auto).
    assert (forall n, (st_externctrl s5) ! n = None) by (any_monad_inv; simplify; auto).

    assert (forall n, (st_externctrl s6) ! n = None) by (any_monad_inv; simplify; auto).
    assert ((st_freshreg s6) > x6)%positive by (relevant_monad_inv; simplify; crush).

    intros.
    repeat match goal with
           | [ H: forall (_ : positive), _ |- _ ] => specialize (H r)
           end.

    enough (n >= st_freshreg s6)%positive by lia.
    inversion INCR13.
    auto.
Qed.
