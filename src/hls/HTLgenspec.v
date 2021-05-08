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
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.HTL.
Require Import vericert.hls.HTLgen.
Require Import vericert.hls.AssocMap.

From Hammer Require Import Tactics.
From Hammer Require Import Hammer.

Hint Resolve Maps.PTree.elements_keys_norepet : htlspec.
Hint Resolve Maps.PTree.elements_correct : htlspec.
Hint Resolve Maps.PTree.gss : htlspec.
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
  crush;
  match reverse goal with
  | [ finalstate : st, prevstate : st |- _] =>
    match reverse goal with
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

Lemma xmap_externctrl_params_combine : forall args k fn s param_pairs s' i,
    xmap_externctrl_params k fn args s = OK param_pairs s' i ->
    exists params, param_pairs = List.combine params args /\ length params = length args.
Proof.
  induction args; intros; monadInv H.
  - exists nil. auto.
  - unshelve (edestruct IHargs with (k:=S k) (s:=s0) (s':=s')); auto.
    subst. exists (x::x1); crush.
Qed.
Hint Resolve xmap_externctrl_params_combine : htlspec.

Lemma map_externctrl_params_combine : forall args fn s param_pairs s' i,
    map_externctrl_params fn args s = OK param_pairs s' i ->
    exists params, param_pairs = List.combine params args /\ length params = length args.
Proof. unfold map_externctrl_params. eauto using xmap_externctrl_params_combine. Qed.
Hint Resolve map_externctrl_params_combine : htlspec.

Lemma xmap_externctrl_params_snd : forall args param_pairs k fn s s' i,
    xmap_externctrl_params k fn args s = OK param_pairs s' i ->
    List.map snd param_pairs = args.
Proof.
  induction args.
  - sauto.
  - intros. monadInv H. sauto.
Qed.
Hint Resolve xmap_externctrl_params_snd : htlspec.

Lemma xmap_externctrl_params_fst : forall args n param_pairs k r fn s s' i,
    xmap_externctrl_params k fn args s = OK param_pairs s' i ->
    nth_error (List.map fst param_pairs) n = Some r ->
    s'.(st_externctrl) ! r = Some (fn, ctrl_param (n+k)).
Proof.
  induction args.
  - intros. monadInv H.
    scongruence use: nth_error_nil.
  - induction n; intros; monadInv H.
    + monad_crush.
    + sauto.
Qed.
Hint Resolve xmap_externctrl_params_fst : htlspec.

Lemma helper__map_externctrl_params_spec :
  forall args n arg,
    List.nth_error args n = Some arg ->
    forall k fn s param_pairs s' i,
      xmap_externctrl_params k fn args s = OK param_pairs s' i ->
      exists r, (In (r, arg) param_pairs) /\
           (s'.(st_externctrl) ! r = Some (fn, ctrl_param (n+k))).
Proof.
  induction args.
  - sauto use: nth_error_nil.
  - destruct n; intros * ? * H; monadInv H.
    + eexists. monad_crush.
    + sauto.
Qed.

Lemma map_externctrl_params_spec :
  forall args n arg fn s param_pairs s' i,
    map_externctrl_params fn args s = OK param_pairs s' i ->
    List.nth_error args n = Some arg ->
    exists r, (In (r, arg) param_pairs) /\
         (s'.(st_externctrl) ! r = Some (fn, ctrl_param n)).
Proof. sauto use: helper__map_externctrl_params_spec. Qed.
Hint Resolve map_externctrl_params_spec : htlspec.

Inductive tr_code (c : RTL.code) (pc : RTL.node) (i : RTL.instruction) (stmnts : datapath) (trans : controllogic)
          (externctrl : AssocMap.t (ident * controlsignal)) (fin rtrn st stk : reg) : Prop :=
| tr_code_single :
    forall s t,
      c!pc = Some i ->
      stmnts!pc = Some s ->
      trans!pc = Some t ->
      tr_instr fin rtrn st stk i s t ->
      tr_code c pc i stmnts trans externctrl fin rtrn st stk
| tr_code_call :
    forall sig fn args dst n,
      c!pc = Some (RTL.Icall sig (inr fn) args dst n) ->
      Z.pos n <= Int.max_unsigned ->

      (exists pc2 fn_rst fn_return fn_finish fn_params,
          externctrl ! fn_rst = Some (fn, ctrl_reset) /\
          externctrl ! fn_return = Some (fn, ctrl_return) /\
          externctrl ! fn_finish = Some (fn, ctrl_finish) /\
          (forall n arg, List.nth_error args n = Some arg ->
                    exists r, In (r, arg) (List.combine fn_params args) /\
                         externctrl ! r = Some (fn, ctrl_param n)) /\

          stmnts!pc = Some (fork fn_rst (List.combine fn_params args)) /\
          trans!pc = Some (state_goto st pc2) /\
          stmnts!pc2 = Some (join fn_return fn_rst dst) /\
          trans!pc2 = Some (state_wait st fn_finish n)) ->

      tr_code c pc i stmnts trans externctrl fin rtrn st stk
| tr_code_return :
    forall r,
      c!pc = Some (RTL.Ireturn r) ->

      (exists pc2,
          stmnts!pc = Some (return_val fin rtrn r) /\
          trans!pc = Some (state_goto st pc2) /\
          stmnts!pc2 = Some (idle fin) /\
          trans!pc2 = Some Vskip) ->

      tr_code c pc i stmnts trans externctrl fin rtrn st stk.
Hint Constructors tr_code : htlspec.

Inductive tr_module (f : RTL.function) : module -> Prop :=
  tr_module_intro :
    forall data control fin rtrn st stk stk_len m start rst clk scldecls arrdecls externctrl wf,
      m = (mkmodule f.(RTL.fn_params)
                        data
                        control
                        f.(RTL.fn_entrypoint)
                        st stk stk_len fin rtrn start rst clk scldecls arrdecls externctrl wf) ->
      (forall pc i, Maps.PTree.get pc f.(RTL.fn_code) = Some i ->
               tr_code f.(RTL.fn_code) pc i data control externctrl fin rtrn st stk) ->
      stk_len = Z.to_nat (f.(RTL.fn_stacksize) / 4) ->
      Z.modulo (f.(RTL.fn_stacksize)) 4 = 0 ->
      0 <= f.(RTL.fn_stacksize) < Integers.Ptrofs.modulus ->
      (st > (RTL.max_reg_function f))%positive ->
      (fin > (RTL.max_reg_function f))%positive ->
      (rtrn > (RTL.max_reg_function f))%positive ->
      (stk > (RTL.max_reg_function f))%positive ->
      (start > (RTL.max_reg_function f))%positive ->
      (rst > (RTL.max_reg_function f))%positive ->
      (clk > (RTL.max_reg_function f))%positive ->
      tr_module f m.
Hint Constructors tr_module : htlspec.

Lemma create_reg_datapath_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_datapath_trans : htlspec.

Lemma create_reg_controllogic_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_controllogic_trans : htlspec.

Lemma create_reg_externctrl_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_externctrl_trans : htlspec.

Lemma create_reg_trans :
  forall sz s s' x i iop,
    create_reg iop sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath) /\
    s.(st_controllogic) = s'.(st_controllogic) /\
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. monadInv H. auto. Qed.
Hint Resolve create_reg_trans : htlspec.

Lemma create_reg_inv : forall a b s r s' i,
    create_reg a b s = OK r s' i ->
    r = s.(st_freshreg) /\ s'.(st_freshreg) = Pos.succ (s.(st_freshreg)).
Proof.
  inversion 1; auto.
Qed.

Lemma map_externctrl_inv : forall othermod ctrl r s s' i,
    map_externctrl othermod ctrl s = OK r s' i ->
    s.(st_externctrl) ! r = None
    /\ r = s.(st_freshreg)
    /\ s'.(st_freshreg) = Pos.succ (s.(st_freshreg))
    /\ s'.(st_externctrl) ! r = Some (othermod, ctrl).
Proof.
  intros. monadInv H.
  auto_apply create_reg_inv.
  auto_apply create_reg_externctrl_trans.
  replace (st_externctrl s).
  simplify; auto with htlspec.
Qed.

Lemma create_state_inv : forall n s s' i,
    create_state s = OK n s' i ->
    n = s.(st_freshstate).
Proof. inversion 1. trivial. Qed.

Lemma create_arr_inv : forall w x y z a b c d,
    create_arr w x y z = OK (a, b) c d ->
    y = b
    /\ a = z.(st_freshreg)
    /\ c.(st_freshreg) = Pos.succ (z.(st_freshreg)).
Proof. inversion 1; crush. Qed.

Lemma map_externctrl_datapath_trans :
  forall s s' x i om sig,
    map_externctrl om sig s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof.
  intros. monadInv H.
  auto_apply create_reg_datapath_trans.
  inv EQ; auto.
Qed.
Hint Resolve map_externctrl_datapath_trans : htlspec.

Lemma map_externctrl_controllogic_trans :
  forall s s' x i om sig,
    map_externctrl om sig s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof.
  intros. monadInv H.
  auto_apply create_reg_controllogic_trans.
  inv EQ; auto.
Qed.
Hint Resolve map_externctrl_controllogic_trans : htlspec.

Lemma declare_reg_datapath_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_datapath_trans : htlspec.

Lemma declare_reg_controllogic_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_controllogic_trans : htlspec.

Lemma declare_reg_freshreg_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_freshreg) = s'.(st_freshreg).
Proof. inversion 1; auto. Qed.
Hint Resolve declare_reg_freshreg_trans : htlspec.

Lemma declare_reg_externctrl_trans :
  forall sz s s' x i iop r,
    declare_reg iop r sz s = OK x s' i ->
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_reg_externctrl_trans : htlspec.

Lemma create_arr_datapath_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_arr_datapath_trans : htlspec.

Lemma create_arr_controllogic_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_arr_controllogic_trans : htlspec.

Lemma create_arr_externctrl_trans :
  forall sz ln s s' x i iop,
    create_arr iop sz ln s = OK x s' i ->
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_arr_externctrl_trans : htlspec.

Lemma create_state_datapath_trans :
  forall s s' x i,
    create_state s = OK x s' i ->
    s.(st_datapath) = s'.(st_datapath).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_state_datapath_trans : htlspec.

Lemma create_state_controllogic_trans :
  forall s s' x i,
    create_state s = OK x s' i ->
    s.(st_controllogic) = s'.(st_controllogic).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_state_controllogic_trans : htlspec.

Lemma create_state_externctrl_trans :
  forall s s' x i,
    create_state s = OK x s' i ->
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. monadInv H. trivial. Qed.
Hint Resolve create_state_externctrl_trans : htlspec.

Lemma add_instr_externctrl_trans :
  forall s s' x i n n' st,
    add_instr n n' st s = OK x s' i ->
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. unfold add_instr in H. repeat (unfold_match H). inv H. eauto with htlspec. Qed.
Hint Resolve add_instr_externctrl_trans : htlspec.

Lemma add_instr_wait_externctrl_trans :
  forall m n n' st s r s' i,
    add_instr_wait m n n' st s = OK r s' i ->
    s.(st_externctrl) = s'.(st_externctrl).
Proof. intros. unfold add_instr_wait in H. repeat (unfold_match H). inv H. eauto with htlspec. Qed.
Hint Resolve add_instr_wait_externctrl_trans : htlspec.

Lemma get_refl_x :
  forall s s' x i,
    get s = OK x s' i ->
    s = x.
Proof. inversion 1. trivial. Qed.
Hint Resolve get_refl_x : htlspec.

Lemma get_refl_s :
  forall s s' x i,
    get s = OK x s' i ->
    s = s'.
Proof. inversion 1. trivial. Qed.
Hint Resolve get_refl_s : htlspec.

Ltac inv_incr :=
  repeat match goal with
  | [ H: create_reg _ _ ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    pose proof H as H1;
    pose proof H as H2;
    learn H as H3;
    eapply create_reg_datapath_trans in H1;
    eapply create_reg_controllogic_trans in H2;
    eapply create_reg_externctrl_trans in H3
  | [ H: map_externctrl _ _ ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    pose proof H as H1;
    learn H as H2;
    eapply map_externctrl_datapath_trans in H1;
    eapply map_externctrl_controllogic_trans in H2
  | [ H: create_arr _ _ ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    pose proof H as H1;
    pose proof H as H2;
    learn H as H3;
    eapply create_arr_datapath_trans in H1;
    eapply create_arr_controllogic_trans in H2;
    eapply create_arr_externctrl_trans in H3
  | [ H: create_state _ _ ?s = OK _ ?s' _ |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    pose proof H as H1;
    pose proof H as H2;
    learn H as H3;
    eapply create_state_datapath_trans in H1;
    eapply create_state_controllogic_trans in H2;
    eapply create_state_externctrl_trans in H3
  | [ H: get ?s = OK _ _ _ |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    pose proof H as H1;
    learn H as H2;
    apply get_refl_x in H1;
    apply get_refl_s in H2;
    subst
  | [ H: st_prop _ _ |- _ ] => unfold st_prop in H; destruct H
  | [ H: st_incr _ _ |- _ ] => destruct st_incr
  end.

Lemma collect_controllogic_trans :
  forall A f l cs cs' ci x,
  (forall s s' x i y, f y s = OK x s' i -> s.(st_controllogic) = s'.(st_controllogic)) ->
  @HTLMonadExtra.collectlist A f l cs = OK x cs' ci -> cs.(st_controllogic) = cs'.(st_controllogic).
Proof.
  induction l; intros; monadInv H0.
  - trivial.
  - apply H in EQ. rewrite EQ. eauto.
Qed.

Lemma collect_datapath_trans :
  forall A f l cs cs' ci x,
  (forall s s' x i y, f y s = OK x s' i -> s.(st_datapath) = s'.(st_datapath)) ->
  @HTLMonadExtra.collectlist A f l cs = OK x cs' ci -> cs.(st_datapath) = cs'.(st_datapath).
Proof.
  induction l; intros; monadInv H0.
  - trivial.
  - apply H in EQ. rewrite EQ. eauto.
Qed.

Lemma collect_freshreg_trans :
  forall A f l cs cs' ci x,
  (forall s s' x i y, f y s = OK x s' i -> s.(st_freshreg) = s'.(st_freshreg)) ->
  @HTLMonadExtra.collectlist A f l cs = OK x cs' ci -> cs.(st_freshreg) = cs'.(st_freshreg).
Proof.
  induction l; intros; monadInv H0.
  - trivial.
  - apply H in EQ. rewrite EQ. eauto.
Qed.

Lemma collect_declare_controllogic_trans :
  forall io n l s s' i x,
  HTLMonadExtra.collectlist (fun r : reg => declare_reg io r n) l s = OK x s' i ->
  s.(st_controllogic) = s'.(st_controllogic).
Proof.
  intros. eapply collect_controllogic_trans; try eassumption.
  intros. eapply declare_reg_controllogic_trans. simpl in H0. eassumption.
Qed.
Hint Resolve collect_declare_controllogic_trans : htlspec.

Lemma collect_declare_datapath_trans :
  forall io n l s s' i x,
  HTLMonadExtra.collectlist (fun r : reg => declare_reg io r n) l s = OK x s' i ->
  s.(st_datapath) = s'.(st_datapath).
Proof.
  intros. eapply collect_datapath_trans; try eassumption.
  intros. eapply declare_reg_datapath_trans. simpl in H0. eassumption.
Qed.
Hint Resolve collect_declare_datapath_trans : htlspec.

Lemma collect_declare_freshreg_trans :
  forall io n l s s' i x,
  HTLMonadExtra.collectlist (fun r : reg => declare_reg io r n) l s = OK x s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  intros. eapply collect_freshreg_trans; try eassumption.
  inversion 1. auto.
Qed.

Lemma translate_eff_addressing_freshreg_trans :
  forall op args s r s' i,
  translate_eff_addressing op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
Hint Resolve translate_eff_addressing_freshreg_trans : htlspec.

Lemma translate_comparison_freshreg_trans :
  forall op args s r s' i,
  translate_comparison op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
Hint Resolve translate_comparison_freshreg_trans : htlspec.

Lemma translate_comparisonu_freshreg_trans :
  forall op args s r s' i,
  translate_comparisonu op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
Hint Resolve translate_comparisonu_freshreg_trans : htlspec.

Lemma translate_comparison_imm_freshreg_trans :
  forall op args s r s' i n,
  translate_comparison_imm op args n s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
Hint Resolve translate_comparison_imm_freshreg_trans : htlspec.

Lemma translate_comparison_immu_freshreg_trans :
  forall op args s r s' i n,
  translate_comparison_immu op args n s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; auto.
Qed.
Hint Resolve translate_comparison_immu_freshreg_trans : htlspec.

Lemma translate_condition_freshreg_trans :
  forall op args s r s' i,
  translate_condition op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; eauto with htlspec.
Qed.
Hint Resolve translate_condition_freshreg_trans : htlspec.

Lemma translate_instr_freshreg_trans :
  forall op args s r s' i,
  translate_instr op args s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  destruct op; intros; simpl in *; repeat (unfold_match H); inv H; eauto with htlspec.
  monadInv H1. eauto with htlspec.
Qed.
Hint Resolve translate_instr_freshreg_trans : htlspec.

Lemma translate_arr_access_freshreg_trans :
  forall mem addr args st s r s' i,
  translate_arr_access mem addr args st s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof.
  intros. unfold translate_arr_access in H. repeat (unfold_match H); inv H; eauto with htlspec.
Qed.
Hint Resolve translate_arr_access_freshreg_trans : htlspec.

Lemma add_instr_freshreg_trans :
  forall n n' st s r s' i,
  add_instr n n' st s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_instr in H. repeat (unfold_match H). inv H. auto. Qed.
Hint Resolve add_instr_freshreg_trans : htlspec.

Lemma add_instr_wait_freshreg_trans :
  forall m n n' st s r s' i,
  add_instr_wait m n n' st s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_instr_wait in H. repeat (unfold_match H). inv H. auto. Qed.
Hint Resolve add_instr_freshreg_trans : htlspec.

Lemma add_branch_instr_freshreg_trans :
  forall n n0 n1 e s r s' i,
  add_branch_instr e n n0 n1 s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_branch_instr in H. repeat (unfold_match H). inv H. auto. Qed.
Hint Resolve add_branch_instr_freshreg_trans : htlspec.

Lemma create_state_freshreg_trans :
  forall n s s' i,
  create_state s = OK n s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold create_state in H. inv H. auto. Qed.
Hint Resolve create_state_freshreg_trans : htlspec.

Lemma add_node_skip_freshreg_trans :
  forall n1 n2 s r s' i,
  add_node_skip n1 n2 s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_node_skip in H. repeat (unfold_match H). inv H. auto. Qed.
Hint Resolve add_node_skip_freshreg_trans : htlspec.

Lemma add_instr_skip_freshreg_trans :
  forall n1 n2 s r s' i,
  add_instr_skip n1 n2 s = OK r s' i ->
  s.(st_freshreg) = s'.(st_freshreg).
Proof. intros. unfold add_instr_skip in H. repeat (unfold_match H). inv H. auto. Qed.
Hint Resolve add_instr_skip_freshreg_trans : htlspec.

Lemma iter_expand_instr_spec :
  forall l fin rtrn stack s s' i x c,
    HTLMonadExtra.collectlist (transf_instr fin rtrn stack) l s = OK x s' i ->
    list_norepet (List.map fst l) ->
    (forall pc instr, In (pc, instr) l -> c!pc = Some instr) ->
    (forall pc instr, In (pc, instr) l -> c!pc = Some instr ->
                 tr_code c pc instr s'.(st_datapath) s'.(st_controllogic) s'.(st_externctrl) fin rtrn s'.(st_st) stack).
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
      eapply tr_code_call; crush.
      destruct (map_externctrl_params_combine _ _ _ _ _ _ EQ1) as [? [? ?]]; subst.
      repeat (eapply ex_intro).
      repeat split; try monad_crush. (* slow *)
      * intros.
        destruct (map_externctrl_params_spec _ _ _ _ _ _ _ _ EQ1 H) as [param [? ?]].
        exists param; crush; trans_step s3 s'.
    + (* Icond *) tr_code_simple_tac.
    + (* Ireturn *) eapply tr_code_return; crush; eexists; monad_crush.
  - clear EQ. (* EQ is very big and sauto gets lost *)
    sauto q: on.
Qed.
Hint Resolve iter_expand_instr_spec : htlspec.

Lemma map_incr_some : forall {A} map (s s' : st) idx (x : A),
    (map s) ! idx = Some x ->
    map_incr map s s' ->
    (map s') ! idx = Some x.
Proof. intros * ? Hincr. destruct Hincr with idx; crush. Qed.
Hint Resolve map_incr_some : htlspec.

Lemma tr_code_trans : forall c pc instr fin rtrn stack s s',
  tr_code c pc instr (st_datapath s) (st_controllogic s) (st_externctrl s) fin rtrn (st_st s) stack ->
  st_prop s s' ->
  tr_code c pc instr (st_datapath s') (st_controllogic s') (st_externctrl s') fin rtrn (st_st s') stack.
Proof.
  intros * Htr Htrans.
  destruct Htr.
  + eapply tr_code_single.
    * trans_step s s'.
    * inversion Htrans.
      destruct H6 with pc. crush.
      rewrite H11. eauto.
    * inversion Htrans.
      destruct H7 with pc. crush.
      rewrite H11. eauto.
    * inversion Htrans. crush.
  + eapply tr_code_call; eauto with htlspec.
    simplify.
    inversion Htrans.
    replace (st_st s').
    repeat eexists; try (eapply map_incr_some; inversion Htrans; eauto with htlspec); try eauto with htlspec; admit.
  + eapply tr_code_return; eauto with htlspec.
    inversion Htrans.
    simplify. eexists.
    replace (st_st s').
    repeat split; eauto with htlspec.
    Unshelve. eauto.
Admitted.
Hint Resolve tr_code_trans : htlspec.

Hint Resolve PTree.elements_complete : htlspec.

Theorem transl_module_correct :
  forall i f m,
    transl_module i f = Errors.OK m -> tr_module f m.
Proof.
  intros * H.
  unfold transl_module in *.
  unfold run_mon in *.
  unfold_match H.
  inv H.
  inversion s; subst.

  unfold transf_module in *.
  unfold stack_correct in *.
  unfold_match Heqr.
  destruct (0 <=? RTL.fn_stacksize f) eqn:STACK_BOUND_LOW;
    destruct (RTL.fn_stacksize f <? Integers.Ptrofs.modulus) eqn:STACK_BOUND_HIGH;
    destruct (RTL.fn_stacksize f mod 4 =? 0) eqn:STACK_ALIGN;
    crush.
  monadInv Heqr.

  repeat unfold_match EQ9. monadInv EQ9.

  monadInv EQ7.
  econstructor; eauto with htlspec.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
Admitted.
