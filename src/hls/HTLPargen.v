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

Require Import Coq.micromega.Lia.

Require Import compcert.common.AST.
Require compcert.common.Errors.
Require compcert.common.Globalenvs.
Require compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.FunctionalUnits.
Require Import vericert.hls.HTL.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Gible.
Require Import vericert.hls.FunctionalUnits.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.

#[local] Hint Resolve AssocMap.gempty : htlh.
#[local] Hint Resolve AssocMap.gso : htlh.
#[local] Hint Resolve AssocMap.gss : htlh.
#[local] Hint Resolve Ple_refl : htlh.
#[local] Hint Resolve Ple_succ : htlh.

Definition assignment : Type := expr -> expr -> stmnt.

Record state: Type := mkstate {
  st_st: reg;
  st_freshreg: reg;
  st_freshstate: node;
  st_scldecls: AssocMap.t (option io * scl_decl);
  st_arrdecls: AssocMap.t (option io * arr_decl);
  st_datapath: datapath;
  st_controllogic: controllogic;
}.

Definition init_state (st : reg) : state :=
  mkstate st
          1%positive
          1%positive
          (AssocMap.empty (option io * scl_decl))
          (AssocMap.empty (option io * arr_decl))
          (AssocMap.empty stmnt)
          (AssocMap.empty stmnt).

Module HTLState <: State.

  Definition st := state.

  Inductive st_incr: state -> state -> Prop :=
    state_incr_intro:
      forall (s1 s2: state),
        st_st s1 = st_st s2 ->
        Ple s1.(st_freshreg) s2.(st_freshreg) ->
        Ple s1.(st_freshstate) s2.(st_freshstate) ->
        (forall n,
            s1.(st_controllogic)!n = None
            \/ s2.(st_controllogic)!n = s1.(st_controllogic)!n) ->
        st_incr s1 s2.
  #[local] Hint Constructors st_incr : htlh.

  Definition st_prop := st_incr.
  #[local] Hint Unfold st_prop : htlh.

  Lemma st_refl : forall s, st_prop s s.
  Proof. auto with htlh. Qed.

  Lemma st_trans :
    forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
  Proof.
    intros. inv H. inv H0.
    apply state_incr_intro; eauto using Ple_trans; intros; try congruence.
    destruct H4 with n; destruct H7 with n; intuition congruence.
  Qed.

End HTLState.
Export HTLState.

Module HTLMonad := Statemonad(HTLState).
Export HTLMonad.

Module HTLMonadExtra := Monad.MonadExtra(HTLMonad).
Import HTLMonadExtra.
Export MonadNotation.
#[local] Open Scope monad_scope.

Fixpoint pred_expr (preg: reg) (p: pred_op) :=
  match p with
  | Plit (b, pred) =>
    if b
    then Vrange preg (Vlit (posToValue pred)) (Vlit (posToValue pred))
    else Vunop Vnot (Vrange preg (Vlit (posToValue pred)) (Vlit (posToValue pred)))
  | Ptrue => Vlit (ZToValue 1)
  | Pfalse => Vlit (ZToValue 0)
  | Pand p1 p2 =>
    Vbinop Vand (pred_expr preg p1) (pred_expr preg p2)
  | Por p1 p2 =>
    Vbinop Vor (pred_expr preg p1) (pred_expr preg p2)
  end.

Definition translate_predicate (a : assignment)
           (preg: reg) (p: option pred_op) (dst e: expr) :=
  match p with
  | None => a dst e
  | Some pos =>
    a dst (Vternary (pred_expr preg pos) e dst)
  end.

Definition state_goto (preg: reg) (p: option pred_op) (st : reg) (n : node) : stmnt :=
  translate_predicate Vblock preg p (Vvar st) (Vlit (posToValue n)).

Definition state_cond (preg: reg) (p: option pred_op) (st : reg) (c : expr) (n1 n2 : node) : stmnt :=
  translate_predicate Vblock preg p (Vvar st) (Vternary c (posToExpr n1) (posToExpr n2)).

Definition check_empty_node_datapath:
  forall (s: state) (n: node), { s.(st_datapath)!n = None } + { True }.
Proof.
  intros. case (s.(st_datapath)!n); tauto.
Defined.

Definition check_empty_node_controllogic:
  forall (s: state) (n: node), { s.(st_controllogic)!n = None } + { True }.
Proof.
  intros. case (s.(st_controllogic)!n); tauto.
Defined.

Lemma declare_reg_state_incr :
  forall i s r sz,
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       s.(st_freshstate)
       (AssocMap.set r (i, VScalar sz) s.(st_scldecls))
       s.(st_arrdecls)
       s.(st_datapath)
       s.(st_controllogic)).
Proof. Admitted.

Definition declare_reg (i : option io) (r : reg) (sz : nat) : mon unit :=
  fun s => OK tt (mkstate
                s.(st_st)
                s.(st_freshreg)
                s.(st_freshstate)
                (AssocMap.set r (i, VScalar sz) s.(st_scldecls))
                s.(st_arrdecls)
                s.(st_datapath)
                s.(st_controllogic))
              (declare_reg_state_incr i s r sz).

Lemma declare_arr_state_incr :
  forall i s r sz ln,
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       s.(st_freshstate)
       s.(st_scldecls)
       (AssocMap.set r (i, VArray sz ln) s.(st_arrdecls))
       s.(st_datapath)
       s.(st_controllogic)).
Proof. Admitted.

Definition declare_arr (i : option io) (r : reg) (sz : nat) (ln : nat) : mon unit :=
  fun s => OK tt (mkstate
                s.(st_st)
                s.(st_freshreg)
                s.(st_freshstate)
                s.(st_scldecls)
                (AssocMap.set r (i, VArray sz ln) s.(st_arrdecls))
                s.(st_datapath)
                s.(st_controllogic))
              (declare_arr_state_incr i s r sz ln).

Lemma add_instr_state_incr :
  forall s preg p n n' st,
    (st_controllogic s)!n = None ->
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (st_freshstate s)
       s.(st_scldecls)
       s.(st_arrdecls)
       (AssocMap.set n st s.(st_datapath))
       (AssocMap.set n (state_goto preg p s.(st_st) n') s.(st_controllogic))).
Proof.
  constructor; intros;
    try (simpl; destruct (peq n n0); subst);
    auto with htlh.
Qed.

Definition add_instr (preg: reg) (p: option pred_op) (n : node) (n' : node) (st : stmnt) : mon unit :=
  fun s =>
    match check_empty_node_controllogic s n with
    | left TRANS =>
      OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (AssocMap.set n st s.(st_datapath))
               (AssocMap.set n (state_goto preg p s.(st_st) n') s.(st_controllogic)))
         (add_instr_state_incr s preg p n n' st TRANS)
    | _ => Error (Errors.msg "HTL.add_instr")
    end.

Lemma add_instr_skip_state_incr :
  forall s n st,
    (st_controllogic s)!n = None ->
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (st_freshstate s)
       s.(st_scldecls)
       s.(st_arrdecls)
       (AssocMap.set n st s.(st_datapath))
       (AssocMap.set n Vskip s.(st_controllogic))).
Proof.
  constructor; intros;
    try (simpl; destruct (peq n n0); subst);
    auto with htlh.
Qed.

Definition add_instr_skip (n : node) (st : stmnt) : mon unit :=
  fun s =>
    match check_empty_node_controllogic s n with
    | left TRANS =>
      OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (AssocMap.set n st s.(st_datapath))
               (AssocMap.set n Vskip s.(st_controllogic)))
         (add_instr_skip_state_incr s n st TRANS)
    | _ => Error (Errors.msg "HTL.add_instr_skip")
    end.

Lemma add_node_skip_state_incr :
  forall s n st,
    (st_controllogic s)!n = None ->
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (st_freshstate s)
       s.(st_scldecls)
       s.(st_arrdecls)
       (AssocMap.set n Vskip s.(st_datapath))
       (AssocMap.set n st s.(st_controllogic))).
Proof.
  constructor; intros;
    try (simpl; destruct (peq n n0); subst);
    auto with htlh.
Qed.

Definition add_node_skip (n : node) (st : stmnt) : mon unit :=
  fun s =>
    match check_empty_node_controllogic s n with
    | left TRANS =>
      OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (AssocMap.set n Vskip s.(st_datapath))
               (AssocMap.set n st s.(st_controllogic)))
         (add_node_skip_state_incr s n st TRANS)
    | _ => Error (Errors.msg "HTL.add_node_skip")
    end.

Definition nonblock (dst : reg) (e : expr) := Vnonblock (Vvar dst) e.
Definition block (dst : reg) (e : expr) := Vblock (Vvar dst) e.

Definition bop (op : binop) (r1 r2 : reg) : expr :=
  Vbinop op (Vvar r1) (Vvar r2).

Definition boplit (op : binop) (r : reg) (l : Integers.int) : expr :=
  Vbinop op (Vvar r) (Vlit (intToValue l)).

Definition boplitz (op: binop) (r: reg) (l: Z) : expr :=
  Vbinop op (Vvar r) (Vlit (ZToValue l)).

Definition translate_comparison (c : Integers.comparison) (args : list reg)
  : mon expr :=
  match c, args with
  | Integers.Ceq, r1::r2::nil => ret (bop Veq r1 r2)
  | Integers.Cne, r1::r2::nil => ret (bop Vne r1 r2)
  | Integers.Clt, r1::r2::nil => ret (bop Vlt r1 r2)
  | Integers.Cgt, r1::r2::nil => ret (bop Vgt r1 r2)
  | Integers.Cle, r1::r2::nil => ret (bop Vle r1 r2)
  | Integers.Cge, r1::r2::nil => ret (bop Vge r1 r2)
  | _, _ => error (Errors.msg
                 "Htlgen: comparison instruction not implemented: other")
  end.

Definition translate_comparison_imm (c : Integers.comparison) (args : list reg)
           (i: Integers.int) : mon expr :=
  match c, args with
  | Integers.Ceq, r1::nil => ret (boplit Veq r1 i)
  | Integers.Cne, r1::nil => ret (boplit Vne r1 i)
  | Integers.Clt, r1::nil => ret (boplit Vlt r1 i)
  | Integers.Cgt, r1::nil => ret (boplit Vgt r1 i)
  | Integers.Cle, r1::nil => ret (boplit Vle r1 i)
  | Integers.Cge, r1::nil => ret (boplit Vge r1 i)
  | _, _ => error (Errors.msg
                 "Htlgen: comparison_imm instruction not implemented: other")
  end.

Definition translate_comparisonu (c : Integers.comparison) (args : list reg)
  : mon expr :=
  match c, args with
  | Integers.Clt, r1::r2::nil => ret (bop Vltu r1 r2)
  | Integers.Cgt, r1::r2::nil => ret (bop Vgtu r1 r2)
  | Integers.Cle, r1::r2::nil => ret (bop Vleu r1 r2)
  | Integers.Cge, r1::r2::nil => ret (bop Vgeu r1 r2)
  | _, _ => error (Errors.msg
                 "Htlgen: comparison instruction not implemented: other")
  end.

Definition translate_comparison_immu (c : Integers.comparison)
           (args : list reg) (i: Integers.int) : mon expr :=
  match c, args with
  | Integers.Clt, r1::nil => ret (boplit Vltu r1 i)
  | Integers.Cgt, r1::nil => ret (boplit Vgtu r1 i)
  | Integers.Cle, r1::nil => ret (boplit Vleu r1 i)
  | Integers.Cge, r1::nil => ret (boplit Vgeu r1 i)
  | _, _ => error (Errors.msg
                 "Htlgen: comparison_imm instruction not implemented: other")
  end.

Definition translate_condition (c : Op.condition) (args : list reg)
  : mon expr :=
  match c, args with
  | Op.Ccomp c, _ => translate_comparison c args
  | Op.Ccompu c, _ => translate_comparisonu c args
  | Op.Ccompimm c i, _ => translate_comparison_imm c args i
  | Op.Ccompuimm c i, _ => translate_comparison_immu c args i
  | Op.Cmaskzero n, _ =>
    error (Errors.msg "Htlgen: condition instruction not implemented: Cmaskzero")
  | Op.Cmasknotzero n, _ =>
    error (Errors.msg
         "Htlgen: condition instruction not implemented: Cmasknotzero")
  | _, _ =>
    error (Errors.msg "Htlgen: condition instruction not implemented: other")
  end.

Definition check_address_parameter_signed (p : Z) : bool :=
  Z.leb Integers.Ptrofs.min_signed p
  && Z.leb p Integers.Ptrofs.max_signed.

Definition check_address_parameter_unsigned (p : Z) : bool :=
  Z.leb p Integers.Ptrofs.max_unsigned.

Lemma create_reg_state_incr:
  forall s sz i,
    st_incr s (mkstate
         s.(st_st)
         (Pos.succ (st_freshreg s))
         (st_freshstate s)
         (AssocMap.set s.(st_freshreg) (i, VScalar sz) s.(st_scldecls))
         s.(st_arrdecls)
         (st_datapath s)
         (st_controllogic s)).
Proof. constructor; simpl; auto with htlh. Qed.

Definition create_reg (i : option io) (sz : nat) : mon reg :=
  fun s => let r := s.(st_freshreg) in
           OK r (mkstate
                   s.(st_st)
                   (Pos.succ r)
                   (st_freshstate s)
                   (AssocMap.set s.(st_freshreg) (i, VScalar sz) s.(st_scldecls))
                   (st_arrdecls s)
                   (st_datapath s)
                   (st_controllogic s))
              (create_reg_state_incr s sz i).

Definition translate_eff_addressing (a: Op.addressing) (args: list reg)
  : mon expr :=
  match a, args with (* TODO: We should be more methodical here; what are the possibilities?*)
  | Op.Aindexed off, r1::nil =>
    if (check_address_parameter_signed off)
    then ret (boplitz Vadd r1 off)
    else error (Errors.msg ("HTLPargen: translate_eff_addressing (Aindexed): address out of bounds"))
  | Op.Ascaled scale offset, r1::nil =>
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then ret (Vbinop Vadd (boplitz Vmul r1 scale) (Vlit (ZToValue offset)))
    else error (Errors.msg "HTLPargen: translate_eff_addressing (Ascaled): address out of bounds")
  | Op.Aindexed2 offset, r1::r2::nil =>
    if (check_address_parameter_signed offset)
    then ret (Vbinop Vadd (bop Vadd r1 r2) (Vlit (ZToValue offset)))
    else error (Errors.msg "HTLPargen: translate_eff_addressing (Aindexed2): address out of bounds")
  | Op.Aindexed2scaled scale offset, r1::r2::nil => (* Typical for dynamic array addressing *)
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then ret (Vbinop Vadd (Vvar r1) (Vbinop Vadd (boplitz Vmul r2 scale) (Vlit (ZToValue offset))))
    else error (Errors.msg "HTLPargen: translate_eff_addressing (Aindexed2scaled): address out of bounds")
  | Op.Ainstack a, nil => (* We need to be sure that the base address is aligned *)
    let a := Integers.Ptrofs.unsigned a in
    if (check_address_parameter_unsigned a)
    then ret (Vlit (ZToValue a))
    else error (Errors.msg "HTLPargen: translate_eff_addressing (Ainstack): address out of bounds")
  | _, _ => error (Errors.msg "HTLPargen: translate_eff_addressing unsuported addressing")
  end.

(*|
Translate an instruction to a statement. FIX mulhs mulhu
|*)

Definition translate_instr (op : Op.operation) (args : list reg) : mon expr :=
  match op, args with
  | Op.Omove, r::nil => ret (Vvar r)
  | Op.Ointconst n, _ => ret (Vlit (intToValue n))
  | Op.Oneg, r::nil => ret (Vunop Vneg (Vvar r))
  | Op.Osub, r1::r2::nil => ret (bop Vsub r1 r2)
  | Op.Omul, r1::r2::nil => ret (bop Vmul r1 r2)
  | Op.Omulimm n, r::nil => ret (boplit Vmul r n)
  | Op.Omulhs, r1::r2::nil => error (Errors.msg "Htlgen: Instruction not implemented: mulhs")
  | Op.Omulhu, r1::r2::nil => error (Errors.msg "Htlgen: Instruction not implemented: mulhu")
  | Op.Odiv, r1::r2::nil => ret (bop Vdiv r1 r2)
  | Op.Odivu, r1::r2::nil => ret (bop Vdivu r1 r2)
  | Op.Omod, r1::r2::nil => ret (bop Vmod r1 r2)
  | Op.Omodu, r1::r2::nil => ret (bop Vmodu r1 r2)
  | Op.Oand, r1::r2::nil => ret (bop Vand r1 r2)
  | Op.Oandimm n, r::nil => ret (boplit Vand r n)
  | Op.Oor, r1::r2::nil => ret (bop Vor r1 r2)
  | Op.Oorimm n, r::nil => ret (boplit Vor r n)
  | Op.Oxor, r1::r2::nil => ret (bop Vxor r1 r2)
  | Op.Oxorimm n, r::nil => ret (boplit Vxor r n)
  | Op.Onot, r::nil => ret (Vunop Vnot (Vvar r))
  | Op.Oshl, r1::r2::nil => ret (bop Vshl r1 r2)
  | Op.Oshlimm n, r::nil => ret (boplit Vshl r n)
  | Op.Oshr, r1::r2::nil => ret (bop Vshr r1 r2)
  | Op.Oshrimm n, r::nil => ret (boplit Vshr r n)
  | Op.Oshrximm n, r::nil =>
    ret (Vternary (Vbinop Vlt (Vvar r) (Vlit (ZToValue 0)))
                  (Vunop Vneg (Vbinop Vshru (Vunop Vneg (Vvar r)) (Vlit n)))
                  (Vbinop Vshru (Vvar r) (Vlit n)))
  | Op.Oshru, r1::r2::nil => ret (bop Vshru r1 r2)
  | Op.Oshruimm n, r::nil => ret (boplit Vshru r n)
  | Op.Ororimm n, r::nil => error (Errors.msg "Htlgen: Instruction not implemented: Ororimm")
  (*ret (Vbinop Vor (boplit Vshru r (Integers.Int.modu n (Integers.Int.repr 32)))
                                        (boplit Vshl r (Integers.Int.sub (Integers.Int.repr 32) (Integers.Int.modu n (Integers.Int.repr 32)))))*)
  | Op.Oshldimm n, r::nil => ret (Vbinop Vor (boplit Vshl r n) (boplit Vshr r (Integers.Int.sub (Integers.Int.repr 32) n)))
  | Op.Ocmp c, _ => translate_condition c args
  | Op.Osel c AST.Tint, r1::r2::rl =>
    do tc <- translate_condition c rl;
    ret (Vternary tc (Vvar r1) (Vvar r2))
  | Op.Olea a, _ => translate_eff_addressing a args
  | Op.Omac, r1::r2::r3::nil => ret (Vbinop Vadd (Vvar r1) (bop Vmul r2 r3))
  | _, _ => error (Errors.msg "Htlgen: Instruction not implemented: other")
  end.

Lemma add_branch_instr_state_incr:
  forall s preg p e n n1 n2,
    (st_controllogic s) ! n = None ->
    st_incr s (mkstate
                 s.(st_st)
                (st_freshreg s)
                (st_freshstate s)
                s.(st_scldecls)
                s.(st_arrdecls)
                (AssocMap.set n Vskip (st_datapath s))
                (AssocMap.set n (state_cond preg p s.(st_st) e n1 n2) (st_controllogic s))).
Proof.
  intros. apply state_incr_intro; simpl;
            try (intros; destruct (peq n0 n); subst);
            auto with htlh.
Qed.

Definition add_branch_instr preg p (e: expr) (n n1 n2: node) : mon unit :=
  fun s =>
    match check_empty_node_controllogic s n with
    | left NTRANS =>
      OK tt (mkstate
               s.(st_st)
                (st_freshreg s)
                (st_freshstate s)
                s.(st_scldecls)
                s.(st_arrdecls)
                (AssocMap.set n Vskip (st_datapath s))
                (AssocMap.set n (state_cond preg p s.(st_st) e n1 n2) (st_controllogic s)))
         (add_branch_instr_state_incr s preg p e n n1 n2 NTRANS)
    | _ => Error (Errors.msg "Htlgen: add_branch_instr")
    end.

Fixpoint enumerate (i : nat) (ns : list node) {struct ns} : list (nat * node) :=
  match ns with
  | n :: ns' => (i, n) :: enumerate (i+1) ns'
  | nil => nil
  end.

Definition tbl_to_case_expr (st : reg) (ns : list node) : list (expr * stmnt) :=
  List.map (fun a => match a with
                    (i, n) => (Vlit (natToValue i), Vblock (Vvar st) (Vlit (posToValue n)))
                  end)
           (enumerate 0 ns).

Definition stack_correct (sz : Z) : bool :=
  (0 <=? sz) && (sz <? Integers.Ptrofs.modulus) && (Z.modulo sz 4 =? 0).

Lemma create_arr_state_incr:
  forall s sz ln i,
    st_incr s (mkstate
         s.(st_st)
         (Pos.succ (st_freshreg s))
         (st_freshstate s)
         s.(st_scldecls)
         (AssocMap.set s.(st_freshreg) (i, VArray sz ln) s.(st_arrdecls))
         (st_datapath s)
         (st_controllogic s)).
Proof. constructor; simpl; auto with htlh. Qed.

Definition create_arr (i : option io) (sz : nat) (ln : nat) : mon (reg * nat) :=
  fun s => let r := s.(st_freshreg) in
           OK (r, ln) (mkstate
                   s.(st_st)
                   (Pos.succ r)
                   (st_freshstate s)
                   s.(st_scldecls)
                   (AssocMap.set s.(st_freshreg) (i, VArray sz ln) s.(st_arrdecls))
                   (st_datapath s)
                   (st_controllogic s))
              (create_arr_state_incr s sz ln i).

Definition max_pc_map (m : Maps.PTree.t stmnt) :=
  PTree.fold (fun m pc i => Pos.max m pc) m 1%positive.

Lemma max_pc_map_sound:
  forall m pc i, m!pc = Some i -> Ple pc (max_pc_map m).
Proof.
  intros until i.
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto.
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
  inv H2. unfold Ple, Plt in *. lia.
  apply Ple_trans with a. auto.
  unfold Ple, Plt in *. lia.
Qed.

Lemma max_pc_wf :
  forall m, Z.pos (max_pc_map m) <= Integers.Int.max_unsigned ->
            map_well_formed m.
Proof.
  unfold map_well_formed. intros.
  exploit list_in_map_inv. eassumption. intros [x [A B]]. destruct x.
  apply Maps.PTree.elements_complete in B. apply max_pc_map_sound in B.
  unfold Ple in B. apply Pos2Z.pos_le_pos in B. subst.
  simplify. transitivity (Z.pos (max_pc_map m)); eauto.
Qed.

Definition poslength {A : Type} (l : list A) : positive :=
  match Zlength l with
  | Z.pos p => p
  | _ => 1
  end.

Fixpoint penumerate {A : Type} (p : positive) (l : list A) {struct l}
  : list (positive * A) :=
  match l with
  | x :: xs => (p, x) :: penumerate (Pos.pred p) xs
  | nil => nil
  end.

Fixpoint prange {A: Type} (p1 p2: positive) (l: list A) {struct l} :=
  match l with
  | x :: xs => (p1, p2, x) :: prange p2 (Pos.pred p2) xs
  | nil => nil
  end.

Lemma add_data_instr_state_incr :
  forall s n st,
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (st_freshstate s)
       s.(st_scldecls)
       s.(st_arrdecls)
       (AssocMap.set n (Vseq (AssocMapExt.get_default
                            _ Vskip n s.(st_datapath)) st) s.(st_datapath))
       s.(st_controllogic)).
Proof.
  constructor; intros;
    try (simpl; destruct (peq n n0); subst);
    auto with htlh.
Qed.

Definition add_data_instr (n : node) (st : stmnt) : mon unit :=
  fun s =>
    OK tt (mkstate
         s.(st_st)
         s.(st_freshreg)
         (st_freshstate s)
         s.(st_scldecls)
         s.(st_arrdecls)
         (AssocMap.set n (Vseq (AssocMapExt.get_default _ Vskip n s.(st_datapath)) st) s.(st_datapath))
         s.(st_controllogic))
       (add_data_instr_state_incr s n st).

Lemma add_control_instr_state_incr :
  forall s n st,
  (st_controllogic s) ! n = None ->
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (st_freshstate s)
       s.(st_scldecls)
       s.(st_arrdecls)
       s.(st_datapath)
       (AssocMap.set n st s.(st_controllogic))).
Proof.
  constructor; intros;
    try (simpl; destruct (peq n n0); subst);
    auto with htlh.
Qed.

Definition add_control_instr (n : node) (st : stmnt) : mon unit :=
  fun s =>
    match check_empty_node_controllogic s n with
    | left CTRL =>
      OK tt (mkstate
           s.(st_st)
           s.(st_freshreg)
           (st_freshstate s)
           s.(st_scldecls)
           s.(st_arrdecls)
           s.(st_datapath)
           (AssocMap.set n st s.(st_controllogic)))
         (add_control_instr_state_incr s n st CTRL)
    | _ =>
      Error (Errors.msg "HTLPargen.add_control_instr: control logic is not empty")
    end.

Definition add_control_instr_force_state_incr :
  forall s n st,
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (st_freshstate s)
       s.(st_scldecls)
       s.(st_arrdecls)
       s.(st_datapath)
       (AssocMap.set n st s.(st_controllogic))).
Admitted.

Definition update_control_instr (n : node) (st : stmnt) : mon unit :=
  fun s =>
    match s.(st_controllogic) ! n with
    | Some st' =>
      OK tt (mkstate
           s.(st_st)
           s.(st_freshreg)
           (st_freshstate s)
           s.(st_scldecls)
           s.(st_arrdecls)
           s.(st_datapath)
           (AssocMap.set n (Vseq st' st) s.(st_controllogic)))
         (add_control_instr_force_state_incr s n (Vseq st' st))
    | None =>
      OK tt (mkstate
           s.(st_st)
           s.(st_freshreg)
           (st_freshstate s)
           s.(st_scldecls)
           s.(st_arrdecls)
           s.(st_datapath)
           (AssocMap.set n st s.(st_controllogic)))
         (add_control_instr_force_state_incr s n st)
    end.

Definition add_control_instr_force (n : node) (st : stmnt) : mon unit :=
  fun s =>
    OK tt (mkstate
      s.(st_st)
      s.(st_freshreg)
      (st_freshstate s)
      s.(st_scldecls)
      s.(st_arrdecls)
      s.(st_datapath)
      (AssocMap.set n st s.(st_controllogic)))
   (add_control_instr_force_state_incr s n st).

Definition add_control_instr_try (n : node) (st : stmnt) : mon unit :=
  fun s =>
    match check_empty_node_controllogic s n with
    | left CTRL =>
      OK tt (mkstate
           s.(st_st)
           s.(st_freshreg)
           (st_freshstate s)
           s.(st_scldecls)
           s.(st_arrdecls)
           s.(st_datapath)
           (AssocMap.set n st s.(st_controllogic)))
         (add_control_instr_state_incr s n st CTRL)
    | _ =>
      OK tt s (st_refl s)
    end.

Definition translate_arr_access (mem : AST.memory_chunk) (addr : Op.addressing)
           (args : list reg) (stack : reg) : mon expr :=
  match mem, addr, args with (* TODO: We should be more methodical here; what are the possibilities?*)
  | Mint32, Op.Aindexed off, r1::nil =>
    if (check_address_parameter_signed off)
    then ret (Vvari stack (Vbinop Vdivu (boplitz Vadd r1 off) (Vlit (ZToValue 4))))
    else error (Errors.msg "HTLgen: translate_arr_access address out of bounds")
  | Mint32, Op.Aindexed2scaled scale offset, r1::r2::nil => (* Typical for dynamic array addressing *)
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then ret (Vvari stack
                    (Vbinop Vdivu
                            (Vbinop Vadd (boplitz Vadd r1 offset) (boplitz Vmul r2 scale))
                            (Vlit (ZToValue 4))))
    else error (Errors.msg "HTLgen: translate_arr_access address out of bounds")
  | Mint32, Op.Ainstack a, nil => (* We need to be sure that the base address is aligned *)
    let a := Integers.Ptrofs.unsigned a in
    if (check_address_parameter_unsigned a)
    then ret (Vvari stack (Vlit (ZToValue (a / 4))))
    else error (Errors.msg "HTLgen: eff_addressing out of bounds stack offset")
  | _, _, _ => error (Errors.msg "HTLgen: translate_arr_access unsuported addressing")
  end.

Lemma create_new_state_state_incr:
  forall s p,
  st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       (s.(st_freshstate) + p)%positive
       s.(st_scldecls)
       s.(st_arrdecls)
       s.(st_datapath)
       s.(st_controllogic)).
Admitted.

Definition create_new_state (p: node): mon node :=
  fun s => OK s.(st_freshstate)
              (mkstate
                s.(st_st)
                s.(st_freshreg)
                (s.(st_freshstate) + p)%positive
                s.(st_scldecls)
                s.(st_arrdecls)
                s.(st_datapath)
                s.(st_controllogic))
              (create_new_state_state_incr s p).

Definition translate_cfi' (fin rtrn preg: reg) p (cfi: cf_instr)
  : mon (stmnt * stmnt) :=
  match cfi with
  | RBgoto n' =>
    do st <- get;
    ret (Vskip, state_goto preg p st.(st_st) n')
  | RBcond c args n1 n2 =>
    do st <- get;
    do e <- translate_condition c args;
    ret (Vskip, state_cond preg p st.(st_st) e n1 n2)
  | RBreturn r =>
    match r with
    | Some r' =>
      ret ((Vseq (block fin (Vlit (ZToValue 1%Z))) (block rtrn (Vvar r'))),
           Vskip)
    | None =>
      ret ((Vseq (block fin (Vlit (ZToValue 1%Z))) (block rtrn (Vlit (ZToValue 0%Z)))),
           Vskip)
    end
  | RBjumptable r tbl =>
    do s <- get;
    ret (Vskip, Vcase (Vvar r) (list_to_stmnt (tbl_to_case_expr s.(st_st) tbl)) (Some Vskip))
  | RBcall sig ri rl r n =>
    error (Errors.msg "HTLPargen: RPcall not supported.")
  | RBtailcall sig ri lr =>
    error (Errors.msg "HTLPargen: RPtailcall not supported.")
  | RBbuiltin e lb b n =>
    error (Errors.msg "HTLPargen: RPbuildin not supported.")
  end.

Definition translate_cfi (fin rtrn preg: reg) p (ni: node * cf_instr) : mon unit :=
  let (n, cfi) := ni in
  do (s, c) <- translate_cfi' fin rtrn preg p cfi;
  do _ <- update_control_instr n c;
  add_data_instr n s.

Definition translate_inst a (fin rtrn preg stack : reg) (n : node) (i : instr) :=
  match i with
  | RBnop =>
    do stmnt <- ret Vskip;
    add_data_instr n stmnt
  | RBop p op args dst =>
    do instr <- translate_instr op args;
    do _ <- declare_reg None dst 32;
    add_data_instr n (translate_predicate a preg p (Vvar dst) instr)
  | RBload p mem addr args dst =>
    do src <- translate_arr_access mem addr args stack;
    do _ <- declare_reg None dst 32;
    add_data_instr n (translate_predicate a preg p (Vvar dst) src)
  | RBstore p mem addr args src =>
    do dst <- translate_arr_access mem addr args stack;
    add_data_instr n (translate_predicate a preg p dst (Vvar src))
  | RBsetpred _ c args p =>
    do cond <- translate_condition c args;
    do stmnt <- ret (a (pred_expr preg (Plit (true, p))) cond);
    add_data_instr n stmnt
  | RBexit p cf =>
    translate_cfi fin rtrn preg p (n, cf)
  end.

Definition translate_inst_list (fin rtrn preg stack: reg) (ni : node * node * list (list instr)) :=
  match ni with
  | (n, p, li) =>
      do st <- get;
      do _ <- add_control_instr n (state_goto preg None st.(st_st) p);
      collectlist (fun l => translate_inst Vblock fin rtrn preg stack n l) (concat li)
  end.

Definition transf_bblock (fin rtrn preg stack: reg) (ni : node * ParBB.t)
  : mon unit :=
  let (n, bb) := ni in
  do nstate <- create_new_state ((poslength bb))%positive;
  do _ <- add_control_instr nstate Vskip;
  collectlist (translate_inst_list fin rtrn preg stack)
                      (prange n (nstate + poslength bb - 1)%positive
                                  bb).

(*Definition decide_order a b c d e f g : {module_ordering a b c d e f g} + {True}.
  refine (match bool_dec ((a <? b) && (b <? c) && (c <? d)
                          && (d <? e) && (e <? f) && (f <? g))%positive true with
          | left t => left _
          | _ => _
          end); auto.
  simplify; repeat match goal with
                   | H: context[(_ <? _)%positive] |- _ => apply Pos.ltb_lt in H
                   end; unfold module_ordering; auto.
Defined.*)

Lemma clk_greater :
  forall ram clk r',
    Some ram = Some r' -> (clk < ram_addr r')%positive.
Proof. Admitted.

Definition declare_ram (r: ram) : mon unit :=
  do _ <- declare_reg None r.(ram_en) 1;
  do _ <- declare_reg None r.(ram_u_en) 1;
  do _ <- declare_reg None r.(ram_wr_en) 1;
  do _ <- declare_reg None r.(ram_addr) 32;
  do _ <- declare_reg None r.(ram_d_in) 32;
  do _ <- declare_reg None r.(ram_d_out) 32;
  do _ <- declare_arr None r.(ram_mem) 32 r.(ram_size);
  ret tt.

Definition transf_module (f: function) : mon HTL.module :=
  if stack_correct f.(fn_stacksize) then
    do fin <- create_reg (Some Voutput) 1;
    do rtrn <- create_reg (Some Voutput) 32;
    do preg <- create_reg None 128;
    do (stack, stack_len) <- create_arr None 32 (Z.to_nat (f.(fn_stacksize) / 4));
    do _ <- collectlist (transf_bblock fin rtrn preg stack)
                        (Maps.PTree.elements f.(fn_code));
    do _ <- collectlist (fun r => declare_reg (Some Vinput) r 32)
                        f.(fn_params);
    do start <- create_reg (Some Vinput) 1;
    do rst <- create_reg (Some Vinput) 1;
    do clk <- create_reg (Some Vinput) 1;
    do r_en <- create_reg None 1;
    do r_u_en <- create_reg None 1;
    do r_addr <- create_reg None 32;
    do r_wr_en <- create_reg None 1;
    do r_d_in <- create_reg None 32;
    do r_d_out <- create_reg None 32;
    do current_state <- get;
    match zle (Z.pos (max_pc_map current_state.(st_datapath)))
              Integers.Int.max_unsigned,
      zle (Z.pos (max_pc_map current_state.(st_controllogic)))
          Integers.Int.max_unsigned,
      max_list_dec (fn_params f) (st_st current_state)
    with
    | left LEDATA, left LECTRL, left WFPARAMS =>
        ret (HTL.mkmodule
        f.(fn_params)
        current_state.(st_datapath)
        current_state.(st_controllogic)
        f.(fn_entrypoint)
        current_state.(st_st)
        fin
        rtrn
        start
        rst
        clk
        current_state.(st_scldecls)
        current_state.(st_arrdecls)
        (mk_ram stack_len stack r_en r_u_en r_addr r_wr_en r_d_in r_d_out))
    | _, _, _=> error (Errors.msg "More than 2^32 states.")
    end
  else error (Errors.msg "Stack size misalignment.").

Definition max_state (f: function) : state :=
  let st := Pos.succ (max_reg_function f) in
  mkstate st
          (Pos.succ st)
          (Pos.succ (max_pc_function f))
          (AssocMap.set st (None, VScalar 32) (st_scldecls (init_state st)))
          (st_arrdecls (init_state st))
          (st_datapath (init_state st))
          (st_controllogic (init_state st)).

Definition transl_module (f : function) : Errors.res HTL.module :=
  run_mon (max_state f) (transf_module f).

Definition transl_fundef := transf_partial_fundef transl_module.

Definition main_is_internal (p : GiblePar.program) : bool :=
  let ge := Globalenvs.Genv.globalenv p in
  match Globalenvs.Genv.find_symbol ge p.(AST.prog_main) with
  | Some b =>
    match Globalenvs.Genv.find_funct_ptr ge b with
    | Some (AST.Internal _) => true
    | _ => false
    end
  | _ => false
  end.

Definition transl_program (p : GiblePar.program) : Errors.res HTL.program :=
  if main_is_internal p
  then transform_partial_program transl_fundef p
  else Errors.Error (Errors.msg "Main function is not Internal.").
