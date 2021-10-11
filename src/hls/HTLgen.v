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

Require Import compcert.lib.Maps.
Require compcert.common.Errors.
Require Import compcert.lib.Integers.
Require compcert.common.Globalenvs.
Require compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.backend.RTL.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.common.Maps.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.HTL.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.

Hint Resolve AssocMap.gempty : htlh.
Hint Resolve AssocMap.gso : htlh.
Hint Resolve AssocMap.gss : htlh.
Hint Resolve Ple_refl : htlh.
Hint Resolve Ple_succ : htlh.

Record state: Type := mkstate {
  st_st : reg;
  st_freshreg: reg;
  st_freshstate: node;
  st_scldecls: AssocMap.t (option io * scl_decl);
  st_arrdecls: AssocMap.t (option io * arr_decl);
  st_externctrl : AssocMap.t (ident * controlsignal);
  st_datapath: datapath;
  st_controllogic: controllogic;
}.

Definition init_state (st : reg) : state :=
  mkstate st
          1%positive
          1%positive
          (AssocMap.empty (option io * scl_decl))
          (AssocMap.empty (option io * arr_decl))
          (AssocMap.empty (ident * controlsignal))
          (AssocMap.empty datapath_stmnt)
          (AssocMap.empty control_stmnt).

(** Describes a map that is created incrementally in the monad, i.e. only new
    values can be added, not changed or deleted. *)
Definition map_incr {S B} (map : S -> PTree.t B) (s1 s2 : S) :=
  forall n, s1.(map)!n = None \/
       s2.(map)!n = s1.(map)!n.
Hint Unfold map_incr : htlh.

Module HTLState <: State.

  Definition st := state.

  Inductive st_incr: state -> state -> Prop :=
  | state_incr_intro:
      forall (s1 s2: state),
    st_st s1 = st_st s2 ->
    Ple s1.(st_freshreg) s2.(st_freshreg) ->
    Ple s1.(st_freshstate) s2.(st_freshstate) ->
    map_incr st_datapath s1 s2 ->
    map_incr st_controllogic s1 s2 ->
    map_incr st_externctrl s1 s2 ->
    (forall n, (st_externctrl s1) ! n = None ->
          (exists x, (st_externctrl s2) ! n = Some x) ->
          (n >= st_freshreg s1)%positive) ->
    st_incr s1 s2.
  Hint Constructors st_incr : htlh.

  Definition st_prop := st_incr.
  Hint Unfold st_prop : htlh.

  Lemma st_refl : forall s, st_prop s s.
  Proof. split; try solve [ auto with htlh; crush ]. Qed.

  Lemma st_trans :
    forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
  Proof.
    intros * H0 H1. inv H0. inv H1.
    split; autounfold with htlh in *; intros; try solve [crush].
    - destruct H4 with n; destruct H10 with n; intuition crush.
    - destruct H5 with n; destruct H11 with n; intuition crush.
    - destruct H6 with n; destruct H12 with n; intuition crush.
    - destruct H6 with n; destruct H12 with n.
      + specialize (H13 n ltac:(auto) ltac:(auto)).
        crush.
      + apply H7; auto.
        rewrite <- H16.
        auto.
      + specialize (H13 n ltac:(auto) ltac:(auto)).
        unfold Ple in *.
        lia.
      + contradict H14.
        rewrite H16.
        rewrite H15.
        rewrite H1.
        intuition crush.
  Qed.

End HTLState.
Export HTLState.

Module HTLMonad := Statemonad(HTLState).
Export HTLMonad.

Module HTLMonadExtra := Monad.MonadExtra(HTLMonad).
Import HTLMonadExtra.
Export MonadNotation.

Definition bop (op : binop) (r1 r2 : reg) : expr :=
  Vbinop op (Vvar r1) (Vvar r2).

Definition boplit (op : binop) (r : reg) (l : Integers.int) : expr :=
  Vbinop op (Vvar r) (Vlit (intToValue l)).

Definition boplitz (op: binop) (r: reg) (l: Z) : expr :=
  Vbinop op (Vvar r) (Vlit (ZToValue l)).

Definition state_goto (st : reg) (n : node) : control_stmnt :=
  Vnonblock (Vvar st) (Vlit (posToValue n)).

Definition state_cond (st : reg) (c : expr) (n1 n2 : node) : control_stmnt :=
  Vnonblock (Vvar st) (Vternary c (posToExpr n1) (posToExpr n2)).

Definition state_wait (st wait_reg : reg) (n : node) : control_stmnt :=
  Vcond (boplitz Veq wait_reg 1) (Vnonblock (Vvar st) (posToExpr n)) Vskip.

Definition nonblock (dst : reg) (e : expr) := (Vnonblock (Vvar dst) e).

Definition block (dst : reg) (e : expr) := (Vblock (Vvar dst) e).

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

Definition check_unmapped_externctrl:
  forall (s: state) (n: reg), { s.(st_externctrl)!n = None } + { True }.
Proof.
  intros. case (s.(st_externctrl)!n); tauto.
Defined.

(** Used for discharging the st_incr proof in simple operations *)
Local Ltac st_tac :=
  constructor; autounfold with htlh in *; intros; simpl; auto with htlh;
  match goal with
  | [ H : (?map ?s) ! ?n = None, n' : positive |- _] => destruct (peq n n')
  end;
  subst; auto with htlh; intuition crush.

Definition declare_reg (i : option io) (r : reg) (sz : nat) : mon unit :=
  fun s => OK tt (mkstate
             (st_st s)
             (st_freshreg s)
             (st_freshstate s)
             (AssocMap.set r (i, VScalar sz) s.(st_scldecls))
             (st_arrdecls s)
             (st_externctrl s)
             (st_datapath s)
             (st_controllogic s)) ltac:(st_tac).

Definition create_reg (i : option io) (sz : nat) : mon reg :=
  fun s => let r := s.(st_freshreg) in
        OK r (mkstate
            (st_st s)
            (Pos.succ r)
            (st_freshstate s)
            (AssocMap.set s.(st_freshreg) (i, VScalar sz) s.(st_scldecls))
            (st_arrdecls s)
            (st_externctrl s)
            (st_datapath s)
            (st_controllogic s)) ltac:(st_tac).

Definition map_externctrl (othermod : ident) (ctrl : controlsignal) : mon reg.
  refine (
  fun s => match check_unmapped_externctrl s (st_freshreg s) with
        | left CTRL => OK (st_freshreg s) (mkstate
                          (st_st s)
                          (Pos.succ (st_freshreg s))
                          (st_freshstate s)
                          (st_scldecls s)
                          (st_arrdecls s)
                          (AssocMap.set (st_freshreg s) (othermod, ctrl) (st_externctrl s))
                          (st_datapath s)
                          (st_controllogic s)) _
        | right CTRL => Error (Errors.msg "HTL.map_externctrl")
        end).
  st_tac.
  rewrite PTree.gsspec in *.
  destruct_match; crush.
Defined.

Definition create_state : mon node.
  refine (fun s => let r := s.(st_freshstate) in
                if Z.leb (Z.pos s.(st_freshstate)) Integers.Int.max_unsigned
                then OK r (mkstate
                         (st_st s)
                         (st_freshreg s)
                         (Pos.succ (st_freshstate s))
                         (st_scldecls s)
                         (st_arrdecls s)
                         (st_externctrl s)
                         (st_datapath s)
                         (st_controllogic s)) _
                else Error (Errors.msg "HTL.create_state")).
  split; autounfold with htlh; crush.
Defined.

Lemma create_state_max : forall s s' i x, create_state s = OK x s' i -> Z.pos x <= Int.max_unsigned.
Admitted.

Definition add_instr (n : node) (n' : node) (st : datapath_stmnt) : mon unit :=
  fun s => match check_empty_node_datapath s n, check_empty_node_controllogic s n with
        | left STM, left TRANS =>
          OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (st_externctrl s)
               (AssocMap.set n st s.(st_datapath))
               (AssocMap.set n (state_goto s.(st_st) n') s.(st_controllogic))) ltac:(st_tac)
        | _, _ => Error (Errors.msg "HTL.add_instr")
        end.

Definition add_instr_wait (wait_reg : reg) (n : node) (n' : node) (st : datapath_stmnt) : mon unit :=
  fun s => match check_empty_node_datapath s n, check_empty_node_controllogic s n with
        | left STM, left TRANS =>
          OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (st_externctrl s)
               (AssocMap.set n st s.(st_datapath))
               (AssocMap.set n (state_wait (st_st s) wait_reg n') s.(st_controllogic))) ltac:(st_tac)
        | _, _ => Error (Errors.msg "HTL.add_instr_wait")
        end.

Definition add_instr_skip (n : node) (st : datapath_stmnt) : mon unit :=
  fun s => match check_empty_node_datapath s n, check_empty_node_controllogic s n with
        | left STM, left TRANS =>
          OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (st_externctrl s)
               (AssocMap.set n st s.(st_datapath))
               (AssocMap.set n Vskip s.(st_controllogic))) ltac:(st_tac)
        | _, _ => Error (Errors.msg "HTL.add_instr")
        end.

Definition add_node_skip (n : node) (st : control_stmnt) : mon unit :=
  fun s => match check_empty_node_datapath s n, check_empty_node_controllogic s n with
        | left STM, left TRANS =>
          OK tt (mkstate
               s.(st_st)
               s.(st_freshreg)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (st_externctrl s)
               (AssocMap.set n Vskip s.(st_datapath))
               (AssocMap.set n st s.(st_controllogic))) ltac:(st_tac)
        | _, _ => Error (Errors.msg "HTL.add_instr")
        end.

Definition translate_comparison (c : Integers.comparison) (args : list reg) : mon expr :=
  match c, args with
  | Integers.Ceq, r1::r2::nil => ret (bop Veq r1 r2)
  | Integers.Cne, r1::r2::nil => ret (bop Vne r1 r2)
  | Integers.Clt, r1::r2::nil => ret (bop Vlt r1 r2)
  | Integers.Cgt, r1::r2::nil => ret (bop Vgt r1 r2)
  | Integers.Cle, r1::r2::nil => ret (bop Vle r1 r2)
  | Integers.Cge, r1::r2::nil => ret (bop Vge r1 r2)
  | _, _ => error (Errors.msg "Htlgen: comparison instruction not implemented: other")
  end.

Definition translate_comparison_imm (c : Integers.comparison) (args : list reg) (i: Integers.int)
  : mon expr :=
  match c, args with
  | Integers.Ceq, r1::nil => ret (boplit Veq r1 i)
  | Integers.Cne, r1::nil => ret (boplit Vne r1 i)
  | Integers.Clt, r1::nil => ret (boplit Vlt r1 i)
  | Integers.Cgt, r1::nil => ret (boplit Vgt r1 i)
  | Integers.Cle, r1::nil => ret (boplit Vle r1 i)
  | Integers.Cge, r1::nil => ret (boplit Vge r1 i)
  | _, _ => error (Errors.msg "Htlgen: comparison_imm instruction not implemented: other")
  end.

Definition translate_comparisonu (c : Integers.comparison) (args : list reg) : mon expr :=
  match c, args with
  | Integers.Clt, r1::r2::nil => ret (bop Vltu r1 r2)
  | Integers.Cgt, r1::r2::nil => ret (bop Vgtu r1 r2)
  | Integers.Cle, r1::r2::nil => ret (bop Vleu r1 r2)
  | Integers.Cge, r1::r2::nil => ret (bop Vgeu r1 r2)
  | _, _ => error (Errors.msg "Htlgen: comparison instruction not implemented: other")
  end.

Definition translate_comparison_immu (c : Integers.comparison) (args : list reg) (i: Integers.int)
  : mon expr :=
  match c, args with
  | Integers.Clt, r1::nil => ret (boplit Vltu r1 i)
  | Integers.Cgt, r1::nil => ret (boplit Vgtu r1 i)
  | Integers.Cle, r1::nil => ret (boplit Vleu r1 i)
  | Integers.Cge, r1::nil => ret (boplit Vgeu r1 i)
  | _, _ => error (Errors.msg "Htlgen: comparison_imm instruction not implemented: other")
  end.

Definition translate_condition (c : Op.condition) (args : list reg) : mon expr :=
  match c, args with
  | Op.Ccomp c, _ => translate_comparison c args
  | Op.Ccompu c, _ => translate_comparisonu c args
  | Op.Ccompimm c i, _ => translate_comparison_imm c args i
  | Op.Ccompuimm c i, _ => translate_comparison_immu c args i
  | Op.Cmaskzero n, _ => error (Errors.msg "Htlgen: condition instruction not implemented: Cmaskzero")
  | Op.Cmasknotzero n, _ => error (Errors.msg "Htlgen: condition instruction not implemented: Cmasknotzero")
  | _, _ => error (Errors.msg "Htlgen: condition instruction not implemented: other")
  end.

Definition check_address_parameter_signed (p : Z) : bool :=
  Z.leb Integers.Ptrofs.min_signed p
  && Z.leb p Integers.Ptrofs.max_signed.

Definition check_address_parameter_unsigned (p : Z) : bool :=
  Z.leb p Integers.Ptrofs.max_unsigned.

Definition translate_eff_addressing (a: Op.addressing) (args: list reg) : mon expr :=
  match a, args with (* TODO: We should be more methodical here; what are the possibilities?*)
  | Op.Aindexed off, r1::nil =>
    if (check_address_parameter_signed off)
    then ret (boplitz Vadd r1 off)
    else error (Errors.msg "Veriloggen: translate_eff_addressing (Aindexed): address out of bounds")
  | Op.Ascaled scale offset, r1::nil =>
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then ret (Vbinop Vadd (boplitz Vmul r1 scale) (Vlit (ZToValue offset)))
    else error (Errors.msg "Veriloggen: translate_eff_addressing (Ascaled): address out of bounds")
  | Op.Aindexed2 offset, r1::r2::nil =>
    if (check_address_parameter_signed offset)
    then ret (Vbinop Vadd (bop Vadd r1 r2) (Vlit (ZToValue offset)))
    else error (Errors.msg "Veriloggen: translate_eff_addressing (Aindexed2): address out of bounds")
  | Op.Aindexed2scaled scale offset, r1::r2::nil => (* Typical for dynamic array addressing *)
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then ret (Vbinop Vadd (Vvar r1) (Vbinop Vadd (boplitz Vmul r2 scale) (Vlit (ZToValue offset))))
    else error (Errors.msg "Veriloggen: translate_eff_addressing (Aindexed2scaled): address out of bounds")
  | Op.Ainstack a, nil => (* We need to be sure that the base address is aligned *)
    let a := Integers.Ptrofs.unsigned a in
    if (check_address_parameter_unsigned a)
    then ret (Vlit (ZToValue a))
    else error (Errors.msg "Veriloggen: translate_eff_addressing (Ainstack): address out of bounds")
  | _, _ => error (Errors.msg "Veriloggen: translate_eff_addressing unsuported addressing")
  end.

(** Translate an instruction to a statement. FIX mulhs mulhu *)
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
  | Op.Oshrximm n, r::nil => ret (Vternary (Vbinop Vlt (Vvar r) (Vlit (ZToValue 0)))
                                         (Vunop Vneg (Vbinop Vshru (Vunop Vneg (Vvar r)) (Vlit n)))
                                         (Vbinop Vshru (Vvar r) (Vlit n)))
  (*ret (Vbinop Vdiv (Vvar r)
    (Vbinop Vshl (Vlit (ZToValue 1))
    (Vlit (intToValue n))))*)
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
  | _, _ => error (Errors.msg "Htlgen: Instruction not implemented: other")
  end.

Definition add_branch_instr (e: expr) (n n1 n2: node) : mon unit :=
  fun s => match check_empty_node_datapath s n, check_empty_node_controllogic s n with
        | left NSTM, left NTRANS =>
          OK tt (mkstate
               s.(st_st)
               (st_freshreg s)
               (st_freshstate s)
               s.(st_scldecls)
               s.(st_arrdecls)
               (st_externctrl s)
               (AssocMap.set n Vskip (st_datapath s))
               (AssocMap.set n (state_cond s.(st_st) e n1 n2) (st_controllogic s))) ltac:(st_tac)
        | _, _ => Error (Errors.msg "Htlgen: add_branch_instr")
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

Fixpoint enumerate (i : nat) (ns : list node) {struct ns} : list (nat * node) :=
  match ns with
  | n :: ns' => (i, n) :: enumerate (i+1) ns'
  | nil => nil
  end.

Definition tbl_to_case_expr (st : reg) (ns : list node) : list (expr * stmnt) :=
  List.map (fun a => match a with
                    (i, n) => (Vlit (natToValue i), Vnonblock (Vvar st) (Vlit (posToValue n)))
                  end)
           (enumerate 0 ns).

Fixpoint nonblock_all pairs :=
  match pairs with
  | (dst, src) :: pairs' => Vseq (nonblock dst (Vvar src)) (nonblock_all pairs')
  | nil => Vskip
  end.

(** [fork] a datapath statement which sets up the execution of a function *)
Definition fork (rst : reg) (params : list (reg * reg)) : datapath_stmnt :=
  let reset_mod := Vnonblock (Vvar rst) (posToLit 1) in
  let assign_params := nonblock_all params in
  Vseq reset_mod assign_params.

Definition join (fn_fin fn_rst fn_rtrn fn_dst : reg) : datapath_stmnt :=
  let set_result := Vcond (boplitz Veq fn_fin 1)
                          (Vnonblock (Vvar fn_dst) (Vvar fn_rtrn)) Vskip in
  let stop_reset := Vnonblock (Vvar fn_rst) (Vlit (ZToValue 0)) in
  Vseq stop_reset set_result.

Definition return_val r :=
  match r with
  | Some r' => Vvar r'
  | None => Vlit (ZToValue 0%Z)
  end.

Definition do_return fin rtrn r :=
  Vseq (block fin (Vlit (ZToValue 1%Z)))
       (block rtrn (return_val r)).

Definition idle fin := nonblock fin (Vlit (ZToValue 0%Z)).

Fixpoint xmap_externctrl_params (n : nat) (fn : ident) (l : list reg) :=
  match l with
  | nil => ret nil
  | arg::args =>
    do param_reg <- map_externctrl fn (ctrl_param n);
    do rest <- xmap_externctrl_params (S n) fn args;
    ret ((param_reg, arg) :: rest)
  end.

Definition map_externctrl_params := xmap_externctrl_params 0.

Definition transf_instr (ge : RTL.genv) (fin rtrn stack: reg) (ni: node * instruction) : mon unit :=
  match ni with
    (n, i) =>
    match i with
    | Inop n' =>
      if Z.leb (Z.pos n') Integers.Int.max_unsigned then
        add_instr n n' Vskip
      else error (Errors.msg "State is larger than 2^32.")
    | Iop op args dst n' =>
      if Z.leb (Z.pos n') Integers.Int.max_unsigned then
        do instr <- translate_instr op args;
        do _ <- declare_reg None dst 32;
        add_instr n n' (nonblock dst instr)
      else error (Errors.msg "State is larger than 2^32.")
    | Iload mem addr args dst n' =>
      if Z.leb (Z.pos n') Integers.Int.max_unsigned then
        do src <- translate_arr_access mem addr args stack;
        do _ <- declare_reg None dst 32;
        add_instr n n' (nonblock dst src)
      else error (Errors.msg "State is larger than 2^32.")
    | Istore mem addr args src n' =>
      if Z.leb (Z.pos n') Integers.Int.max_unsigned then
        do dst <- translate_arr_access mem addr args stack;
        add_instr n n' (Vnonblock dst (Vvar src)) (* TODO: Could juse use add_instr? reg exists. *)
      else error (Errors.msg "State is larger than 2^32.")
    | Icall sig (inl fn) args dst n' => error (Errors.msg "Indirect calls are not implemented.")
    | Icall sig (inr fn) args dst n' =>
      if Z.leb (Z.pos n') Integers.Int.max_unsigned
      then match find_func ge fn with
           | Some (AST.Internal _) =>
             do params <- map_externctrl_params fn args;

             do _ <- declare_reg None dst 32;
             do join_state <- create_state;

             do finish_reg <- map_externctrl fn ctrl_finish;
             do reset_reg <- map_externctrl fn ctrl_reset;
             do return_reg <- map_externctrl fn ctrl_return;

             let fork_instr := fork reset_reg params in
             let join_instr := join finish_reg reset_reg return_reg dst in

             do _ <- add_instr n join_state fork_instr;
             add_instr_wait finish_reg join_state n' join_instr
           | _ => error (Errors.msg "Call to non-internal function")
           end
      else error (Errors.msg "State is larger than 2^32.")
    | Itailcall _ _ _ => error (Errors.msg "Tailcalls are not implemented.")
    | Ibuiltin _ _ _ _ => error (Errors.msg "Builtin functions not implemented.")
    | Icond cond args n1 n2 =>
      if Z.leb (Z.pos n1) Integers.Int.max_unsigned && Z.leb (Z.pos n2) Integers.Int.max_unsigned then
        do e <- translate_condition cond args;
        add_branch_instr e n n1 n2
      else error (Errors.msg "State is larger than 2^32.")
    | Ijumptable r tbl =>
      (*do s <- get;
      add_node_skip n (Vcase (Vvar r) (tbl_to_case_expr s.(st_st) tbl) (Some Vskip))*)
      error (Errors.msg "Ijumptable: Case statement not supported.")
    | Ireturn r =>
      do idle_state <- create_state;
      do _ <- add_instr n idle_state (do_return fin rtrn r);
      add_instr_skip idle_state (idle fin)
    end
  end.

Definition create_arr (i : option io) (sz : nat) (ln : nat) : mon (reg * nat) :=
  fun s => let r := s.(st_freshreg) in
        OK (r, ln) (mkstate
                  s.(st_st)
                  (Pos.succ r)
                  (st_freshstate s)
                  s.(st_scldecls)
                  (AssocMap.set s.(st_freshreg) (i, VArray sz ln) s.(st_arrdecls))
                  (st_externctrl s)
                  (st_datapath s)
                  (st_controllogic s)) ltac:(st_tac).

Definition stack_correct (sz : Z) : bool :=
  (0 <=? sz) && (sz <? Integers.Ptrofs.modulus) && (Z.modulo sz 4 =? 0).

Definition declare_params params := collectlist (fun r => declare_reg (Some Vinput) r 32) params.

Lemma max_pc_map_sound {A} :
  forall (m : PTree.t A) pc i, m!pc = Some i -> Ple pc (max_pc_map m).
Proof.
  intros until i. unfold max_pc_function.
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto.
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
  inv H2. unfold Ple; lia.
  apply Ple_trans with a. auto. unfold Ple; lia.
Qed.

Lemma max_pc_wf {A} :
  forall (m : PTree.t A), Z.pos (max_pc_map m) <= Integers.Int.max_unsigned ->
                     map_well_formed m.
Proof.
  unfold map_well_formed. intros.
  exploit list_in_map_inv. eassumption. intros [x [H1 H2]]. destruct x.
  apply Maps.PTree.elements_complete in H2. apply max_pc_map_sound in H2.
  unfold Ple in H2. apply Pos2Z.pos_le_pos in H2. subst.
  simplify. transitivity (Z.pos (max_pc_map m)); eauto.
Qed.

Definition transf_module (ge : RTL.genv) (main : ident) (f: function) : mon HTL.module.
  refine (
  if stack_correct f.(fn_stacksize) then
    do _ <- declare_params (RTL.fn_params f);
    do fin <- create_reg (Some Voutput) 1;
    do rtrn <- create_reg (Some Voutput) 32;
    do (stack, stack_len) <- create_arr None 32 (Z.to_nat (f.(fn_stacksize) / 4));
    do start <- create_reg (Some Vinput) 1;
    do rst <- create_reg (Some Vinput) 1;
    do clk <- create_reg (Some Vinput) 1;
    do _ <- collectlist (transf_instr ge fin rtrn stack) (Maps.PTree.elements f.(RTL.fn_code));
    do current_state <- get;
    match zle (Z.pos (max_pc_map current_state.(st_datapath))) Integers.Int.max_unsigned,
          zle (Z.pos (max_pc_map current_state.(st_controllogic))) Integers.Int.max_unsigned,
          decide_order (st_st current_state) fin rtrn stack start rst clk,
          max_list_dec (RTL.fn_params f) (st_st current_state)
    with
    | left LEDATA, left LECTRL, left MORD, left WFPARAMS =>
        ret (HTL.mkmodule
           f.(RTL.fn_params)
           current_state.(st_datapath)
           current_state.(st_controllogic)
           f.(fn_entrypoint)
           current_state.(st_st)
           stack
           stack_len
           fin
           rtrn
           start
           rst
           clk
           current_state.(st_scldecls)
           current_state.(st_arrdecls)
           current_state.(st_externctrl)
           None
           (conj (max_pc_wf _ LECTRL) (max_pc_wf _ LEDATA))
           MORD
           _
           WFPARAMS)
    | _, _, _, _ => error (Errors.msg "More than 2^32 states.")
    end
  else error (Errors.msg "Stack size misalignment.")); discriminate.
Defined.

Definition max_state (f: function) : state :=
  let st := Pos.succ (max_reg_function f) in
  mkstate st
          (Pos.succ st)
          (Pos.succ (RTL.max_pc_function f))
          (AssocMap.set st (None, VScalar 32) (st_scldecls (init_state st)))
          (st_arrdecls (init_state st))
          (st_externctrl (init_state st))
          (st_datapath (init_state st))
          (st_controllogic (init_state st)).

Definition prog_funmap (prog : RTL.program) : (PTree.t RTL.fundef) :=
  AssocMap_Properties.of_list (
    Option.map_option (fun '(ident, def) => match def with
                                         | AST.Gfun f => Some (ident, f)
                                         | _ => None
                                         end)
                      (AST.prog_defs prog)
  ).

Definition transl_module (prog : RTL.program) (f : function) : Errors.res HTL.module :=
  run_mon (max_state f) (transf_module (Globalenvs.Genv.globalenv prog) (AST.prog_main prog) f).

Definition transl_fundef prog := transf_partial_fundef (transl_module prog).

Definition main_is_internal (p : RTL.program) : bool :=
  let ge := Globalenvs.Genv.globalenv p in
  match Globalenvs.Genv.find_symbol ge p.(AST.prog_main) with
  | Some b =>
    match Globalenvs.Genv.find_funct_ptr ge b with
    | Some (AST.Internal _) => true
    | _ => false
    end
  | _ => false
  end.

Definition only_main_has_stack (p : RTL.program) : Prop :=
  Forall (fun '(name, def) =>
            match def with
            | AST.Gfun (Internal f) => name <> (AST.prog_main p) -> RTL.fn_stacksize f = 0
            | _ => True
            end)
         (PTree.elements (Globalenvs.Genv.genv_defs (Globalenvs.Genv.globalenv p))).

Definition only_main_has_stack_dec (p : RTL.program) : {only_main_has_stack p} + {~ only_main_has_stack p}.
Proof.
  refine (Forall_dec _
                     (fun '(name, def) => match def with
                                       | AST.Gfun (Internal f) =>
                                         if (Pos.eq_dec (prog_main p) name)
                                         then left _
                                         else if (Z.eq_dec (fn_stacksize f) 0)
                                              then left _
                                              else right _
                                       | _ => left _
                                       end)
                     _).
  all: crush.
Qed.

Definition transl_program (p : RTL.program) : Errors.res HTL.program :=
  if main_is_internal p && only_main_has_stack_dec p
  then transform_partial_program (transl_fundef p) p
  else Errors.Error (Errors.msg "Main function is not Internal.").
