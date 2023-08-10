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
Require compcert.common.Globalenvs.
Require compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.DHTL.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Predicate.

#[local] Hint Resolve AssocMap.gempty : htlh.
#[local] Hint Resolve AssocMap.gso : htlh.
#[local] Hint Resolve AssocMap.gss : htlh.
#[local] Hint Resolve Ple_refl : htlh.
#[local] Hint Resolve Ple_succ : htlh.

Record state: Type := mkstate {
  st_st : reg;
  st_freshreg: reg;
  st_freshstate: node;
  st_scldecls: AssocMap.t (option io * scl_decl);
  st_arrdecls: AssocMap.t (option io * arr_decl);
  st_datapath: datapath;
}.

Definition init_state (st : reg) : state :=
  mkstate st
          1%positive
          1%positive
          (AssocMap.empty (option io * scl_decl))
          (AssocMap.empty (option io * arr_decl))
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
            s1.(st_datapath)!n = None \/ s2.(st_datapath)!n = s1.(st_datapath)!n) ->
        st_incr s1 s2.
  #[export] Hint Constructors st_incr : htlh.

  Definition st_prop := st_incr.
  #[export] Hint Unfold st_prop : htlh.

  Lemma st_refl : forall s, st_prop s s. Proof. auto with htlh. Qed.

  Lemma st_trans :
    forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
  Proof.
    intros. inv H. inv H0. apply state_incr_intro; eauto using Ple_trans; intros; try congruence.
    - destruct H4 with n; destruct H7 with n; intuition congruence.
  Qed.

End HTLState.
Export HTLState.

Module HTLMonad := Statemonad(HTLState).
Export HTLMonad.

Module HTLMonadExtra := Monad.MonadExtra(HTLMonad).
Import HTLMonadExtra.
Export MonadNotation.

#[local] Open Scope monad_scope.

Definition pred_lit (preg: reg) (pred: predicate) :=
  Vrange preg (Vlit (posToValue pred)) (Vlit (posToValue pred)).

Fixpoint pred_expr (preg: reg) (p: pred_op) :=
  match p with
  | Plit (b, pred) =>
    if b
    then pred_lit preg pred
    else Vunop Vnot (pred_lit preg pred)
  | Ptrue => Vlit (ZToValue 1)
  | Pfalse => Vlit (ZToValue 0)
  | Pand p1 p2 =>
    Vbinop Vand (pred_expr preg p1) (pred_expr preg p2)
  | Por p1 p2 =>
    Vbinop Vor (pred_expr preg p1) (pred_expr preg p2)
  end.

Definition assignment : Type := expr -> expr -> stmnt.

Definition translate_predicate (a : assignment)
           (preg: reg) (p: option pred_op) (dst e: expr) :=
  match p with
  | None => a dst e
  | Some pos =>
    let pos' := deep_simplify peq pos in
    match sat_pred_simple (negate pos') with
    | None => a dst e
    | Some _ => a dst (Vternary (pred_expr preg pos') e dst)
    end
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

Definition append_instr (n : node) (st : stmnt) (d : datapath) : datapath :=
  match AssocMap.get n d with 
  | Some st' => AssocMap.set n (Vseq st' st) d
  | None => AssocMap.set n st d
  end.

Lemma declare_reg_state_incr :
  forall i s r sz,
    st_incr s
    (mkstate
       s.(st_st)
       s.(st_freshreg)
       s.(st_freshstate)
       (AssocMap.set r (i, VScalar sz) s.(st_scldecls))
       s.(st_arrdecls)
       s.(st_datapath)).
Proof. Admitted.

Definition declare_reg (i : option io) (r : reg) (sz : nat) : mon unit :=
  fun s => OK tt (mkstate
                s.(st_st)
                s.(st_freshreg)
                s.(st_freshstate)
                (AssocMap.set r (i, VScalar sz) s.(st_scldecls))
                s.(st_arrdecls)
                s.(st_datapath))
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
       s.(st_datapath)).
Proof. Admitted.

Definition declare_arr (i : option io) (r : reg) (sz : nat) (ln : nat) : mon unit :=
  fun s => OK tt (mkstate
                s.(st_st)
                s.(st_freshreg)
                s.(st_freshstate)
                s.(st_scldecls)
                (AssocMap.set r (i, VArray sz ln) s.(st_arrdecls))
                s.(st_datapath))
              (declare_arr_state_incr i s r sz ln).

Definition nonblock (dst : reg) (e : expr) := Vnonblock (Vvar dst) e.
Definition block (dst : reg) (e : expr) := Vblock (Vvar dst) e.

Definition bop (op : binop) (r1 r2 : reg) : expr :=
  Vbinop op (Vvar r1) (Vvar r2).

Definition boplit (op : binop) (r : reg) (l : Integers.int) : expr :=
  Vbinop op (Vvar r) (Vlit (intToValue l)).

Definition boplitz (op: binop) (r: reg) (l: Z) : expr :=
  Vbinop op (Vvar r) (Vlit (ZToValue l)).

Definition translate_comparison (c : Integers.comparison) (args : list reg) : Errors.res expr :=
  match c, args with
  | Integers.Ceq, r1::r2::nil => Errors.OK (bop Veq r1 r2)
  | Integers.Cne, r1::r2::nil => Errors.OK (bop Vne r1 r2)
  | Integers.Clt, r1::r2::nil => Errors.OK (bop Vlt r1 r2)
  | Integers.Cgt, r1::r2::nil => Errors.OK (bop Vgt r1 r2)
  | Integers.Cle, r1::r2::nil => Errors.OK (bop Vle r1 r2)
  | Integers.Cge, r1::r2::nil => Errors.OK (bop Vge r1 r2)
  | _, _ => Errors.Error (Errors.msg "Htlgen: comparison instruction not implemented: other")
  end.

Definition translate_comparison_imm (c : Integers.comparison) (args : list reg) (i: Integers.int)
  : Errors.res expr :=
  match c, args with
  | Integers.Ceq, r1::nil => Errors.OK (boplit Veq r1 i)
  | Integers.Cne, r1::nil => Errors.OK (boplit Vne r1 i)
  | Integers.Clt, r1::nil => Errors.OK (boplit Vlt r1 i)
  | Integers.Cgt, r1::nil => Errors.OK (boplit Vgt r1 i)
  | Integers.Cle, r1::nil => Errors.OK (boplit Vle r1 i)
  | Integers.Cge, r1::nil => Errors.OK (boplit Vge r1 i)
  | _, _ => Errors.Error (Errors.msg "Htlgen: comparison_imm instruction not implemented: other")
  end.

Definition translate_comparisonu (c : Integers.comparison) (args : list reg) : Errors.res expr :=
  match c, args with
  | Integers.Clt, r1::r2::nil => Errors.OK (bop Vltu r1 r2)
  | Integers.Cgt, r1::r2::nil => Errors.OK (bop Vgtu r1 r2)
  | Integers.Cle, r1::r2::nil => Errors.OK (bop Vleu r1 r2)
  | Integers.Cge, r1::r2::nil => Errors.OK (bop Vgeu r1 r2)
  | _, _ => Errors.Error (Errors.msg "Htlgen: comparison instruction not implemented: other")
  end.

Definition translate_comparison_immu (c : Integers.comparison) (args : list reg) (i: Integers.int)
  : Errors.res expr :=
  match c, args with
  | Integers.Clt, r1::nil => Errors.OK (boplit Vltu r1 i)
  | Integers.Cgt, r1::nil => Errors.OK (boplit Vgtu r1 i)
  | Integers.Cle, r1::nil => Errors.OK (boplit Vleu r1 i)
  | Integers.Cge, r1::nil => Errors.OK (boplit Vgeu r1 i)
  | _, _ => Errors.Error (Errors.msg "Htlgen: comparison_imm instruction not implemented: other")
  end.

Definition translate_condition (c : Op.condition) (args : list reg) : Errors.res expr :=
  match c, args with
  | Op.Ccomp c, _ => translate_comparison c args
  | Op.Ccompu c, _ => translate_comparisonu c args
  | Op.Ccompimm c i, _ => translate_comparison_imm c args i
  | Op.Ccompuimm c i, _ => translate_comparison_immu c args i
  | Op.Cmaskzero n, _ => Errors.Error (Errors.msg "Htlgen: condition instruction not implemented: Cmaskzero")
  | Op.Cmasknotzero n, _ => Errors.Error (Errors.msg "Htlgen: condition instruction not implemented: Cmasknotzero")
  | _, _ => Errors.Error (Errors.msg "Htlgen: condition instruction not implemented: other")
  end.

Definition check_address_parameter_signed (p : Z) : bool :=
  Z.leb Integers.Ptrofs.min_signed p
  && Z.leb p Integers.Ptrofs.max_signed.

Definition check_address_parameter_unsigned (p : Z) : bool :=
  Z.leb p Integers.Ptrofs.max_unsigned.

Definition translate_eff_addressing (a: Op.addressing) (args: list reg) : Errors.res expr :=
  match a, args with (* TODO: We should be more methodical here; what are the possibilities?*)
  | Op.Aindexed off, r1::nil =>
    if (check_address_parameter_signed off)
    then Errors.OK (boplitz Vadd r1 off)
    else Errors.Error (Errors.msg "Veriloggen: translate_eff_addressing (Aindexed): address out of bounds")
  | Op.Ascaled scale offset, r1::nil =>
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then Errors.OK (Vbinop Vadd (boplitz Vmul r1 scale) (Vlit (ZToValue offset)))
    else Errors.Error (Errors.msg "Veriloggen: translate_eff_addressing (Ascaled): address out of bounds")
  | Op.Aindexed2 offset, r1::r2::nil =>
    if (check_address_parameter_signed offset)
    then Errors.OK (Vbinop Vadd (bop Vadd r1 r2) (Vlit (ZToValue offset)))
    else Errors.Error (Errors.msg "Veriloggen: translate_eff_addressing (Aindexed2): address out of bounds")
  | Op.Aindexed2scaled scale offset, r1::r2::nil => (* Typical for dynamic array addressing *)
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then Errors.OK (Vbinop Vadd (Vvar r1) (Vbinop Vadd (boplitz Vmul r2 scale) (Vlit (ZToValue offset))))
    else Errors.Error (Errors.msg "Veriloggen: translate_eff_addressing (Aindexed2scaled): address out of bounds")
  | Op.Ainstack a, nil => (* We need to be sure that the base address is aligned *)
    let a := Integers.Ptrofs.unsigned a in
    if (check_address_parameter_unsigned a)
    then Errors.OK (Vlit (ZToValue a))
    else Errors.Error (Errors.msg "Veriloggen: translate_eff_addressing (Ainstack): address out of bounds")
  | _, _ => Errors.Error (Errors.msg "Veriloggen: translate_eff_addressing unsuported addressing")
  end.

#[local] Close Scope monad_scope.
#[local] Open Scope error_monad_scope.

(** Translate an instruction to a statement. FIX mulhs mulhu *)
Definition translate_instr (op : Op.operation) (args : list reg) : Errors.res expr :=
  match op, args with
  | Op.Omove, r::nil => Errors.OK (Vvar r)
  | Op.Ointconst n, _ => Errors.OK (Vlit (intToValue n))
  | Op.Oneg, r::nil => Errors.OK (Vunop Vneg (Vvar r))
  | Op.Osub, r1::r2::nil => Errors.OK (bop Vsub r1 r2)
  | Op.Omul, r1::r2::nil => Errors.OK (bop Vmul r1 r2)
  | Op.Omulimm n, r::nil => Errors.OK (boplit Vmul r n)
  | Op.Omulhs, r1::r2::nil => Errors.Error (Errors.msg "Htlgen: Instruction not implemented: mulhs")
  | Op.Omulhu, r1::r2::nil => Errors.Error (Errors.msg "Htlgen: Instruction not implemented: mulhu")
  | Op.Odiv, r1::r2::nil => Errors.OK (bop Vdiv r1 r2)
  | Op.Odivu, r1::r2::nil => Errors.OK (bop Vdivu r1 r2)
  | Op.Omod, r1::r2::nil => Errors.OK (bop Vmod r1 r2)
  | Op.Omodu, r1::r2::nil => Errors.OK (bop Vmodu r1 r2)
  | Op.Oand, r1::r2::nil => Errors.OK (bop Vand r1 r2)
  | Op.Oandimm n, r::nil => Errors.OK (boplit Vand r n)
  | Op.Oor, r1::r2::nil => Errors.OK (bop Vor r1 r2)
  | Op.Oorimm n, r::nil => Errors.OK (boplit Vor r n)
  | Op.Oxor, r1::r2::nil => Errors.OK (bop Vxor r1 r2)
  | Op.Oxorimm n, r::nil => Errors.OK (boplit Vxor r n)
  | Op.Onot, r::nil => Errors.OK (Vunop Vnot (Vvar r))
  | Op.Oshl, r1::r2::nil => Errors.OK (bop Vshl r1 r2)
  | Op.Oshlimm n, r::nil => Errors.OK (boplit Vshl r n)
  | Op.Oshr, r1::r2::nil => Errors.OK (bop Vshr r1 r2)
  | Op.Oshrimm n, r::nil => Errors.OK (boplit Vshr r n)
  | Op.Oshrximm n, r::nil =>
    Errors.OK (Vternary (Vbinop Vlt (Vvar r) (Vlit (ZToValue 0)))
                  (Vunop Vneg (Vbinop Vshru (Vunop Vneg (Vvar r)) (Vlit n)))
                  (Vbinop Vshru (Vvar r) (Vlit n)))
  | Op.Oshru, r1::r2::nil => Errors.OK (bop Vshru r1 r2)
  | Op.Oshruimm n, r::nil => Errors.OK (boplit Vshru r n)
  | Op.Ororimm n, r::nil => Errors.Error (Errors.msg "Htlgen: Instruction not implemented: Ororimm")
  (*Errors.OK (Vbinop Vor (boplit Vshru r (Integers.Int.modu n (Integers.Int.repr 32)))
                                        (boplit Vshl r (Integers.Int.sub (Integers.Int.repr 32) (Integers.Int.modu n (Integers.Int.repr 32)))))*)
  | Op.Oshldimm n, r::nil => Errors.OK (Vbinop Vor (boplit Vshl r n) (boplit Vshr r (Integers.Int.sub (Integers.Int.repr 32) n)))
  | Op.Ocmp c, _ => translate_condition c args
  | Op.Osel c AST.Tint, r1::r2::rl =>
    do tc <- translate_condition c rl;
    Errors.OK (Vternary tc (Vvar r1) (Vvar r2))
  | Op.Olea a, _ => translate_eff_addressing a args
  | _, _ => Errors.Error (Errors.msg "Htlgen: Instruction not implemented: other")
  end.

Definition translate_arr_access (mem : AST.memory_chunk) (addr : Op.addressing)
           (args : list reg) (stack : reg) : Errors.res expr :=
  match mem, addr, args with (* TODO: We should be more methodical here; what are the possibilities?*)
  | Mint32, Op.Aindexed off, r1::nil =>
    if (check_address_parameter_signed off)
    then Errors.OK (Vvari stack (Vbinop Vdivu (boplitz Vadd r1 off) (Vlit (ZToValue 4))))
    else Errors.Error (Errors.msg "HTLPargen: translate_arr_access address out of bounds")
  | Mint32, Op.Aindexed2scaled scale offset, r1::r2::nil => (* Typical for dynamic array addressing *)
    if (check_address_parameter_signed scale) && (check_address_parameter_signed offset)
    then Errors.OK (Vvari stack
                    (Vbinop Vdivu
                            (Vbinop Vadd (boplitz Vadd r1 offset) (boplitz Vmul r2 scale))
                            (Vlit (ZToValue 4))))
    else Errors.Error (Errors.msg "HTLPargen: translate_arr_access address out of bounds")
  | Mint32, Op.Ainstack a, nil => (* We need to be sure that the base address is aligned *)
    let a := Integers.Ptrofs.unsigned a in
    if (check_address_parameter_unsigned a)
    then Errors.OK (Vvari stack (Vlit (ZToValue (a / 4))))
    else Errors.Error (Errors.msg "HTLPargen: eff_addressing out of bounds stack offset")
  | _, _, _ => Errors.Error (Errors.msg "HTLPargen: translate_arr_access unsuported addressing")
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

Definition translate_cfi (fin rtrn state preg: reg) p (cfi: cf_instr)
  : Errors.res stmnt :=
  match cfi with
  | RBgoto n' =>
    Errors.OK (state_goto preg p state n')
  | RBcond c args n1 n2 =>
    do e <- translate_condition c args;
    Errors.OK (state_cond preg p state e n1 n2)
  | RBreturn r =>
    match r with
    | Some r' =>
      Errors.OK (Vseq (block fin (Vlit (ZToValue 1%Z))) (block rtrn (Vvar r')))
    | None =>
      Errors.OK (Vseq (block fin (Vlit (ZToValue 1%Z))) (block rtrn (Vlit (ZToValue 0%Z))))
    end
  | RBjumptable r tbl =>
    Errors.OK (Vcase (Vvar r) (list_to_stmnt (tbl_to_case_expr state tbl)) (Some Vskip))
  | RBcall sig ri rl r n =>
    Errors.Error (Errors.msg "HTLPargen: RBcall not supported.")
  | RBtailcall sig ri lr =>
    Errors.Error (Errors.msg "HTLPargen: RBtailcall not supported.")
  | RBbuiltin e lb b n =>
    Errors.Error (Errors.msg "HTLPargen: RBbuildin not supported.")
  end.

Definition dfltp {A} (p: option (@Predicate.pred_op A)) := Option.default Ptrue p.

Definition transf_instr (fin rtrn stack state preg: reg) 
           (dc: pred_op * stmnt) (i: instr)
           : Errors.res (pred_op * stmnt) :=
  let '(curr_p, d) := dc in
  let npred p := Some (Pand curr_p (dfltp p)) in
  match i with
  | RBnop => Errors.OK dc
  | RBop p op args dst => 
    do instr <- translate_instr op args;
    let stmnt := translate_predicate Vblock preg (npred p) (Vvar dst) instr in
    Errors.OK (curr_p, Vseq d stmnt)
  | RBload p mem addr args dst =>
    do src <- translate_arr_access mem addr args stack;
    let stmnt := translate_predicate Vnonblock preg (npred p) (Vvar dst) src in
    Errors.OK (curr_p, Vseq d stmnt)
  | RBstore p mem addr args src =>
    do dst <- translate_arr_access mem addr args stack;
    let stmnt := translate_predicate Vnonblock preg (npred p) dst (Vvar src) in
    Errors.OK (curr_p, Vseq d stmnt)
  | RBsetpred p' cond args p =>
    do cond' <- translate_condition cond args;
    let stmnt := translate_predicate Vblock preg (npred p') (pred_expr preg (Plit (true, p))) cond' in
    Errors.OK (curr_p, Vseq d stmnt)
  | RBexit p cf => 
    do d_stmnt <- translate_cfi fin rtrn state preg (npred p) cf;
    Errors.OK (Pand curr_p (negate (dfltp p)), Vseq d d_stmnt)
  end.

Definition fold_leftE {A B} (f: A -> B -> Errors.res A) (l: list B) (el: A): Errors.res A :=
  fold_left (fun a b => do a' <- a; f a' b) l (Errors.OK el).

Definition transf_chained_block (fin rtrn stack state preg: reg)
           (dc: @pred_op positive * stmnt)
           (block: list instr)
           : Errors.res (pred_op * stmnt) :=
  fold_leftE (transf_instr fin rtrn stack state preg) block dc.

Definition transf_parallel_block (fin rtrn stack state preg: reg)
           (dc: @pred_op positive * stmnt)
           (block: list (list instr))
           : Errors.res (pred_op * stmnt) :=
  fold_leftE (transf_chained_block fin rtrn stack state preg) block dc.

Definition transf_parallel_full_block (fin rtrn stack state preg: reg)
           (dc: node * @pred_op positive * datapath)
           (block: list (list instr))
           : Errors.res (node * pred_op * datapath) :=
  let '(n, curr_p, dt) := dc in
  match AssocMap.get n dt with
  | None =>
    do ctrl_init_stmnt <-
          translate_cfi fin rtrn state preg (Some curr_p) (RBgoto (n - 1)%positive);
    do dc' <- transf_parallel_block fin rtrn stack state preg (curr_p, ctrl_init_stmnt) block;
    let '(curr_p', dt_stmnt) := dc' in
    Errors.OK ((n - 1)%positive, curr_p', AssocMap.set n dt_stmnt dt)
  | _ => Errors.Error (msg "HtlPargen.transf_parallel_full_block: block not empty")
  end.

Definition transf_seq_block (fin rtrn stack state preg: reg)
           (d: datapath) (n: node)
           (block: list (list (list instr)))
           : Errors.res datapath :=
  do res <- fold_leftE
    (transf_parallel_full_block fin rtrn stack state preg) block (n, Ptrue, d);
  let '(_, _, d') := res in
  Errors.OK d'.

#[local] Close Scope error_monad_scope.
#[local] Open Scope monad_scope.

Program Definition transf_seq_blockM (fin rtrn stack preg: reg) (ni: node * ParBB.t): mon unit :=
  fun st =>
    let (n, i) := ni in
    match transf_seq_block fin rtrn stack st.(st_st) preg st.(st_datapath) n i with
    | Errors.OK d => 
      OK tt (mkstate st.(st_st)
             st.(st_freshreg)
             st.(st_freshstate)
             st.(st_scldecls)
             st.(st_arrdecls)
             d) _
    | Errors.Error m => Error m
    end.
Next Obligation.
admit.
Admitted.

Definition declare_regs (i: instr): mon unit :=
  match i with
  | RBop _ _ _ d => declare_reg None d 32
  | RBload _ _ _ _ d => declare_reg None d 32
  | _ => ret tt
  end.

Definition declare_all_regs (ni: node * ParBB.t): mon unit :=
  let (n, i) := ni in
  ParBB.foldl _ (fun (st_f: mon unit) i => do _tt <- st_f; declare_regs i) i (ret tt).

Lemma create_reg_state_incr:
  forall s sz i,
    st_incr s (mkstate
         s.(st_st)
         (Pos.succ (st_freshreg s))
         (st_freshstate s)
         (AssocMap.set s.(st_freshreg) (i, VScalar sz) s.(st_scldecls))
         s.(st_arrdecls)
         (st_datapath s)).
Proof. constructor; simpl; auto with htlh. Qed.

Definition create_reg (i : option io) (sz : nat) : mon reg :=
  fun s => let r := s.(st_freshreg) in
           OK r (mkstate
                   s.(st_st)
                   (Pos.succ r)
                   (st_freshstate s)
                   (AssocMap.set s.(st_freshreg) (i, VScalar sz) s.(st_scldecls))
                   (st_arrdecls s)
                   (st_datapath s))
              (create_reg_state_incr s sz i).

Lemma create_arr_state_incr:
  forall s sz ln i,
    st_incr s (mkstate
         s.(st_st)
         (Pos.succ (st_freshreg s))
         (st_freshstate s)
         s.(st_scldecls)
         (AssocMap.set s.(st_freshreg) (i, VArray sz ln) s.(st_arrdecls))
         (st_datapath s)).
Proof. constructor; simpl; auto with htlh. Qed.

Definition create_arr (i : option io) (sz : nat) (ln : nat) : mon (reg * nat) :=
  fun s => let r := s.(st_freshreg) in
           OK (r, ln) (mkstate
                   s.(st_st)
                   (Pos.succ r)
                   (st_freshstate s)
                   s.(st_scldecls)
                   (AssocMap.set s.(st_freshreg) (i, VArray sz ln) s.(st_arrdecls))
                   (st_datapath s))
              (create_arr_state_incr s sz ln i).

Definition stack_correct (sz : Z) : bool :=
  (0 <=? sz) && (sz <? Integers.Ptrofs.modulus) && (Z.modulo sz 4 =? 0).

Definition max_pc_map (m : Maps.PTree.t stmnt) :=
  PTree.fold (fun m pc i => Pos.max m pc) m 1%positive.

Lemma max_pc_map_sound:
  forall m pc i, m!pc = Some i -> Ple pc (max_pc_map m).
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

Definition decide_order a b c d e f g h : {module_ordering a b c d e f g h} + {True}.
  refine (match bool_dec ((a <? b) && (b <? c) && (c <? d)
                          && (d <? e) && (e <? f) && (f <? g) && (g <? h))%positive true with
          | left t => left _
          | _ => _
          end); auto.
  simplify; repeat match goal with
                   | H: context[(_ <? _)%positive] |- _ => apply Pos.ltb_lt in H
                   end; unfold module_ordering; auto.
Defined.

Definition transf_module (f: function) : mon DHTL.module.
  refine (
  if stack_correct f.(fn_stacksize) then
    do fin <- create_reg (Some Voutput) 1;
    do rtrn <- create_reg (Some Voutput) 32;
    do (stack, stack_len) <- create_arr None 32 (Z.to_nat (f.(fn_stacksize) / 4));
    do start <- create_reg (Some Vinput) 1;
    do rst <- create_reg (Some Vinput) 1;
    do clk <- create_reg (Some Vinput) 1;
    do preg <- create_reg None 128;
    do _stmnt <- collectlist (transf_seq_blockM fin rtrn stack preg) (Maps.PTree.elements f.(GiblePar.fn_code));
    do _stmnt' <- collectlist (fun r => declare_reg (Some Vinput) r 32) f.(GiblePar.fn_params);
    do _stmnt'' <- collectlist declare_all_regs (Maps.PTree.elements f.(GiblePar.fn_code));
    do current_state <- get;
    match zle (Z.pos (max_pc_map current_state.(st_datapath))) Integers.Int.max_unsigned,
          decide_order (st_st current_state) fin rtrn stack start rst clk preg,
          max_list_dec (GiblePar.fn_params f) (st_st current_state)
    with
    | left LEDATA, left MORD, left WFPARAMS =>
        ret (DHTL.mkmodule
           f.(GiblePar.fn_params)
           current_state.(st_datapath)
           f.(fn_entrypoint)
           current_state.(st_st)
           stack
           stack_len
           fin
           rtrn
           start
           rst
           clk
           preg
           current_state.(st_scldecls)
           current_state.(st_arrdecls)
           None
           (max_pc_wf _ LEDATA)
           MORD
           _
           WFPARAMS)
    | _, _, _ => error (Errors.msg "More than 2^32 states.")
    end
  else error (Errors.msg "Stack size misalignment.")); discriminate.
Defined.

Definition max_state (f: function) : state :=
  let st := Pos.succ (max_reg_function f) in
  mkstate st
          (Pos.succ st)
          (Pos.succ (max_pc_function f))
          (AssocMap.set st (None, VScalar 32) (st_scldecls (init_state st)))
          (st_arrdecls (init_state st))
          (st_datapath (init_state st)).

Definition transl_module (f : function) : Errors.res DHTL.module :=
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

Definition transl_program (p : GiblePar.program) : Errors.res DHTL.program :=
  if main_is_internal p
  then transform_partial_program transl_fundef p
  else Errors.Error (Errors.msg "Main function is not Internal.").
