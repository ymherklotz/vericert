(* -*- mode: coq -*-
 * CoqUp: Verified high-level synthesis.
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

From Coq Require Import FSets.FMapPositive.

From coqup Require Import Verilog Coquplib Value.

From compcert Require Errors Op AST Integers Maps.
From compcert Require Import RTL.

Notation "a ! b" := (PositiveMap.find b a) (at level 1).

Definition node : Type := positive.
Definition reg : Type := positive.
Definition ident : Type := positive.

Hint Resolve PositiveMap.gempty : verilog_state.
Hint Resolve PositiveMap.gso : verilog_state.
Hint Resolve PositiveMap.gss : verilog_state.
Hint Resolve Ple_refl : verilog_state.

Inductive statetrans : Type :=
| StateGoto (p : node)
| StateCond (c : expr) (t f : node).

Definition valid_freshstate (stm: PositiveMap.t stmnt) (fs: node) :=
  forall (n: node),
    Plt n fs \/ stm!n = None.
Hint Unfold valid_freshstate : verilog_state.

Definition states_have_transitions (stm: PositiveMap.t stmnt) (st: PositiveMap.t statetrans) :=
  forall (n: node),
      (forall x, stm!n = Some x -> exists y, st!n = Some y)
      /\ (forall x, st!n = Some x -> exists y, stm!n = Some y).
Hint Unfold states_have_transitions : verilog_state.

Record state: Type := mkstate {
  st_freshreg: reg;
  st_freshstate: node;
  st_stm: PositiveMap.t stmnt;
  st_statetrans: PositiveMap.t statetrans;
  st_decl: PositiveMap.t (nat * nat);
  st_wf: valid_freshstate st_stm st_freshstate
         /\ states_have_transitions st_stm st_statetrans;
}.

Remark init_state_valid_freshstate:
  valid_freshstate (PositiveMap.empty stmnt) 1%positive.
Proof. auto with verilog_state. Qed.
Hint Resolve init_state_valid_freshstate : verilog_state.

Remark init_state_states_have_transitions:
  states_have_transitions (PositiveMap.empty stmnt) (PositiveMap.empty statetrans).
Proof.
  unfold states_have_transitions.
  split; intros; rewrite PositiveMap.gempty in H; discriminate.
Qed.
Hint Resolve init_state_states_have_transitions : verilog_state.

Remark init_state_wf:
    valid_freshstate (PositiveMap.empty stmnt) 1%positive
    /\ states_have_transitions (PositiveMap.empty stmnt) (PositiveMap.empty statetrans).
Proof. auto with verilog_state. Qed.

Definition init_state : state :=
  mkstate 1%positive
          1%positive
          (PositiveMap.empty stmnt)
          (PositiveMap.empty statetrans)
          (PositiveMap.empty (nat * nat))
          init_state_wf.

Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
      Ple s1.(st_freshreg) s2.(st_freshreg) ->
      Ple s1.(st_freshstate) s2.(st_freshstate) ->
      (forall n,
          s1.(st_stm)!n = None \/ s2.(st_stm)!n = s1.(st_stm)!n) ->
      (forall n,
          s1.(st_statetrans)!n = None
          \/ s2.(st_statetrans)!n = s1.(st_statetrans)!n) ->
      state_incr s1 s2.
Hint Constructors state_incr : verilog_state.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof. auto with verilog_state. Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H. inv H0. apply state_incr_intro; eauto using Ple_trans.
  - intros. destruct H3 with n.
    + left; assumption.
    + destruct H6 with n;
      [ rewrite <- H0; left; assumption
      | right; rewrite <- H0; apply H8
      ].
  - intros. destruct H4 with n.
    + left; assumption.
    + destruct H7 with n.
      * rewrite <- H0. left. assumption.
      * right. rewrite <- H0. apply H8.
Qed.

Inductive res (A: Type) (s: state): Type :=
| Error : Errors.errmsg -> res A s
| OK : A -> forall (s' : state), state_incr s s' -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s : state) => OK x s (state_incr_refl s).

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s : state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
      match g a s' with
      | Error msg => Error msg
      | OK b s'' i' => OK b s'' (state_incr_trans s s' s'' i i')
      end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

(* FIXME: This is disgusting and probably unecessary *)
Definition bind3 {A B C D: Type} (f: mon (A * B * C)) (g: A -> B -> C -> mon D) : mon D :=
  bind f (fun xyz => g (fst (fst xyz)) (snd (fst xyz)) (snd xyz)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
(at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
(at level 200, X ident, Y ident, A at level 100, B at level 200).
Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
(at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  fun (s : state) =>
    match f s with
    | OK a s' i => OK a s' i
    | Error _ => g s
    end.

Definition error {A: Type} (err: Errors.errmsg) : mon A := fun (s: state) => Error err.

Definition get : mon state := fun s => OK s s (state_incr_refl s).

Definition set (s: state) (i: forall s', state_incr s' s) : mon unit :=
  fun s' => OK tt s (i s').

Definition run_mon {A: Type} (s: state) (m: mon A): Errors.res A :=
    match m s with
    | OK a s' i => Errors.OK a
    | Error err => Errors.Error err
    end.

Definition map_state (f: state -> state) (i: forall s, state_incr s (f s)): mon state :=
  fun s => let s' := f s in OK s' s' (i s).

Fixpoint traverselist {A B: Type} (f: A -> mon B) (l: list A) {struct l}: mon (list B) :=
  match l with
  | nil => ret nil
  | x::xs =>
    do r <- f x;
    do rs <- traverselist f xs;
    ret (r::rs)
  end.

Definition nonblock (dst : reg) (e : expr) := Vnonblock (Vvar dst) e.
Definition block (dst : reg) (e : expr) := Vblock (Vvar dst) e.

Definition bop (op : binop) (r1 r2 : reg) : expr :=
  Vbinop op (Vvar r1) (Vvar r2).

Definition boplit (op : binop) (r : reg) (l : Integers.int) : expr :=
  Vbinop op (Vvar r) (Vlit (intToValue l)).

Definition boplitz (op: binop) (r: reg) (l: Z) : expr :=
  Vbinop op (Vvar r) (Vlit (ZToValue 32%nat l)).

Definition translate_comparison (c : Integers.comparison) (args : list reg) : mon expr :=
  match c, args with
  | Integers.Ceq, r1::r2::nil => ret (bop Veq r1 r2)
  | Integers.Cne, r1::r2::nil => ret (bop Vne r1 r2)
  | Integers.Clt, r1::r2::nil => ret (bop Vlt r1 r2)
  | Integers.Cgt, r1::r2::nil => ret (bop Vgt r1 r2)
  | Integers.Cle, r1::r2::nil => ret (bop Vle r1 r2)
  | Integers.Cge, r1::r2::nil => ret (bop Vge r1 r2)
  | _, _ => error (Errors.msg "Veriloggen: comparison instruction not implemented: other")
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
  | _, _ => error (Errors.msg "Veriloggen: comparison_imm instruction not implemented: other")
  end.

Definition translate_condition (c : Op.condition) (args : list reg) : mon expr :=
  match c, args with
  | Op.Ccomp c, _ => translate_comparison c args
  | Op.Ccompu c, _ => translate_comparison c args
  | Op.Ccompimm c i, _ => translate_comparison_imm c args i
  | Op.Ccompuimm c i, _ => translate_comparison_imm c args i
  | Op.Cmaskzero n, _ => error (Errors.msg "Veriloggen: condition instruction not implemented: Cmaskzero")
  | Op.Cmasknotzero n, _ => error (Errors.msg "Veriloggen: condition instruction not implemented: Cmasknotzero")
  | _, _ => error (Errors.msg "Veriloggen: condition instruction not implemented: other")
  end.

Definition translate_eff_addressing (a: Op.addressing) (args: list reg) : mon expr :=
  match a, args with
  | Op.Aindexed off, r1::nil => ret (boplitz Vadd r1 off)
  | Op.Aindexed2 off, r1::r2::nil => ret (Vbinop Vadd (Vvar r1) (boplitz Vadd r2 off))
  | Op.Ascaled scale offset, r1::nil =>
    ret (Vbinop Vadd (boplitz Vadd r1 scale) (Vlit (ZToValue 32%nat offset)))
  | Op.Aindexed2scaled scale offset, r1::r2::nil =>
    ret (Vbinop Vadd (boplitz Vadd r1 offset) (boplitz Vmul r2 scale))
  (* Stack arrays/referenced variables *)
  | Op.Ainstack a, nil => (* We need to be sure that the base address is aligned *)
    let a := Integers.Ptrofs.unsigned a in (* FIXME: Assuming stack offsets are +ve; is this ok? *)
    if (Z.eq_dec (Z.modulo a 4) 0) then ret (Vlit (ZToValue 32%nat (a / 4)))
    else error (Errors.msg "Veriloggen: eff_addressing misaligned stack offset")
  | _, _ => error (Errors.msg "Veriloggen: eff_addressing instruction not implemented: other")
  end.

(** Translate an instruction to a statement. *)
Definition translate_instr (op : Op.operation) (args : list reg) : mon expr :=
  match op, args with
  | Op.Omove, r::nil => ret (Vvar r)
  | Op.Ointconst n, _ => ret (Vlit (intToValue n))
  | Op.Oneg, r::nil => ret (Vunop Vneg (Vvar r))
  | Op.Osub, r1::r2::nil => ret (bop Vsub r1 r2)
  | Op.Omul, r1::r2::nil => ret (bop Vmul r1 r2)
  | Op.Omulimm n, r::nil => ret (boplit Vmul r n)
  | Op.Omulhs, _ => error (Errors.msg "Veriloggen: Instruction not implemented: Omulhs")
  | Op.Omulhu, _ => error (Errors.msg "Veriloggen: Instruction not implemented: Omulhu")
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
  | Op.Oshrximm n, r::nil => error (Errors.msg "Veriloggen: Instruction not implemented: Oshrximm")
  | Op.Oshru, r1::r2::nil => error (Errors.msg "Veriloggen: Instruction not implemented: Oshru")
  | Op.Oshruimm n, r::nil => error (Errors.msg "Veriloggen: Instruction not implemented: Oshruimm")
  | Op.Ororimm n, r::nil => error (Errors.msg "Veriloggen: Instruction not implemented: Ororimm")
  | Op.Oshldimm n, r::nil => error (Errors.msg "Veriloggen: Instruction not implemented: Oshldimm")
  | Op.Ocmp c, _ => translate_condition c args
  | Op.Olea a, _ => translate_eff_addressing a args
  | Op.Oleal a, _ => translate_eff_addressing a args (* FIXME: Need to be careful here; large arrays might fail? *)
  | Op.Ocast32signed, r::nill => ret (Vvar r) (* FIXME: Don't need to sign extend for now since everything is 32 bit? *)
  | _, _ => error (Errors.msg "Veriloggen: Instruction not implemented: other")
  end.

Remark add_instr_valid_freshstate:
  forall (s: state) (n: node) (st: stmnt),
    Plt n (st_freshstate s) ->
    valid_freshstate (PositiveMap.add n st s.(st_stm)) (st_freshstate s).
Proof.
  unfold valid_freshstate. intros.
  case (peq n0 n); intro.
  subst n0. left. assumption.
  rewrite PositiveMap.gso.
  apply (st_wf s). assumption.
Qed.
Hint Resolve add_instr_valid_freshstate : verilog_state.

Remark add_instr_states_have_transitions:
  forall (s: state) (n n': node) (st: stmnt),
  states_have_transitions
    (PositiveMap.add n st s.(st_stm))
    (PositiveMap.add n (StateGoto n') s.(st_statetrans)).
Proof.
  unfold states_have_transitions. split; intros.
  - case (peq n0 n); intro.
    subst. exists (StateGoto n'). apply PositiveMap.gss.
    rewrite PositiveMap.gso. rewrite PositiveMap.gso in H.
    assert (H2 := st_wf s). inv H2. unfold states_have_transitions in H1.
    destruct H1 with n0. apply H2 with x. assumption. assumption. assumption.
  - case (peq n0 n); intro.
    subst. exists st. apply PositiveMap.gss.
    rewrite PositiveMap.gso. rewrite PositiveMap.gso in H.
    assert (H2 := st_wf s). inv H2. unfold states_have_transitions in H1.
    destruct H1 with n0. apply H3 with x. assumption. assumption. assumption.
Qed.
Hint Resolve add_instr_states_have_transitions : verilog_state.

Remark add_instr_state_wf:
  forall (s: state) (n n': node) (st: stmnt) (LT: Plt n (st_freshstate s)),
    valid_freshstate (PositiveMap.add n st (st_stm s)) (st_freshstate s)
    /\ states_have_transitions
     (PositiveMap.add n st s.(st_stm))
     (PositiveMap.add n (StateGoto n') s.(st_statetrans)).
Proof. auto with verilog_state. Qed.

Lemma add_instr_state_incr :
  forall s n n' st LT,
    (st_stm s)!n = None ->
    (st_statetrans s)!n = None ->
    state_incr s
    (mkstate s.(st_freshreg)
             (st_freshstate s)
             (PositiveMap.add n st s.(st_stm))
             (PositiveMap.add n (StateGoto n') s.(st_statetrans))
             s.(st_decl)
             (add_instr_state_wf s n n' st LT)).
Proof.
  constructor; intros;
    try (simpl; destruct (peq n n0); subst);
    auto with verilog_state.
Qed.

Definition check_empty_node_stm:
  forall (s: state) (n: node), { s.(st_stm)!n = None } + { True }.
Proof.
  intros. case (s.(st_stm)!n); intros. right; auto. left; auto.
Defined.

Definition check_empty_node_statetrans:
  forall (s: state) (n: node), { s.(st_statetrans)!n = None } + { True }.
Proof.
  intros. case (s.(st_statetrans)!n); intros. right; auto. left; auto.
Defined.

Definition add_instr (n : node) (n' : node) (st : stmnt) : mon unit :=
  fun s =>
    match plt n (st_freshstate s), check_empty_node_stm s n, check_empty_node_statetrans s n with
    | left LT, left STM, left TRANS =>
      OK tt (mkstate s.(st_freshreg)
                     (st_freshstate s)
                     (PositiveMap.add n st s.(st_stm))
                     (PositiveMap.add n (StateGoto n') s.(st_statetrans))
                     s.(st_decl)
                     (add_instr_state_wf s n n' st LT))
         (add_instr_state_incr s n n' st LT STM TRANS)
    | _, _, _ => Error (Errors.msg "Veriloggen.add_instr")
    end.

Definition add_reg (r: reg) (s: state) : state :=
  mkstate (st_freshreg s)
          (st_freshstate s)
          (st_stm s)
          (st_statetrans s)
          (PositiveMap.add r (32%nat, 1%nat) (st_decl s))
          (st_wf s).

Lemma add_reg_state_incr:
  forall r s,
  state_incr s (add_reg r s).
Proof. auto with verilog_state. Qed.

Definition add_instr_reg (r: reg) (n: node) (n': node) (st: stmnt) : mon unit :=
  do _ <- map_state (add_reg r) (add_reg_state_incr r);
  add_instr n n' st.

Lemma change_decl_state_incr:
  forall s decl',
    state_incr s (mkstate
         (st_freshreg s)
         (st_freshstate s)
         (st_stm s)
         (st_statetrans s)
         decl'
         (st_wf s)).
Proof. auto with verilog_state. Qed.

Lemma decl_io_state_incr:
  forall s,
    state_incr s (mkstate
         (Pos.succ (st_freshreg s))
         (st_freshstate s)
         (st_stm s)
         (st_statetrans s)
         (st_decl s)
         (st_wf s)).
Proof. constructor; simpl; auto using Ple_succ with verilog_state. Qed.

Definition decl_io (sz: nat) (ln: nat): mon (reg * nat * nat) :=
  fun s => let r := s.(st_freshreg) in
           OK (r, sz, ln) (mkstate
                     (Pos.succ r)
                     (st_freshstate s)
                     (st_stm s)
                     (st_statetrans s)
                     (st_decl s)
                     (st_wf s))
              (decl_io_state_incr s).

Definition declare_reg (r: reg) (sz: nat) (ln: nat): mon (reg * nat * nat) :=
  fun s => OK (r, sz, ln) (mkstate
                      (st_freshreg s)
                      (st_freshstate s)
                      (st_stm s)
                      (st_statetrans s)
                      (PositiveMap.add r (sz, ln) s.(st_decl))
                      (st_wf s))
              (change_decl_state_incr s (PositiveMap.add r (sz, ln) s.(st_decl))).

Definition decl_fresh_reg (sz : nat) (ln : nat) : mon (reg * nat * nat) :=
  do (r, s, l) <- decl_io sz ln;
  declare_reg r s l.

Lemma add_branch_instr_states_have_transitions:
  forall s e n n1 n2,
    states_have_transitions (PositiveMap.add n Vskip (st_stm s))
                            (PositiveMap.add n (StateCond e n1 n2) (st_statetrans s)).
Proof.
  split; intros; destruct (peq n0 n); subst; eauto with verilog_state;
    rewrite PositiveMap.gso in *;
    assert (H1 := (st_wf s)); inv H1; unfold states_have_transitions in H2;
    destruct H2 with n0; try (apply H1 with x); try (apply H3 with x); assumption.
Qed.

Lemma add_branch_valid_freshstate:
  forall s n,
  Plt n (st_freshstate s) ->
  valid_freshstate (PositiveMap.add n Vskip (st_stm s)) (st_freshstate s).
Proof.
  unfold valid_freshstate; intros; destruct (peq n0 n).
    - subst; auto.
    - assert (H1 := st_wf s); destruct H1;
      unfold valid_freshstate in H0; rewrite PositiveMap.gso; auto.
Qed.

Lemma add_branch_instr_st_wf:
  forall s e n n1 n2,
    Plt n (st_freshstate s) ->
    valid_freshstate (PositiveMap.add n Vskip (st_stm s)) (st_freshstate s)
    /\ states_have_transitions (PositiveMap.add n Vskip (st_stm s))
                               (PositiveMap.add n (StateCond e n1 n2) (st_statetrans s)).
Proof.
  auto using add_branch_valid_freshstate, add_branch_instr_states_have_transitions.
Qed.

Lemma add_branch_instr_state_incr:
  forall s e n n1 n2 LT,
    (st_stm s) ! n = None ->
    (st_statetrans s) ! n = None ->
    state_incr s (mkstate
                (st_freshreg s)
                (st_freshstate s)
                (PositiveMap.add n Vskip (st_stm s))
                (PositiveMap.add n (StateCond e n1 n2) (st_statetrans s))
                (st_decl s)
                (add_branch_instr_st_wf s e n n1 n2 LT)).
Proof.
  intros. apply state_incr_intro; simpl;
            try (intros; destruct (peq n0 n); subst);
            auto with verilog_state.
Qed.

Definition add_branch_instr (e: expr) (n n1 n2: node) : mon unit :=
  fun s =>
    match plt n (st_freshstate s), check_empty_node_stm s n, check_empty_node_statetrans s n with
    | left LT, left NSTM, left NTRANS =>
      OK tt (mkstate
                (st_freshreg s)
                (st_freshstate s)
                (PositiveMap.add n Vskip (st_stm s))
                (PositiveMap.add n (StateCond e n1 n2) (st_statetrans s))
                (st_decl s)
                (add_branch_instr_st_wf s e n n1 n2 LT))
         (add_branch_instr_state_incr s e n n1 n2 LT NSTM NTRANS)
    | _, _, _ => Error (Errors.msg "Veriloggen: add_branch_instr")
    end.

Definition translate_arr_access (mem : AST.memory_chunk) (addr : Op.addressing)
           (args : list reg) (stack : reg) : mon expr :=
  match addr, args with (* TODO: We should be more methodical here; what are the possibilities?*)
  | Op.Aindexed2scaled scale offset, r1::r2::nil =>
    if ((Z.eqb (Z.modulo scale 4) 0) && (Z.eqb (Z.modulo offset 4) 0))
    then ret (Vvari stack (Vbinop Vadd (boplitz Vadd r1 (offset / 4)) (boplitz Vmul r2 (scale / 4))))
    else error (Errors.msg "Veriloggen: translate_arr_access address misaligned")
  | _, _ => error (Errors.msg "Veriloggen: translate_arr_access unsuported addressing")
  end.

Definition transf_instr (fin rtrn stack: reg) (ni: node * instruction) : mon unit :=
  match ni with
    (n, i) =>
    match i with
    | Inop n' => add_instr n n' Vskip
    | Iop op args dst n' =>
      do instr <- translate_instr op args;
      add_instr_reg dst n n' (block dst instr)
    | Iload mem addr args dst n' =>
      do src <- translate_arr_access mem addr args stack;
      add_instr_reg dst n n' (block dst src)
    | Istore mem addr args src n' =>
      do dst <- translate_arr_access mem addr args stack;
      add_instr_reg src n n' (Vblock dst (Vvar src)) (* TODO: Could juse use add_instr? reg exists. *)
    | Icall _ _ _ _ _ => error (Errors.msg "Calls are not implemented.")
    | Itailcall _ _ _ => error (Errors.msg "Tailcalls are not implemented.")
    | Ibuiltin _ _ _ _ => error (Errors.msg "Builtin functions not implemented.")
    | Icond cond args n1 n2 =>
      do e <- translate_condition cond args;
      add_branch_instr e n n1 n2
    | Ijumptable _ _ => error (Errors.msg "Jumptable not implemented")
    | Ireturn r =>
      match r with
      | Some r' =>
        add_instr n n (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z))) (block rtrn (Vvar r')))
      | None =>
        add_instr n n (block fin (Vlit (ZToValue 1%nat 1%Z)))
      end
    end
  end.

Definition make_stm_cases (s : positive * stmnt) : expr * stmnt :=
  match s with (a, b) => (posToExpr 32 a, b) end.

Definition make_stm (r : reg) (s : PositiveMap.t stmnt) : stmnt :=
  Vcase (Vvar r) (map make_stm_cases (PositiveMap.elements s)) (Some Vskip).

Definition make_statetrans_cases (r : reg) (st : positive * statetrans) : expr * stmnt :=
  match st with
  | (n, StateGoto n') => (posToExpr 32 n, nonblock r (posToExpr 32 n'))
  | (n, StateCond c n1 n2) => (posToExpr 32 n, nonblock r (Vternary c (posToExpr 32 n1) (posToExpr 32 n2)))
  end.

Definition make_statetrans (r : reg) (s : PositiveMap.t statetrans) : stmnt :=
  Vcase (Vvar r) (map (make_statetrans_cases r) (PositiveMap.elements s)) (Some Vskip).

Fixpoint allocate_regs (e : list (reg * (nat * nat))) {struct e} : list module_item :=
  match e with
  | (r, (n, 1%nat))::es => Vdecl r n :: allocate_regs es
  | (r, (n, l))::es => Vdeclarr r n l :: allocate_regs es
  | nil => nil
  end.

Definition make_module_items (entry: node) (clk st rst: reg) (s: state) : list module_item :=
  (Valways_ff (Vposedge clk)
    (Vcond (Vbinop Veq (Vinputvar rst) (Vlit (ZToValue 1 1)))
      (nonblock st (posToExpr 32 entry))
      (make_statetrans st s.(st_statetrans))))
  :: (Valways_ff (Vposedge clk) (make_stm st s.(st_stm)))
  :: (allocate_regs (PositiveMap.elements s.(st_decl))).

(** To start out with, the assumption is made that there is only one
    function/module in the original code. *)

Definition set_int_size (r: reg) : reg * nat := (r, 32%nat).

(* FIXME: Tuple nesting madness everywhere. *)
Definition transf_module (f: function) : mon module :=
  do fin <- decl_io 1%nat 1%nat;
  do rtrn <- decl_io 32%nat 1%nat;
  do stack <- decl_fresh_reg 32%nat (Z.to_nat (f.(fn_stacksize) / 4));
  do _ <- traverselist (transf_instr (fst (fst fin)) (fst (fst rtrn)) (fst (fst stack))) (Maps.PTree.elements f.(fn_code));
  do start <- decl_io 1%nat 1%nat;
  do rst <- decl_io 1%nat 1%nat;
  do clk <- decl_io 1%nat 1%nat;
  do st <- decl_fresh_reg 32%nat 1%nat;
  do current_state <- get;
  let mi := make_module_items f.(fn_entrypoint) (fst (fst clk)) (fst (fst st)) (fst (fst rst)) current_state in
  ret (mkmodule (fst start) (fst rst) (fst clk) (fst fin) (fst rtrn) (map set_int_size f.(fn_params)) mi).

Fixpoint main_function (main : ident) (flist : list (ident * AST.globdef fundef unit))
{struct flist} : option function :=
  match flist with
  | (i, AST.Gfun (AST.Internal f)) :: xs =>
    if Pos.eqb i main
    then Some f
    else main_function main xs
  | _ :: xs => main_function main xs
  | nil => None
  end.

Lemma max_state_valid_freshstate:
  forall f,
    valid_freshstate (st_stm init_state) (Pos.succ (max_pc_function f)).
Proof. unfold valid_freshstate; simpl; auto with verilog_state. Qed.
Hint Resolve max_state_valid_freshstate : verilog_state.

Lemma max_state_st_wf:
  forall f,
    valid_freshstate (st_stm init_state) (Pos.succ (max_pc_function f))
    /\ states_have_transitions (st_stm init_state) (st_statetrans init_state).
Proof. auto with verilog_state. Qed.

Definition max_state (f: function) : state :=
  mkstate (Pos.succ (max_reg_function f))
          (Pos.succ (max_pc_function f))
          (st_stm init_state)
          (st_statetrans init_state)
          (st_decl init_state)
          (max_state_st_wf f).

Definition transf_program (d : program) : Errors.res module :=
  match main_function d.(AST.prog_main) d.(AST.prog_defs) with
  | Some f => run_mon (max_state f) (transf_module f)
  | _ => Errors.Error (Errors.msg "Veriloggen: could not find main function")
  end.
