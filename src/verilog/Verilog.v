(* -*- mode: coq -*-
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

From Coq Require Import
  Structures.OrderedTypeEx
  FSets.FMapPositive
  Program.Basics
  PeanoNat
  ZArith
  Lists.List
  Program.

Import ListNotations.

From coqup Require Import common.Coquplib common.Show verilog.Value.

From compcert Require Integers.
From compcert Require Import Errors.

Notation "a ! b" := (PositiveMap.find b a) (at level 1).

Definition reg : Type := positive.
Definition node : Type := positive.
Definition szreg : Type := reg * nat.

Definition assoclist : Type := PositiveMap.t value.

(** * Verilog AST

The Verilog AST is defined here, which is the target language of the
compilation.

** Value

The Verilog [value] is a bitvector containg a size and the actual bitvector. In
this case, the [Word.word] type is used as many theorems about that bitvector
have already been proven. *)

Definition estate : Type := assoclist * assoclist.

(** ** Binary Operators

These are the binary operations that can be represented in Verilog. Ideally,
multiplication and division would be done by custom modules which could al so be
scheduled properly. However, for now every Verilog operator is assumed to take
one clock cycle. *)

Inductive binop : Type :=
| Vadd : binop  (** addition (binary [+]) *)
| Vsub : binop  (** subtraction (binary [-]) *)
| Vmul : binop  (** multiplication (binary [*]) *)
| Vdiv : binop  (** division (binary [/]) *)
| Vdivu : binop  (** division unsigned (binary [/]) *)
| Vmod : binop  (** remainder ([%]) *)
| Vmodu : binop  (** remainder unsigned ([%]) *)
| Vlt : binop   (** less than ([<]) *)
| Vltu : binop   (** less than unsigned ([<]) *)
| Vgt : binop   (** greater than ([>]) *)
| Vgtu : binop   (** greater than unsigned ([>]) *)
| Vle : binop   (** less than or equal ([<=]) *)
| Vleu : binop   (** less than or equal unsigned ([<=]) *)
| Vge : binop   (** greater than or equal ([>=]) *)
| Vgeu : binop   (** greater than or equal unsigned ([>=]) *)
| Veq : binop   (** equal to ([==]) *)
| Vne : binop   (** not equal to ([!=]) *)
| Vand : binop  (** and (binary [&]) *)
| Vor : binop   (** or (binary [|]) *)
| Vxor : binop  (** xor (binary [^|]) *)
| Vshl : binop  (** shift left ([<<]) *)
| Vshr : binop. (** shift right ([>>]) *)

(** ** Unary Operators *)

Inductive unop : Type :=
| Vneg  (** negation ([~]) *)
| Vnot. (** not operation [!] *)

(** ** Expressions *)

Inductive expr : Type :=
| Vlit : value -> expr
| Vvar : reg -> expr
| Vinputvar : reg -> expr
| Vbinop : binop -> expr -> expr -> expr
| Vunop : unop -> expr -> expr
| Vternary : expr -> expr -> expr -> expr.

Definition posToExpr (sz : nat) (p : positive) : expr :=
  Vlit (posToValue sz p).

(** ** Statements *)

Inductive stmnt : Type :=
| Vskip : stmnt
| Vseq : stmnt -> stmnt -> stmnt
| Vcond : expr -> stmnt -> stmnt -> stmnt
| Vcase : expr -> list (expr * stmnt) -> option stmnt -> stmnt
| Vblock : expr -> expr -> stmnt
| Vnonblock : expr -> expr -> stmnt.

(** ** Edges

These define when an always block should be triggered, for example if the always
block should be triggered synchronously at the clock edge, or asynchronously for
combinational logic.

[edge] is not part of [stmnt] in this formalisation because is closer to the
semantics that are used. *)

Inductive edge : Type :=
| Vposedge : reg -> edge
| Vnegedge : reg -> edge
| Valledge : edge
| Voredge : edge -> edge -> edge.

(** ** Module Items

Module items can either be declarations ([Vdecl]) or always blocks ([Valways]).
The declarations are always register declarations as combinational logic can be
done using combinational always block instead of continuous assignments. *)

Inductive module_item : Type :=
| Vdecl : reg -> nat -> module_item
| Valways : edge -> stmnt -> module_item
| Valways_ff : edge -> stmnt -> module_item
| Valways_comb : edge -> stmnt -> module_item.

(** The main module type containing all the important control signals

- [mod_start] If set, starts the computations in the module.
- [mod_reset] If set, reset the state in the module.
- [mod_clk] The clock that controls the computation in the module.
- [mod_args] The arguments to the module.
- [mod_finish] Bit that is set if the result is ready.
- [mod_return] The return value that was computed.
- [mod_body] The body of the module, including the state machine.
*)

Record module : Type := mkmodule {
  mod_start : szreg;
  mod_reset : szreg;
  mod_clk : szreg;
  mod_finish : szreg;
  mod_return : szreg;
  mod_args : list szreg;
  mod_body : list module_item;
}.

(** Convert a [positive] to an expression directly, setting it to the right
    size. *)
Definition posToLit (p : positive) : expr :=
  Vlit (posToValueAuto p).

Coercion Vlit : value >-> expr.
Coercion Vvar : reg >-> expr.

Definition fext := PositiveMap.t value.
Definition fextclk := nat -> fext.

Inductive state: Type :=
  Runstate:
    forall (assoc : assoclist)
           (nbassoc : assoclist)
           (f : fextclk)
           (cycle : positive),
    state.

Definition binop_run (op : binop) : forall v1 v2 : value, vsize v1 = vsize v2 -> value :=
  match op with
  | Vadd => vplus
  | Vsub => vminus
  | Vmul => vmul
  | Vdiv => vdivs
  | Vdivu => vdiv
  | Vmod => vmods
  | Vmodu => vmod
  | Vlt => vlts
  | Vltu => vlt
  | Vgt => vgts
  | Vgtu => vgt
  | Vle => vles
  | Vleu => vle
  | Vge => vges
  | Vgeu => vge
  | Veq => veq
  | Vne => vne
  | Vand => vand
  | Vor => vor
  | Vxor => vxor
  | Vshl => vshl
  | Vshr => vshr
  end.

Definition unop_run (op : unop) : value -> value :=
  match op with
  | Vneg => vnot
  | Vnot => vbitneg
  end.

Inductive expr_runp : state -> expr -> value -> Prop :=
  | erun_Vlit :
      forall s v,
      expr_runp s (Vlit v) v
  | erun_Vvar :
      forall assoc na f c v r,
      assoc!r = Some v ->
      expr_runp (Runstate assoc na f c) (Vvar r) v
  | erun_Vinputvar :
      forall s r v,
      expr_runp s (Vinputvar r) v
  | erun_Vbinop :
      forall s op l r lv rv oper EQ,
      expr_runp s l lv ->
      expr_runp s r rv ->
      oper = binop_run op ->
      expr_runp s (Vbinop op l r) (oper lv rv EQ)
  | erun_Vunop :
      forall s u vu op oper,
      expr_runp s u vu ->
      oper = unop_run op ->
      expr_runp s (Vunop op u) (oper vu)
  | erun_Vternary_true :
      forall s c ts fs vc vt,
      expr_runp s c vc ->
      expr_runp s ts vt ->
      valueToBool vc = true ->
      expr_runp s (Vternary c ts fs) vt
  | erun_Vternary_false :
      forall s c ts fs vc vf,
      expr_runp s c vc ->
      expr_runp s fs vf ->
      valueToBool vc = false ->
      expr_runp s (Vternary c ts fs) vf.

Definition handle_opt {A : Type} (err : errmsg) (val : option A)
  : res A :=
  match val with
  | Some a => OK a
  | None => Error err
  end.

Definition handle_def {A : Type} (a : A) (val : option A)
  : res A :=
  match val with
  | Some a' => OK a'
  | None => OK a
  end.

Local Open Scope error_monad_scope.

Definition access_fext (s : state) (r : reg) : res value :=
  match s with
  | Runstate _ _ f c =>
    match PositiveMap.find r (f (Pos.to_nat c)) with
    | Some v => OK v
    | _ => OK (ZToValue 1 0)
    end
  end.

(* TODO FIX Vvar case without default *)
Fixpoint expr_run (s : state) (e : expr)
         {struct e} : res value :=
  match e with
  | Vlit v => OK v
  | Vvar r => match s with
              | Runstate assoc _ _ _ => handle_def (ZToValue 32 0) assoc!r
              end
  | Vinputvar r => access_fext s r
  | Vbinop op l r =>
    let lv := expr_run s l in
    let rv := expr_run s r in
    let oper := binop_run op in
    do lv' <- lv;
    do rv' <- rv;
    handle_opt (msg "Verilog: sizes are not equal")
               (eq_to_opt lv' rv' (oper lv' rv'))
  | Vunop op e =>
    let oper := unop_run op in
    do ev <- expr_run s e;
    OK (oper ev)
  | Vternary c te fe =>
    do cv <- expr_run s c;
    if valueToBool cv then expr_run s te else expr_run s fe
  end.

(** Return the name of the lhs of an assignment. For now, this function is quite
simple because only assignment to normal variables is supported and needed. *)

Definition assign_name (e : expr) : res reg :=
  match e with
  | Vvar r => OK r
  | _ => Error (msg "Verilog: expression not supported on lhs of assignment")
  end.

Fixpoint stmnt_height (st : stmnt) {struct st} : nat :=
  match st with
  | Vseq s1 s2 => S (stmnt_height s1 + stmnt_height s2)
  | Vcond _ s1 s2 => S (Nat.max (stmnt_height s1) (stmnt_height s2))
  | Vcase _ ls (Some st) =>
    S (fold_right (fun t acc => Nat.max acc (stmnt_height (snd t))) 0%nat ls)
  | _ => 1
  end.

Fixpoint find_case_stmnt (s : state) (v : value) (cl : list (expr * stmnt))
         {struct cl} : option (res stmnt) :=
  match cl with
  | (e, st)::xs =>
    match expr_run s e with
    | OK v' =>
      match eq_to_opt v v' (veq v v') with
      | Some eq => if valueToBool eq then Some (OK st) else find_case_stmnt s v xs
      | None => Some (Error (msg "Verilog: equality check sizes not equal"))
      end
    | Error msg => Some (Error msg)
    end
  | _ => None
  end.

Fixpoint stmnt_run' (n : nat) (s : state) (st : stmnt) {struct n} : res state :=
  match n with
  | S n' =>
    match st with
    | Vskip => OK s
    | Vseq s1 s2 =>
      do s' <- stmnt_run' n' s s1;
      stmnt_run' n' s' s2
    | Vcond c st sf =>
      do cv <- expr_run s c;
      if valueToBool cv
      then stmnt_run' n' s st
      else stmnt_run' n' s sf
    | Vcase e cl defst =>
      do v <- expr_run s e;
      match find_case_stmnt s v cl with
      | Some (OK st') => stmnt_run' n' s st'
      | Some (Error msg) => Error msg
      | None => do s' <- handle_opt (msg "Verilog: no case was matched")
                                    (option_map (stmnt_run' n' s) defst); s'
      end
    | Vblock lhs rhs =>
      match s with
      | Runstate assoc nbassoc f c =>
        do name <- assign_name lhs;
        do rhse <- expr_run s rhs;
        OK (Runstate (PositiveMap.add name rhse assoc) nbassoc f c)
      end
    | Vnonblock lhs rhs =>
      match s with
      | Runstate assoc nbassoc f c =>
        do name <- assign_name lhs;
        do rhse <- expr_run s rhs;
        OK (Runstate assoc (PositiveMap.add name rhse nbassoc) f c)
      end
    end
  | _ => OK s
  end.

Definition stmnt_run (s : state) (st : stmnt) : res state :=
  stmnt_run' (stmnt_height st) s st.

Inductive not_matched (s : state) (caseval : value) (curr : expr * stmnt) : Prop :=
  not_in:
    forall currval,
    expr_runp s (fst curr) currval ->
    caseval <> currval ->
    not_matched s caseval curr.

Inductive stmnt_runp: state -> stmnt -> state -> Prop :=
| stmnt_run_Vskip:
    forall s, stmnt_runp s Vskip s
| stmnt_run_Vseq:
    forall st1 st2 s0 s1 s2,
    stmnt_runp s0 st1 s1 ->
    stmnt_runp s1 st2 s2 ->
    stmnt_runp s0 (Vseq st1 st2) s2
| stmnt_runp_Vcond_true:
    forall s0 s1 c vc stt stf,
    expr_runp s0 c vc ->
    valueToBool vc = true ->
    stmnt_runp s0 stt s1 ->
    stmnt_runp s0 (Vcond c stt stf) s1
| stmnt_runp_Vcond_false:
    forall s0 s1 c vc stt stf,
    expr_runp s0 c vc ->
    valueToBool vc = false ->
    stmnt_runp s0 stf s1 ->
    stmnt_runp s0 (Vcond c stt stf) s1
| stmnt_runp_Vcase:
    forall e ve s0 s1 me mve sc clst def,
    expr_runp s0 e ve ->
    expr_runp s0 me mve ->
    mve = ve ->
    In (me, sc) clst ->
    stmnt_runp s0 sc s1 ->
    stmnt_runp s0 (Vcase e clst def) s1
| stmnt_runp_Vcase_default:
    forall s0 st s1 e ve clst,
    expr_runp s0 e ve ->
    Forall (not_matched s0 ve) clst ->
    stmnt_runp s0 st s1 ->
    stmnt_runp s0 (Vcase e clst (Some st)) s1
| stmnt_runp_Vblock:
    forall lhs name rhs rhsval s assoc assoc' nbassoc f cycle,
    assign_name lhs = OK name ->
    expr_runp s rhs rhsval ->
    assoc' = (PositiveMap.add name rhsval assoc) ->
    stmnt_runp (Runstate assoc nbassoc f cycle)
               (Vblock lhs rhs)
               (Runstate assoc' nbassoc f cycle)
| stmnt_runp_Vnonblock:
    forall lhs name rhs rhsval s assoc nbassoc nbassoc' f cycle,
    assign_name lhs = OK name ->
    expr_runp s rhs rhsval ->
    nbassoc' = (PositiveMap.add name rhsval nbassoc) ->
    stmnt_runp (Runstate assoc nbassoc f cycle)
               (Vblock lhs rhs)
               (Runstate assoc nbassoc' f cycle).

Fixpoint mi_step (s : state) (m : list module_item) {struct m} : res state :=
  let run := fun st ls =>
              do s' <- stmnt_run s st;
              mi_step s' ls
  in
  match m with
  | (Valways _ st)::ls => run st ls
  | (Valways_ff _ st)::ls => run st ls
  | (Valways_comb _ st)::ls => run st ls
  | (Vdecl _ _)::ls => mi_step s ls
  | nil => OK s
  end.

Definition add_assoclist (r : reg) (v : value) (assoc : assoclist) : assoclist :=
  PositiveMap.add r v assoc.

Definition merge_assoclist (nbassoc assoc : assoclist) : assoclist :=
  PositiveMap.fold add_assoclist nbassoc assoc.

Definition empty_assoclist : assoclist := PositiveMap.empty value.

Definition mi_step_commit (s : state) (m : list module_item) : res state :=
  match mi_step s m with
  | OK (Runstate assoc nbassoc f c) =>
    OK (Runstate (merge_assoclist nbassoc assoc) empty_assoclist f c)
  | Error msg => Error msg
  end.

Fixpoint mi_run (f : fextclk) (assoc : assoclist) (m : list module_item) (n : nat)
         {struct n} : res assoclist :=
  match n with
  | S n' =>
    do assoc' <- mi_run f assoc m n';
    match mi_step_commit (Runstate assoc' empty_assoclist f (Pos.of_nat n')) m with
    | OK (Runstate assoc _ _ _) => OK assoc
    | Error m => Error m
    end
  | O => OK assoc
  end.

(** Resets the module into a known state, so that it can be executed.  This is
assumed to be the starting state of the module, and may have to be changed if
other arguments to the module are also to be supported. *)

Definition initial_fextclk (m : module) : fextclk :=
  fun x => match x with
           | S O => (add_assoclist (fst (mod_reset m)) (ZToValue 1 1) empty_assoclist)
           | _ => (add_assoclist (fst (mod_reset m)) (ZToValue 1 0) empty_assoclist)
           end.

Definition module_run (n : nat) (m : module) : res assoclist :=
  mi_run (initial_fextclk m) empty_assoclist (mod_body m) n.

Local Close Scope error_monad_scope.

(*Theorem value_eq_size_if_eq:
  forall lv rv EQ,
  vsize lv = vsize rv -> value_eq_size lv rv = left EQ.
Proof. intros. unfold value_eq_size.

Theorem expr_run_same:
  forall assoc e v, expr_run assoc e = OK v <-> expr_runp assoc e v.
Proof.
  split; generalize dependent v; generalize dependent assoc.
  - induction e.
    + intros. inversion H. constructor.
    + intros. inversion H. constructor. assumption.
    + intros. inversion H. destruct (expr_run assoc e1) eqn:?. destruct (expr_run assoc e2) eqn:?.
      unfold eq_to_opt in H1. destruct (value_eq_size v0 v1) eqn:?. inversion H1.
      constructor. apply IHe1. assumption. apply IHe2. assumption. reflexivity. discriminate. discriminate.
      discriminate.
    + intros. inversion H. destruct (expr_run assoc e) eqn:?. unfold option_map in H1.
      inversion H1. constructor. apply IHe. assumption. reflexivity. discriminate.
    + intros. inversion H. destruct (expr_run assoc e1) eqn:?. destruct (valueToBool v0) eqn:?.
      eapply erun_Vternary_true. apply IHe1. eassumption. apply IHe2. eassumption. assumption.
      eapply erun_Vternary_false. apply IHe1. eassumption. apply IHe3. eassumption. assumption.
      discriminate.
  - induction e.
    + intros. inversion H. reflexivity.
    + intros. inversion H. subst. simpl. assumption.
    + intros. inversion H. subst. simpl. apply IHe1 in H4. rewrite H4.
      apply IHe2 in H6. rewrite H6. unfold eq_to_opt. assert (vsize lv = vsize rv).
      apply EQ. apply (value_eq_size_if_eq lv rv EQ) in H0. rewrite H0. reflexivity.
    + intros. inversion H. subst. simpl. destruct (expr_run assoc e) eqn:?. simpl.
      apply IHe in H3. rewrite Heqo in H3.
      inversion H3. subst. reflexivity. apply IHe in H3. rewrite Heqo in H3. discriminate.
    + intros. inversion H. subst. simpl. apply IHe1 in H4. rewrite H4. rewrite H7.
      apply IHe2 in H6. rewrite H6. reflexivity.
      subst. simpl. apply IHe1 in H4. rewrite H4. rewrite H7. apply IHe3.
      assumption.
Qed.

 *)

Inductive initial_state (m: module): state -> Prop :=
| initial_state_intro:
    initial_state m (Runstate empty_assoclist empty_assoclist (initial_fextclk m) xH).

(** A final state is a [Returnstate] with an empty call stack. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.

(** The small-step semantics for a module. *)

Definition semantics (p: module) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
