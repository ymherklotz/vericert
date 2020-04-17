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

Inductive state: Type :=
| State:
    forall (assoc: assoclist)
           (nbassoc: assoclist),
    state
| Callstate: state
| Returnstate: state.

Definition fext := reg -> res value.
Definition fextclk := nat -> fext.

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

Inductive expr_runp : assoclist -> expr -> value -> Prop :=
  | erun_Vlit :
      forall a v,
      expr_runp a (Vlit v) v
  | erun_Vvar :
      forall assoc v r,
      assoc!r = Some v ->
      expr_runp assoc (Vvar r) v
  | erun_Vbinop :
      forall a op l r lv rv oper EQ,
      expr_runp a l lv ->
      expr_runp a r rv ->
      oper = binop_run op ->
      expr_runp a (Vbinop op l r) (oper lv rv EQ)
  | erun_Vunop :
      forall a u vu op oper,
      expr_runp a u vu ->
      oper = unop_run op ->
      expr_runp a (Vunop op u) (oper vu)
  | erun_Vternary_true :
      forall a c t f vc vt,
      expr_runp a c vc ->
      expr_runp a t vt ->
      valueToBool vc = true ->
      expr_runp a (Vternary c t f) vt
  | erun_Vternary_false :
      forall a c t f vc vf,
      expr_runp a c vc ->
      expr_runp a f vf ->
      valueToBool vc = false ->
      expr_runp a (Vternary c t f) vf.

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

(* TODO FIX Vvar case without default *)
Fixpoint expr_run (f : fext) (assoc : assoclist) (e : expr)
  {struct e} : res value :=
  match e with
  | Vlit v => OK v
  | Vvar r => handle_def (ZToValue 32 0) assoc!r
  | Vinputvar r => f r
  | Vbinop op l r =>
    let lv := expr_run f assoc l in
    let rv := expr_run f assoc r in
    let oper := binop_run op in
    do lv' <- lv;
    do rv' <- rv;
    handle_opt (msg "Verilog: sizes are not equal")
               (eq_to_opt lv' rv' (oper lv' rv'))
  | Vunop op e =>
    let oper := unop_run op in
    do ev <- expr_run f assoc e;
    OK (oper ev)
  | Vternary c te fe =>
    do cv <- expr_run f assoc c;
    if valueToBool cv then expr_run f assoc te else expr_run f assoc fe
  end.

(** Return the name of the lhs of an assignment. For now, this function is quite
simple because only assignment to normal variables is supported and needed. *)

Definition assign_name (e : expr) : res reg :=
  match e with
  | Vvar r => OK r
  | _ => Error (msg "Verilog: expression not supported on lhs of assignment")
  end.

Fixpoint find_case_stmnt (f : fext) (a : assoclist) (v : value) (cl : list (expr * stmnt))
         {struct cl} : option (res stmnt) :=
  match cl with
  | (e, s)::xs =>
    match expr_run f a e with
    | OK v' =>
      match eq_to_opt v v' (veq v v') with
      | Some eq => if valueToBool eq then Some (OK s) else find_case_stmnt f a v xs
      | None => Some (Error (msg "Verilog: equality check sizes not equal"))
      end
    | Error msg => Some (Error msg)
    end
  | _ => None
  end.

Fixpoint stmnt_run' (f : fext) (n : nat) (s : state) (st : stmnt) {struct n} : res state :=
  match n with
  | S n' =>
    match st with
    | Vskip => OK s
    | Vseq s1 s2 =>
      do s' <- stmnt_run' f n' s s1;
      stmnt_run' f n' s' s2
    | Vcond c st sf =>
      match s with
      | State assoc _ =>
        do cv <- expr_run f assoc c;
        if valueToBool cv
        then stmnt_run' f n' s st
        else stmnt_run' f n' s sf
      | _ => Error (msg "Verilog: stmnt execution in wrong state")
      end
    | Vcase e cl defst =>
      match s with
      | State a _ =>
        do v <- expr_run f a e;
        match find_case_stmnt f a v cl with
        | Some (OK st') => stmnt_run' f n' s st'
        | Some (Error msg) => Error msg
        | None => do s' <- handle_opt (msg "Verilog: no case was matched")
                                      (option_map (stmnt_run' f n' s) defst); s'
        end
      | _ => Error (msg "Verilog: stmnt execution in wrong state")
      end
    | Vblock lhs rhs =>
      match s with
      | State assoc nbassoc =>
        do name <- assign_name lhs;
        do rhse <- expr_run f assoc rhs;
        OK (State (PositiveMap.add name rhse assoc) nbassoc)
      | _ => Error (msg "Verilog: stmnt exectution in wrong state")
      end
    | Vnonblock lhs rhs =>
      match s with
      | State assoc nbassoc =>
        do name <- assign_name lhs;
        do rhse <- expr_run f assoc rhs;
        OK (State assoc (PositiveMap.add name rhse nbassoc))
      | _ => Error (msg "Verilog: stmnt execution in wrong state")
      end
    end
  | _ => OK s
  end.

Fixpoint stmnt_height (st : stmnt) {struct st} : nat :=
  match st with
  | Vskip => 1
  | Vseq s1 s2 => stmnt_height s1 + stmnt_height s2
  | Vcond _ s1 s2 => Nat.max (stmnt_height s1) (stmnt_height s2)
  | Vcase _ ls (Some st) =>
    fold_right (fun t acc => Nat.max acc (stmnt_height (snd t))) 0%nat ls
  | _ => 1
  end.

Definition stmnt_run (f : fext) (s : state) (st : stmnt) : res state :=
  stmnt_run' f (stmnt_height st) s st.

Fixpoint mi_step (f : fext) (s : state) (m : list module_item) {struct m} : res state :=
  let run := fun st ls =>
              do s' <- stmnt_run f s st;
              mi_step f s' ls
  in
  match m with
  | (Valways _ st)::ls => run st ls
  | (Valways_ff _ st)::ls => run st ls
  | (Valways_comb _ st)::ls => run st ls
  | (Vdecl _ _)::ls => mi_step f s ls
  | nil => OK s
  end.

Definition add_assoclist (r : reg) (v : value) (assoc : assoclist) : assoclist :=
  PositiveMap.add r v assoc.

Definition merge_assoclist (nbassoc assoc : assoclist) : assoclist :=
  PositiveMap.fold add_assoclist nbassoc assoc.

Definition empty_assoclist : assoclist := PositiveMap.empty value.

Definition mi_step_commit (f : fext) (assoc : assoclist) (m : list module_item) : res assoclist :=
  match mi_step f (State assoc empty_assoclist) m with
  | OK (State assoc' nbassoc) =>
    OK (merge_assoclist nbassoc assoc')
  | Error msg => Error msg
  | _ => Error (msg "Returned in the wrong state")
  end.

Fixpoint mi_run (f : fextclk) (assoc : assoclist) (m : list module_item) (n : nat) 
         {struct n} : res assoclist :=
  match n with
  | S n' =>
    do assoc' <- mi_step_commit (f n') assoc m;
    mi_run f assoc' m n'
  | O => OK assoc
  end.

Definition module_run (n : nat) (m : module) : res assoclist :=
  let f :=
      fun n =>
      match n with
      | 1%nat => fun r => if Pos.eqb r (fst (mod_reset m)) then OK (natToValue 1 1) else Error (msg "")
      | _ => fun r => if Pos.eqb r (fst (mod_reset m)) then OK (natToValue 1 0) else Error (msg "")
      end in
  mi_run f empty_assoclist (mod_body m) n.

Local Close Scope error_monad_scope.

Theorem value_eq_size_if_eq:
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
