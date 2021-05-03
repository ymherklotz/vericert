(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

Set Implicit Arguments.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.

Require compcert.common.Events.
Require Import compcert.lib.Integers.
Require Import compcert.common.Errors.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Globalenvs.

Require Import vericert.common.Vericertlib.
Require Import vericert.common.Show.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.

Import ListNotations.

Local Open Scope assocmap.

Definition reg : Type := positive.
Definition node : Type := positive.
Definition szreg : Type := reg * nat.

Record associations (A : Type) : Type :=
  mkassociations {
    assoc_blocking : AssocMap.t A;
    assoc_nonblocking : AssocMap.t A
  }.

Definition arr := (Array (option value)).

Definition reg_associations := associations value.
Definition arr_associations := associations arr.

Definition assocmap_reg := AssocMap.t value.
Definition assocmap_arr := AssocMap.t arr.

Definition merge_regs (new : assocmap_reg) (old : assocmap_reg) : assocmap_reg :=
  AssocMapExt.merge value new old.

Definition merge_cell (new : option value) (old : option value) : option value :=
  match new, old with
  | Some _, _ => new
  | _, _ => old
  end.

Definition merge_arr (new : option arr) (old : option arr) : option arr :=
  match new, old with
  | Some new', Some old' => Some (combine merge_cell new' old')
  | Some new', None => Some new'
  | None, Some old' => Some old'
  | None, None => None
  end.

Definition merge_arrs (new : assocmap_arr) (old : assocmap_arr) : assocmap_arr :=
  AssocMap.combine merge_arr new old.

Lemma merge_arr_empty':
  forall l,
  merge_arr (Some (arr_repeat None (length l))) (Some (make_array l)) = Some (make_array l).
Proof.
  induction l; auto.
  unfold merge_arr.
  unfold combine, make_array. simplify. rewrite H0.
  rewrite list_repeat_cons. simplify.
  rewrite H0; auto.
Qed.

Lemma merge_arr_empty:
  forall v l,
  v = Some (make_array l) ->
  merge_arr (Some (arr_repeat None (length l))) v = v.
Proof. intros. rewrite H. apply merge_arr_empty'. Qed.

Lemma merge_arr_empty2:
  forall v l v',
  v = Some v' ->
  l = arr_length v' ->
  merge_arr (Some (arr_repeat None l)) v = v.
Proof.
  intros. subst. destruct v'. simplify.
  generalize dependent arr_wf. generalize dependent arr_length.
  induction arr_contents.
  - simplify; subst; auto.
  - unfold combine, make_array in *; simplify; subst.
    rewrite list_repeat_cons; simplify.
    specialize (IHarr_contents (Datatypes.length arr_contents) eq_refl).
    inv IHarr_contents. rewrite H0. rewrite H0. auto.
Qed.

Definition arr_assocmap_lookup (a : assocmap_arr) (r : reg) (i : nat) : option value :=
  match a ! r with
  | None => None
  | Some arr => Some (Option.default (NToValue 0) (Option.join (array_get_error i arr)))
  end.

Definition arr_assocmap_set (r : reg) (i : nat) (v : value) (a : assocmap_arr) : assocmap_arr :=
  match a ! r with
  | None => a
  | Some arr => a # r <- (array_set i (Some v) arr)
  end.

Definition block_arr (r : reg) (i : nat) (asa : arr_associations) (v : value) : arr_associations :=
  mkassociations (arr_assocmap_set r i v asa.(assoc_blocking)) asa.(assoc_nonblocking).

Definition nonblock_arr (r : reg) (i : nat) (asa : arr_associations) (v : value) : arr_associations :=
  mkassociations asa.(assoc_blocking) (arr_assocmap_set r i v asa.(assoc_nonblocking)).

Definition block_reg (r : reg) (asr : reg_associations) (v : value) :=
  mkassociations (AssocMap.set r v asr.(assoc_blocking)) asr.(assoc_nonblocking).

Definition nonblock_reg (r : reg) (asr : reg_associations) (v : value) :=
  mkassociations asr.(assoc_blocking) (AssocMap.set r v asr.(assoc_nonblocking)).

Inductive scl_decl : Type := VScalar (sz : nat).
Inductive arr_decl : Type := VArray (sz : nat) (ln : nat).

(** * Verilog AST

The Verilog AST is defined here, which is the target language of the
compilation.

** Value

The Verilog [value] is a bitvector containg a size and the actual bitvector. In
this case, the [Word.word] type is used as many theorems about that bitvector
have already been proven. *)

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
| Vshr : binop (** shift right ([>>>]) *)
| Vshru : binop. (** shift right unsigned ([>>]) *)
(*| Vror : binop (** shift right unsigned ([>>]) *)*)

(** ** Unary Operators *)

Inductive unop : Type :=
| Vneg  (** negation ([-]) *)
| Vnot. (** not operation [!] *)

(** ** Expressions *)

Inductive expr : Type :=
| Vlit : value -> expr
| Vvar : reg -> expr
| Vvari : reg -> expr -> expr
| Vrange : reg -> expr -> expr -> expr
| Vinputvar : reg -> expr
| Vbinop : binop -> expr -> expr -> expr
| Vunop : unop -> expr -> expr
| Vternary : expr -> expr -> expr -> expr.

Definition posToExpr (p : positive) : expr :=
  Vlit (posToValue p).

(** ** Statements *)

Inductive stmnt : Type :=
| Vskip : stmnt
| Vseq : stmnt -> stmnt -> stmnt
| Vcond : expr -> stmnt -> stmnt -> stmnt
| Vcase : expr -> stmnt_expr_list -> option stmnt -> stmnt
| Vblock : expr -> expr -> stmnt
| Vnonblock : expr -> expr -> stmnt
with stmnt_expr_list : Type :=
| Stmntnil : stmnt_expr_list
| Stmntcons : expr -> stmnt -> stmnt_expr_list -> stmnt_expr_list.

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

Inductive io : Type :=
| Vinput : io
| Voutput : io
| Vinout : io.

Inductive declaration : Type :=
| Vdecl : option io -> reg -> nat -> declaration
| Vdeclarr : option io -> reg -> nat -> nat -> declaration.

Inductive module_item : Type :=
| Vdeclaration : declaration -> module_item
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


Record div := mk_div {
    div_a: reg;
    div_b: reg;
    div_q: reg;
    div_r: reg;
    div_u_en: reg;
    div_en: reg;
    div_done: reg;
    div_ordering: (div_a < div_b < div_q
                   /\ div_q < div_r < div_u_en
                   /\ div_u_en < div_en < div_done)%positive
  }.

Record module : Type := mkmodule {
  mod_start : reg;
  mod_reset : reg;
  mod_clk : reg;
  mod_finish : reg;
  mod_return : reg;
  mod_st : reg; (**r Variable that defines the current state, it should be internal. *)
  mod_stk : reg;
  mod_stk_len : nat;
  mod_args : list reg;
  mod_body : list module_item;
  mod_entrypoint : node;
  mod_div : option div;
}.

Definition fundef := AST.fundef module.

Definition program := AST.program fundef unit.

(** Convert a [positive] to an expression directly, setting it to the right
    size. *)
Definition posToLit (p : positive) : expr :=
  Vlit (posToValue p).

Definition fext := unit.
Definition fextclk := nat -> fext.

(** ** State

The [state] contains the following items:
n
- Current [module] that is being worked on, so that the state variable can be
retrieved and set appropriately.
- Current [module_item] which is being worked on.
- A contiunation ([cont]) which defines what to do next.  The option is to
  either evaluate another module item or go to the next clock cycle.  Finally
  it could also end if the finish flag of the module goes high.
- Association list containing the blocking assignments made, or assignments made
  in previous clock cycles.
- Nonblocking association list containing all the nonblocking assignments made
  in the current module.
- The environment containing values for the input.
- The program counter which determines the value for the state in this version of
  Verilog, as the Verilog was generated by the RTL, which means that we have to
  make an assumption about how it looks.  In this case, that it contains state
  which determines which part of the Verilog is executed.  This is then the part
  of the Verilog that should match with the RTL. *)

Inductive stackframe : Type :=
  Stackframe :
    forall  (res : reg)
            (m : module)
            (pc : node)
            (reg_assoc : assocmap_reg)
            (arr_assoc : assocmap_arr),
      stackframe.

Inductive state : Type :=
| State :
    forall (stack : list stackframe)
           (m : module)
           (st : node)
           (reg_assoc : assocmap_reg)
           (arr_assoc : assocmap_arr), state
| Returnstate :
    forall (res : list stackframe)
           (v : value), state
| Callstate :
    forall (stack : list stackframe)
           (m : module)
           (args : list value), state.

Definition binop_run (op : binop) (v1 v2 : value) : option value :=
  match op with
  | Vadd => Some (Int.add v1 v2)
  | Vsub => Some (Int.sub v1 v2)
  | Vmul => Some (Int.mul v1 v2)
  | Vdiv => if Int.eq v2 Int.zero
               || Int.eq v1 (Int.repr Int.min_signed) && Int.eq v2 Int.mone
            then None
            else Some (Int.divs v1 v2)
  | Vdivu => if Int.eq v2 Int.zero then None else Some (Int.divu v1 v2)
  | Vmod => if Int.eq v2 Int.zero
               || Int.eq v1 (Int.repr Int.min_signed) && Int.eq v2 Int.mone
            then None
            else Some (Int.mods v1 v2)
  | Vmodu => if Int.eq v2 Int.zero then None else Some (Int.modu v1 v2)
  | Vlt => Some (boolToValue (Int.lt v1 v2))
  | Vltu => Some (boolToValue (Int.ltu v1 v2))
  | Vgt => Some (boolToValue (Int.lt v2 v1))
  | Vgtu => Some (boolToValue (Int.ltu v2 v1))
  | Vle => Some (boolToValue (negb (Int.lt v2 v1)))
  | Vleu => Some (boolToValue (negb (Int.ltu v2 v1)))
  | Vge => Some (boolToValue (negb (Int.lt v1 v2)))
  | Vgeu => Some (boolToValue (negb (Int.ltu v1 v2)))
  | Veq => Some (boolToValue (Int.eq v1 v2))
  | Vne => Some (boolToValue (negb (Int.eq v1 v2)))
  | Vand => Some (Int.and v1 v2)
  | Vor => Some (Int.or v1 v2)
  | Vxor => Some (Int.xor v1 v2)
  | Vshl => Some (Int.shl v1 v2)
  | Vshr => Some (Int.shr v1 v2)
  | Vshru => Some (Int.shru v1 v2)
  end.

Definition unop_run (op : unop) (v1 : value) : value :=
  match op with
  | Vneg => Int.neg v1
  | Vnot => Int.not v1
  end.

Inductive expr_runp : fext -> assocmap -> assocmap_arr -> expr -> value -> Prop :=
  | erun_Vlit :
      forall fext reg stack v,
      expr_runp fext reg stack (Vlit v) v
  | erun_Vvar :
      forall fext reg stack v r,
      reg#r = v ->
      expr_runp fext reg stack (Vvar r) v
  | erun_Vvari :
      forall fext reg stack v iexp i r,
      expr_runp fext reg stack iexp i ->
      arr_assocmap_lookup stack r (valueToNat i) = Some v ->
      expr_runp fext reg stack (Vvari r iexp) v
  | erun_Vbinop :
      forall fext reg stack op l r lv rv resv,
      expr_runp fext reg stack l lv ->
      expr_runp fext reg stack r rv ->
      Some resv = binop_run op lv rv ->
      expr_runp fext reg stack (Vbinop op l r) resv
  | erun_Vunop :
      forall fext reg stack u vu op oper resv,
      expr_runp fext reg stack u vu ->
      oper = unop_run op ->
      resv = oper vu ->
      expr_runp fext reg stack (Vunop op u) resv
  | erun_Vternary_true :
      forall fext reg stack c ts fs vc vt,
      expr_runp fext reg stack c vc ->
      expr_runp fext reg stack ts vt ->
      valueToBool vc = true ->
      expr_runp fext reg stack (Vternary c ts fs) vt
  | erun_Vternary_false :
      forall fext reg stack c ts fs vc vf,
      expr_runp fext reg stack c vc ->
      expr_runp fext reg stack fs vf ->
      valueToBool vc = false ->
      expr_runp fext reg stack (Vternary c ts fs) vf.
Hint Constructors expr_runp : verilog.

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

(** Return the location of the lhs of an assignment. *)

Inductive location : Type :=
| LocReg (_ : reg)
| LocArray (_ : reg) (_ : nat).

Inductive location_is : fext -> assocmap -> assocmap_arr -> expr -> location -> Prop :=
| Base : forall f asr asa r, location_is f asr asa (Vvar r) (LocReg r)
| Indexed : forall f asr asa r iexp iv,
  expr_runp f asr asa iexp iv ->
  location_is f asr asa (Vvari r iexp) (LocArray r (valueToNat iv)).

Inductive stmnt_runp: fext -> reg_associations -> arr_associations ->
                      stmnt -> reg_associations -> arr_associations -> Prop :=
| stmnt_runp_Vskip:
    forall f ar al, stmnt_runp f ar al Vskip ar al
| stmnt_runp_Vseq:
    forall f st1 st2 asr0 asa0 asr1 asa1 asr2 asa2,
    stmnt_runp f asr0 asa0 st1 asr1 asa1 ->
    stmnt_runp f asr1 asa1 st2 asr2 asa2 ->
    stmnt_runp f asr0 asa0 (Vseq st1 st2) asr2 asa2
| stmnt_runp_Vcond_true:
    forall asr0 asa0 asr1 asa1 f c vc stt stf,
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) c vc ->
    valueToBool vc = true ->
    stmnt_runp f asr0 asa0 stt asr1 asa1 ->
    stmnt_runp f asr0 asa0 (Vcond c stt stf) asr1 asa1
| stmnt_runp_Vcond_false:
    forall asr0 asa0 asr1 asa1 f c vc stt stf,
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) c vc ->
    valueToBool vc = false ->
    stmnt_runp f asr0 asa0 stf asr1 asa1 ->
    stmnt_runp f asr0 asa0 (Vcond c stt stf) asr1 asa1
| stmnt_runp_Vcase_nomatch:
    forall e ve asr0 asa0 f asr1 asa1 me mve sc cs def,
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) e ve ->
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) me mve ->
    mve <> ve ->
    stmnt_runp f asr0 asa0 (Vcase e cs def) asr1 asa1 ->
    stmnt_runp f asr0 asa0 (Vcase e (Stmntcons me sc cs) def) asr1 asa1
| stmnt_runp_Vcase_match:
    forall e ve asr0 asa0 f asr1 asa1 me mve sc cs def,
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) e ve ->
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) me mve ->
    mve = ve ->
    stmnt_runp f asr0 asa0 sc asr1 asa1 ->
    stmnt_runp f asr0 asa0 (Vcase e (Stmntcons me sc cs) def) asr1 asa1
| stmnt_runp_Vcase_default:
    forall asr0 asa0 asr1 asa1 f st e ve,
    expr_runp f asr0.(assoc_blocking) asa0.(assoc_blocking) e ve ->
    stmnt_runp f asr0 asa0 st asr1 asa1 ->
    stmnt_runp f asr0 asa0 (Vcase e Stmntnil (Some st)) asr1 asa1
| stmnt_runp_Vblock_reg:
    forall lhs r rhs rhsval asr asa f,
    location_is f asr.(assoc_blocking) asa.(assoc_blocking) lhs (LocReg r) ->
    expr_runp f asr.(assoc_blocking) asa.(assoc_blocking) rhs rhsval ->
    stmnt_runp f asr asa
                 (Vblock lhs rhs)
                 (block_reg r asr rhsval) asa
| stmnt_runp_Vnonblock_reg:
    forall lhs r rhs rhsval asr asa f,
    location_is f asr.(assoc_blocking) asa.(assoc_blocking) lhs (LocReg r) ->
    expr_runp f asr.(assoc_blocking) asa.(assoc_blocking) rhs rhsval ->
    stmnt_runp f asr asa
                 (Vnonblock lhs rhs)
                 (nonblock_reg r asr rhsval) asa
| stmnt_runp_Vblock_arr:
    forall lhs r i rhs rhsval asr asa f,
    location_is f asr.(assoc_blocking) asa.(assoc_blocking) lhs (LocArray r i) ->
    expr_runp f asr.(assoc_blocking) asa.(assoc_blocking) rhs rhsval ->
    stmnt_runp f asr asa
                 (Vblock lhs rhs)
                 asr (block_arr r i asa rhsval)
| stmnt_runp_Vnonblock_arr:
    forall lhs r i rhs rhsval asr asa f,
    location_is f asr.(assoc_blocking) asa.(assoc_blocking) lhs (LocArray r i) ->
    expr_runp f asr.(assoc_blocking) asa.(assoc_blocking) rhs rhsval ->
    stmnt_runp f asr asa
                 (Vnonblock lhs rhs)
                 asr (nonblock_arr r i asa rhsval).
Hint Constructors stmnt_runp : verilog.

Inductive mi_stepp : fext -> reg_associations -> arr_associations ->
                     module_item -> reg_associations -> arr_associations -> Prop :=
| mi_stepp_Valways :
    forall f sr0 sa0 st sr1 sa1 c,
    stmnt_runp f sr0 sa0 st sr1 sa1 ->
    mi_stepp f sr0 sa0 (Valways (Vposedge c) st) sr1 sa1
| mi_stepp_Valways_ne :
    forall f sr0 sa0 c st,
    mi_stepp f sr0 sa0 (Valways (Vnegedge c) st) sr0 sa0
| mi_stepp_Vdecl :
    forall f sr0 sa0 d,
    mi_stepp f sr0 sa0 (Vdeclaration d) sr0 sa0.
Hint Constructors mi_stepp : verilog.

Inductive mi_stepp_negedge : fext -> reg_associations -> arr_associations ->
                             module_item -> reg_associations -> arr_associations -> Prop :=
| mi_stepp_negedge_Valways :
    forall f sr0 sa0 st sr1 sa1 c,
    stmnt_runp f sr0 sa0 st sr1 sa1 ->
    mi_stepp_negedge f sr0 sa0 (Valways (Vnegedge c) st) sr1 sa1
| mi_stepp_negedge_Valways_ne :
    forall f sr0 sa0 c st,
    mi_stepp_negedge f sr0 sa0 (Valways (Vposedge c) st) sr0 sa0
| mi_stepp_negedge_Vdecl :
    forall f sr0 sa0 d,
    mi_stepp_negedge f sr0 sa0 (Vdeclaration d) sr0 sa0.
Hint Constructors mi_stepp : verilog.

Inductive mis_stepp : fext -> reg_associations -> arr_associations ->
                      list module_item -> reg_associations -> arr_associations -> Prop :=
| mis_stepp_Cons :
    forall f mi mis sr0 sa0 sr1 sa1 sr2 sa2,
    mi_stepp f sr0 sa0 mi sr1 sa1 ->
    mis_stepp f sr1 sa1 mis sr2 sa2 ->
    mis_stepp f sr0 sa0 (mi :: mis) sr2 sa2
| mis_stepp_Nil :
    forall f sr sa,
    mis_stepp f sr sa nil sr sa.
Hint Constructors mis_stepp : verilog.

Inductive mis_stepp_negedge : fext -> reg_associations -> arr_associations ->
                      list module_item -> reg_associations -> arr_associations -> Prop :=
| mis_stepp_negedge_Cons :
    forall f mi mis sr0 sa0 sr1 sa1 sr2 sa2,
    mi_stepp_negedge f sr0 sa0 mi sr1 sa1 ->
    mis_stepp_negedge f sr1 sa1 mis sr2 sa2 ->
    mis_stepp_negedge f sr0 sa0 (mi :: mis) sr2 sa2
| mis_stepp_negedge_Nil :
    forall f sr sa,
    mis_stepp_negedge f sr sa nil sr sa.
Hint Constructors mis_stepp : verilog.

Local Close Scope error_monad_scope.

Fixpoint init_params (vl : list value) (rl : list reg) {struct rl} :=
  match rl, vl with
  | r :: rl', v :: vl' => AssocMap.set r v (init_params vl' rl')
  | _, _ => empty_assocmap
  end.

Definition genv := Globalenvs.Genv.t fundef unit.
Definition empty_stack (m : module) : assocmap_arr :=
  (AssocMap.set m.(mod_stk) (Array.arr_repeat None m.(mod_stk_len)) (AssocMap.empty arr)).

Inductive exec_div :
  Verilog.reg_associations -> option div -> Verilog.reg_associations -> Prop :=
| exec_div_Some_idle:
    forall r d,
      Int.eq (Verilog.assoc_blocking r)#(div_en d, 32)
             (Verilog.assoc_blocking r)#(div_u_en d, 32) = true ->
      Int.eq ((Verilog.assoc_blocking r)#(div_done d, 32)) (ZToValue 0) = true ->
      exec_div r (Some d) r
| exec_div_Some_input:
    forall r d u_en en don,
      Int.eq en u_en = false ->
      Int.eq don (ZToValue 0) = true ->
      (Verilog.assoc_blocking r)#(div_done d, 32) = don ->
      (Verilog.assoc_blocking r)#(div_en d, 32) = en ->
      (Verilog.assoc_blocking r)!(div_u_en d) = Some u_en ->
      exec_div r (Some d) (Verilog.nonblock_reg (div_en d)
                             (Verilog.nonblock_reg (div_done d) r (ZToValue 1)) u_en)
| exec_div_Some_output:
    forall r d don a b,
      Int.eq don (ZToValue 0) = false ->
      (Verilog.assoc_blocking r)#(div_done d, 32) = don ->
      (Verilog.assoc_blocking r)!(div_a d) = Some a ->
      (Verilog.assoc_blocking r)!(div_b d) = Some b ->
      exec_div r (Some d) (Verilog.nonblock_reg (div_done d)
                             (Verilog.nonblock_reg (div_r d)
                                (Verilog.nonblock_reg (div_q d) r (Int.divs a b)) (Int.mods a b))
                             (ZToValue 0))
| exec_div_None: forall r, exec_div r None r.

Inductive step : genv -> state -> Events.trace -> state -> Prop :=
  | step_module :
      forall asr asa asr' asa' basr1 nasr1 basr1' nasr1' basa1
             nasa1 basr2 nasr2 basa2 nasa2 f stval pstval m sf st g ist,
      asr!(m.(mod_reset)) = Some (ZToValue 0) ->
      asr!(m.(mod_finish)) = Some (ZToValue 0) ->
      asr!(m.(mod_st)) = Some ist ->
      valueToPos ist = st ->
      mis_stepp f (mkassociations asr empty_assocmap)
                  (mkassociations asa (empty_stack m))
                  (mod_body m)
                  (mkassociations basr1 nasr1)
                  (mkassociations basa1 nasa1) ->
      exec_div (mkassociations basr1 nasr1) (mod_div m) (mkassociations basr1' nasr1') ->
      mis_stepp_negedge f (mkassociations (merge_regs nasr1' basr1') empty_assocmap)
                        (mkassociations (merge_arrs nasa1 basa1) (empty_stack m))
                        (mod_body m)
                        (mkassociations basr2 nasr2)
                        (mkassociations basa2 nasa2) ->
      asr' = merge_regs nasr2 basr2 ->
      asa' = merge_arrs nasa2 basa2 ->
      asr'!(m.(mod_st)) = Some stval ->
      valueToPos stval = pstval ->
      step g (State sf m st asr asa) Events.E0 (State sf m pstval asr' asa')
| step_finish :
    forall asr asa sf retval m st g,
    asr!(m.(mod_finish)) = Some (ZToValue 1) ->
    asr!(m.(mod_return)) = Some retval ->
    step g (State sf m st asr asa) Events.E0 (Returnstate sf retval)
| step_call :
    forall g res m args,
    step g (Callstate res m args) Events.E0
         (State res m m.(mod_entrypoint)
          (AssocMap.set (mod_reset m) (ZToValue 0)
           (AssocMap.set (mod_finish m) (ZToValue 0)
            (AssocMap.set m.(mod_st) (posToValue m.(mod_entrypoint))
             (init_params args m.(mod_args)))))
          (empty_stack m))
| step_return :
    forall g m asr i r sf pc mst asa,
    mst = mod_st m ->
    step g (Returnstate (Stackframe r m pc asr asa :: sf) i) Events.E0
         (State sf m pc ((asr # mst <- (posToValue pc)) # r <- i) asa).
Hint Constructors step : verilog.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b m0 m,
      let ge := Globalenvs.Genv.globalenv p in
      Globalenvs.Genv.init_mem p = Some m0 ->
      Globalenvs.Genv.find_symbol ge p.(AST.prog_main) = Some b ->
      Globalenvs.Genv.find_funct_ptr ge b = Some (AST.Internal m) ->
      initial_state p (Callstate nil m nil).

Inductive final_state : state -> Integers.int -> Prop :=
| final_state_intro : forall retval retvali,
    retvali = valueToInt retval ->
    final_state (Returnstate nil retval) retvali.

Definition semantics (m : program) :=
  Smallstep.Semantics step (initial_state m) final_state
                      (Globalenvs.Genv.globalenv m).

Fixpoint list_to_stmnt st :=
  match st with
  | (e, s) :: r => Stmntcons e s (list_to_stmnt r)
  | nil => Stmntnil
  end.

Fixpoint stmnt_to_list st :=
  match st with
  | Stmntcons e s r => (e, s) :: stmnt_to_list r
  | Stmntnil => nil
  end.

Lemma expr_runp_determinate :
  forall f e asr asa v,
  expr_runp f asr asa e v ->
  forall v',
  expr_runp f asr asa e v' ->
  v' = v.
Proof.
  induction e; intros;

  repeat (try match goal with
              | [ H : expr_runp _ _ _ (Vlit _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vvar _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vvari _ _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vinputvar _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vbinop _ _ _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vunop _ _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vternary _ _ _) _ |- _ ] => invert H
              | [ H : expr_runp _ _ _ (Vrange _ _ _) _ |- _ ] => invert H

              | [ H1 : forall asr asa v, expr_runp _ asr asa ?e v -> _,
                  H2 : expr_runp _ _ _ ?e _ |- _ ] =>
                learn (H1 _ _ _ H2)
              | [ H1 : forall v, expr_runp _ ?asr ?asa ?e v -> _,
                  H2 : expr_runp _ ?asr ?asa ?e _ |- _ ] =>
                learn (H1 _ H2)
              end; crush).
Qed.
Hint Resolve expr_runp_determinate : verilog.

Lemma location_is_determinate :
  forall f asr asa e l,
  location_is f asr asa e l ->
  forall l',
  location_is f asr asa e l' ->
  l' = l.
Proof.
  induction 1; intros;

  repeat (try match goal with
              | [ H : location_is _ _ _ _ _ |- _ ] => invert H
              | [ H1 : expr_runp _ ?asr ?asa ?e _,
                  H2 : expr_runp _ ?asr ?asa ?e _ |- _ ] =>
                learn (expr_runp_determinate H1 H2)
              end; crush).
Qed.

Lemma stmnt_runp_determinate :
  forall f s asr0 asa0 asr1 asa1,
  stmnt_runp f asr0 asa0 s asr1 asa1 ->
  forall asr1' asa1',
  stmnt_runp f asr0 asa0 s asr1' asa1' ->
  asr1' = asr1 /\ asa1' = asa1.
  induction 1; intros;

  repeat (try match goal with
             | [ H : stmnt_runp _ _ _ (Vseq _ _) _ _ |- _ ] => invert H
             | [ H : stmnt_runp _ _ _ (Vnonblock _ _) _ _ |- _ ] => invert H
             | [ H : stmnt_runp _ _ _ (Vblock _ _) _ _ |- _ ] => invert H
             | [ H : stmnt_runp _ _ _ Vskip _ _ |- _ ] => invert H
             | [ H : stmnt_runp _ _ _ (Vcond _ _ _) _ _ |- _ ] => invert H
             | [ H : stmnt_runp _ _ _ (Vcase _ (Stmntcons _ _ _) _) _ _ |- _ ] => invert H
             | [ H : stmnt_runp _ _ _ (Vcase _ Stmntnil  _) _ _ |- _ ] => invert H

             | [ H1 : expr_runp _ ?asr ?asa ?e _,
                 H2 : expr_runp _ ?asr ?asa ?e _ |- _ ] =>
               learn (expr_runp_determinate H1 H2)

             | [ H1 : location_is _ ?asr ?asa ?e _,
                 H2 : location_is _ ?asr ?asa ?e _ |- _ ] =>
               learn (location_is_determinate H1 H2)

             | [ H1 : forall asr1 asa1, stmnt_runp _ ?asr0 ?asa0 ?s asr1 asa1 -> _,
                 H2 : stmnt_runp _ ?asr0 ?asa0 ?s _ _ |- _ ] =>
               learn (H1 _ _ H2)
              end; crush).
Qed.
Hint Resolve stmnt_runp_determinate : verilog.

Lemma mi_stepp_determinate :
  forall f asr0 asa0 m asr1 asa1,
  mi_stepp f asr0 asa0 m asr1 asa1 ->
  forall asr1' asa1',
  mi_stepp f asr0 asa0 m asr1' asa1' ->
  asr1' = asr1 /\ asa1' = asa1.
Proof.
  intros. destruct m; invert H; invert H0;

  repeat (try match goal with
              | [ H1 : stmnt_runp _ ?asr0 ?asa0 ?s _ _,
                  H2 : stmnt_runp _ ?asr0 ?asa0 ?s _ _ |- _ ] =>
                learn (stmnt_runp_determinate H1 H2)
              end; crush).
Qed.

Lemma mi_stepp_negedge_determinate :
  forall f asr0 asa0 m asr1 asa1,
  mi_stepp_negedge f asr0 asa0 m asr1 asa1 ->
  forall asr1' asa1',
  mi_stepp_negedge f asr0 asa0 m asr1' asa1' ->
  asr1' = asr1 /\ asa1' = asa1.
Proof.
  intros. destruct m; invert H; invert H0;

  repeat (try match goal with
              | [ H1 : stmnt_runp _ ?asr0 ?asa0 ?s _ _,
                  H2 : stmnt_runp _ ?asr0 ?asa0 ?s _ _ |- _ ] =>
                learn (stmnt_runp_determinate H1 H2)
              end; crush).
Qed.

Lemma mis_stepp_determinate :
  forall f asr0 asa0 m asr1 asa1,
  mis_stepp f asr0 asa0 m asr1 asa1 ->
  forall asr1' asa1',
  mis_stepp f asr0 asa0 m asr1' asa1' ->
  asr1' = asr1 /\ asa1' = asa1.
Proof.
  induction 1; intros;

  repeat (try match goal with
              | [ H : mis_stepp _ _ _ [] _ _ |- _ ] => invert H
              | [ H : mis_stepp _ _ _ ( _ :: _ ) _ _ |- _ ] => invert H

              | [ H1 : mi_stepp _ ?asr0 ?asa0 ?s _ _,
                  H2 : mi_stepp _ ?asr0 ?asa0 ?s _ _ |- _ ] =>
                learn (mi_stepp_determinate H1 H2)

             | [ H1 : forall asr1 asa1, mis_stepp _ ?asr0 ?asa0 ?m asr1 asa1 -> _,
                 H2 : mis_stepp _ ?asr0 ?asa0 ?m _ _ |- _ ] =>
               learn (H1 _ _ H2)
              end; crush).
Qed.

Lemma mis_stepp_negedge_determinate :
  forall f asr0 asa0 m asr1 asa1,
  mis_stepp_negedge f asr0 asa0 m asr1 asa1 ->
  forall asr1' asa1',
  mis_stepp_negedge f asr0 asa0 m asr1' asa1' ->
  asr1' = asr1 /\ asa1' = asa1.
Proof.
  induction 1; intros;

  repeat (try match goal with
              | [ H : mis_stepp_negedge _ _ _ [] _ _ |- _ ] => invert H
              | [ H : mis_stepp_negedge _ _ _ ( _ :: _ ) _ _ |- _ ] => invert H

              | [ H1 : mi_stepp_negedge _ ?asr0 ?asa0 ?s _ _,
                  H2 : mi_stepp_negedge _ ?asr0 ?asa0 ?s _ _ |- _ ] =>
                learn (mi_stepp_negedge_determinate H1 H2)

             | [ H1 : forall asr1 asa1, mis_stepp_negedge _ ?asr0 ?asa0 ?m asr1 asa1 -> _,
                 H2 : mis_stepp_negedge _ ?asr0 ?asa0 ?m _ _ |- _ ] =>
               learn (H1 _ _ H2)
              end; crush).
Qed.

Lemma exec_div_determinate :
  forall asr0 d asr1,
  exec_div asr0 d asr1 ->
  forall asr1',
  exec_div asr0 d asr1' ->
  asr1' = asr1.
Proof.
  induction 1; intros.
  - inv H1. auto. unfold find_assocmap, AssocMapExt.get_default in *.
    rewrite H8 in H. rewrite H3 in H. discriminate.
    unfold find_assocmap, AssocMapExt.get_default in *.
    rewrite H3 in H0. discriminate.
  - inv H4. unfold find_assocmap, AssocMapExt.get_default in *. rewrite H3 in H6.
    rewrite H6 in H. discriminate.
    rewrite H3 in H11. inv H11. auto.
    unfold find_assocmap, AssocMapExt.get_default in *.
    rewrite H6 in H0. discriminate.
  - inv H3. rewrite H7 in H. discriminate.
    rewrite H6 in H. discriminate.
    rewrite H7 in H1. rewrite H9 in H2. inv H1. inv H2. auto.
  - inv H. auto.
Qed.

Lemma semantics_determinate :
  forall (p: program), Smallstep.determinate (semantics p).
Proof.
  intros. constructor; set (ge := Globalenvs.Genv.globalenv p); simplify.
  - invert H; invert H0; constructor. (* Traces are always empty *)
  - invert H; invert H0; crush. assert (f = f0) by (destruct f; destruct f0; auto); subst.
    pose proof (mis_stepp_determinate H5 H16). simplify. inv H0. inv H4.
    pose proof (exec_div_determinate H6 H17). simplify. inv H.
    pose proof (mis_stepp_negedge_determinate H7 H19).
    crush.
  - constructor. invert H; crush.
  - invert H; invert H0; unfold ge0, ge1 in *; crush.
  - red; simplify; intro; invert H0; invert H; crush.
  - invert H; invert H0; crush.
Qed.

Local Open Scope positive.

Fixpoint max_reg_expr (e: expr) :=
  match e with
  | Vlit _ => 1
  | Vvar r => r
  | Vvari r e => Pos.max r (max_reg_expr e)
  | Vrange r e1 e2 => Pos.max r (Pos.max (max_reg_expr e1) (max_reg_expr e2))
  | Vinputvar r => r
  | Vbinop _ e1 e2 => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  | Vunop _ e => max_reg_expr e
  | Vternary e1 e2 e3 => Pos.max (max_reg_expr e1) (Pos.max (max_reg_expr e2) (max_reg_expr e3))
  end.

Fixpoint max_reg_stmnt (st: stmnt) :=
  match st with
  | Vskip => 1
  | Vseq s1 s2 => Pos.max (max_reg_stmnt s1) (max_reg_stmnt s2)
  | Vcond e s1 s2 =>
    Pos.max (max_reg_expr e)
            (Pos.max (max_reg_stmnt s1) (max_reg_stmnt s2))
  | Vcase e stl None => Pos.max (max_reg_expr e) (max_reg_stmnt_expr_list stl)
  | Vcase e stl (Some s) =>
    Pos.max (max_reg_stmnt s)
            (Pos.max (max_reg_expr e) (max_reg_stmnt_expr_list stl))
  | Vblock e1 e2 => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  | Vnonblock e1 e2 => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  end
with max_reg_stmnt_expr_list (stl: stmnt_expr_list) :=
  match stl with
  | Stmntnil => 1
  | Stmntcons e s stl' =>
    Pos.max (max_reg_expr e)
            (Pos.max (max_reg_stmnt s)
                     (max_reg_stmnt_expr_list stl'))
  end.
