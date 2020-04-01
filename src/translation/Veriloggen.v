(*
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

From coqup Require Import Verilog Coquplib.

From compcert Require Errors Op AST Integers Maps.
From compcert Require Import RTL.

Definition node : Type := positive.
Definition reg : Type := positive.
Definition ident : Type := positive.

Inductive statetrans : Type :=
| StateGoto (p : node)
| StateCond (c : expr) (t f : node).

Record state: Type := mkstate {
  st_freshreg : reg;
  st_freshstate : node;
  st_stm : PositiveMap.t stmnt;
  st_statetrans : PositiveMap.t statetrans;
  st_decl : list (reg * nat);
  st_fin : option reg;
  st_ret : option reg;
}.

(** Map from initial register allocations to new allocations. *)
Definition mapping: Type := PositiveMap.t reg.

Definition init_state : state :=
  mkstate 1%positive
          1%positive
          (PositiveMap.empty stmnt)
          (PositiveMap.empty statetrans)
          nil
          None
          None.

Inductive res (A: Type) (s: state): Type :=
| Error : Errors.errmsg -> res A s
| OK : A -> forall (_ : state), res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s : state) => OK x s.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s : state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' =>
      match g a s' with
      | Error msg => Error msg
      | OK b s'' => OK b s''
      end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
(at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
(at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  fun (s : state) =>
    match f s with
    | OK a s' => OK a s'
    | Error _ => g s
    end.

Definition error {A: Type} (err: Errors.errmsg) : mon A := fun (s: state) => Error err.

Definition get : mon state := fun s => OK s s.

Definition set (s: state) : mon unit := fun _ => OK tt s.

Definition run_mon {A: Type} (s: state) (m: mon A): Errors.res A :=
    match m s with
    | OK a s' => Errors.OK a
    | Error err => Errors.Error err
    end.

Definition map_state (f: state -> state): mon state :=
  fun s => let s' := f s in OK s' s'.

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

Definition bop (op : binop) (r1 r2 : reg) : option expr :=
  Some (Vbinop op (Vvar r1) (Vvar r2)).

Definition boplit (op : binop) (r : reg) (l : Integers.int) : option expr :=
  Some (Vbinop op (Vvar r) (Vlit (intToValue l))).

Definition translate_comparison (c : Integers.comparison) (args : list reg) : option expr :=
  match c, args with
  | Integers.Ceq, r1::r2::nil => bop Veq r1 r2
  | Integers.Cne, r1::r2::nil => bop Vne r1 r2
  | Integers.Clt, r1::r2::nil => bop Vlt r1 r2
  | Integers.Cgt, r1::r2::nil => bop Vgt r1 r2
  | Integers.Cle, r1::r2::nil => bop Vle r1 r2
  | Integers.Cge, r1::r2::nil => bop Vge r1 r2
  | _, _ => None
  end.

Definition translate_condition (c : Op.condition) (args : list reg) : option expr :=
  match c, args with
  | Op.Ccomp c, _ => translate_comparison c args
  | Op.Ccompu c, _ => None
  | Op.Ccompimm c i, _ => None
  | Op.Ccompuimm c i, _ => None
  | Op.Cmaskzero n, _ => None
  | Op.Cmasknotzero n, _ => None
  | _, _ => None
  end.

(** Translate an instruction to a statement. *)
Definition translate_instr (op : Op.operation) (args : list reg) : option expr :=
  match op, args with
  | Op.Omove, r::nil => Some (Vvar r)
  | Op.Ointconst n, _ => Some (Vlit (intToValue n))
  | Op.Oneg, r::nil => Some (Vunop Vneg (Vvar r))
  | Op.Osub, r1::r2::nil => bop Vsub r1 r2
  | Op.Omul, r1::r2::nil => bop Vmul r1 r2
  | Op.Omulimm n, r::nil => boplit Vmul r n
  | Op.Omulhs, _ => None
  | Op.Omulhu, _ => None
  | Op.Odiv, r1::r2::nil => bop Vdiv r1 r2
  | Op.Odivu, r1::r2::nil => bop Vdivu r1 r2
  | Op.Omod, r1::r2::nil => bop Vmod r1 r2
  | Op.Omodu, r1::r2::nil => bop Vmodu r1 r2
  | Op.Oand, r1::r2::nil => bop Vand r1 r2
  | Op.Oandimm n, r::nil => boplit Vand r n
  | Op.Oor, r1::r2::nil => bop Vor r1 r2
  | Op.Oorimm n, r::nil => boplit Vor r n
  | Op.Oxor, r1::r2::nil => bop Vxor r1 r2
  | Op.Oxorimm n, r::nil => boplit Vxor r n
  | Op.Onot, r::nil => Some (Vunop Vnot (Vvar r))
  | Op.Oshl, r1::r2::nil => bop Vshl r1 r2
  | Op.Oshlimm n, r::nil => boplit Vshl r n
  | Op.Oshr, r1::r2::nil => bop Vshr r1 r2
  | Op.Oshrimm n, r::nil => boplit Vshr r n
  | Op.Oshrximm n, r::nil => None
  | Op.Oshru, r1::r2::nil => None
  | Op.Oshruimm n, r::nil => None
  | Op.Ororimm n, r::nil => None
  | Op.Oshldimm n, r::nil => None
  | Op.Ocmp c, _ => translate_condition c args
  | _, _ => None
  end.

Definition add_instr (n : node) (n' : node) (st : stmnt) : mon node :=
  fun s =>
    OK n' (mkstate s.(st_freshreg)
                   (Pos.max (Pos.succ n) s.(st_freshstate))
                   (PositiveMap.add n st s.(st_stm))
                   (PositiveMap.add n (StateGoto n') s.(st_statetrans))
                   s.(st_decl)
                   s.(st_fin)
                   s.(st_ret)).

Definition add_reg (r: reg) (s: state) : state :=
  mkstate (Pos.max (Pos.succ r) s.(st_freshreg))
          s.(st_freshstate)
          s.(st_stm)
          s.(st_statetrans)
          ((r, 32%nat) :: s.(st_decl))
          s.(st_fin)
          s.(st_ret).

Definition add_instr_reg (r: reg) (n: node) (n': node) (st: stmnt) : mon node :=
  do _ <- map_state (add_reg r);
  add_instr n n' st.

Definition decl_fresh_reg (sz : nat) : mon reg :=
  fun s =>
    let r := s.(st_freshreg) in
    OK r (mkstate
         (Pos.succ r)
         s.(st_freshstate)
         s.(st_stm)
         s.(st_statetrans)
         ((r, sz) :: s.(st_decl))
         s.(st_fin)
         s.(st_ret)).

Definition add_fin_ret (f r: reg) : mon unit :=
  fun s => OK tt (mkstate
    s.(st_freshreg)
    s.(st_freshstate)
    s.(st_stm)
    s.(st_statetrans)
    s.(st_decl)
    (Some f) (Some r)).

Definition transf_instr (ni: node * instruction) : mon node :=
  match ni with
    (n, i) =>
    match i with
    | Inop n' => add_instr n n' Vskip
    | Iop op args dst n' =>
      match translate_instr op args with
      | Some instr => add_instr_reg dst n n' (block dst instr)
      | _ => error (Errors.msg "Instruction is not implemented.")
      end
    | Iload _ _ _ _ _ => error (Errors.msg "Loads are not implemented.")
    | Istore _ _ _ _ _ => error (Errors.msg "Stores are not implemented.")
    | Icall _ _ _ _ _ => error (Errors.msg "Calls are not implemented.")
    | Itailcall _ _ _ => error (Errors.msg "Tailcalls are not implemented.")
    | Ibuiltin _ _ _ _ => error (Errors.msg "Builtin functions not implemented.")
    | Icond cond args n1 n2 => error (Errors.msg "Condition not implemented.")
    | Ijumptable _ _ => error (Errors.msg "Jumptable not implemented.")
    | Ireturn r =>
      do fin <- decl_fresh_reg 1%nat;
      do rtrn <- decl_fresh_reg 32%nat;
      do _ <- add_fin_ret fin rtrn;
      match r with
      | Some r' =>
        add_instr n n (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z)) :: block rtrn (Vvar r') :: nil))
      | None =>
        add_instr n n (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z)) :: nil))
      end
    end
  end.

Definition make_stm_cases (s : positive * stmnt) : expr * stmnt :=
  match s with (a, b) => (posToExpr a, b) end.

Definition make_stm (r : reg) (s : PositiveMap.t stmnt) : stmnt :=
  Vcase (Vvar r) (map make_stm_cases (PositiveMap.elements s)).

Definition make_statetrans_cases (r : reg) (st : positive * statetrans) : expr * stmnt :=
  match st with
  | (n, StateGoto n') => (posToExpr n, nonblock r (posToExpr n'))
  | (n, StateCond c n1 n2) => (posToExpr n, nonblock r (Vternary c (posToExpr n1) (posToExpr n2)))
  end.

Definition make_statetrans (r : reg) (s : PositiveMap.t statetrans) : stmnt :=
  Vcase (Vvar r) (map (make_statetrans_cases r) (PositiveMap.elements s)).

Fixpoint allocate_regs (e : list (reg * nat)) {struct e} : list module_item :=
  match e with
  | (r, n)::es => Vdecl r n (Vlit (ZToValue n 0%Z)) :: allocate_regs es
  | nil => nil
  end.

Definition make_module_items (entry: node) (clk st rst: reg) (s: state) : list module_item :=
  (Valways (Voredge (Vposedge clk) (Vposedge rst))
    (Vcond (Vbinop Veq (Vvar rst) (Vlit (ZToValue 1%nat 1%Z)))
      (nonblock st (posToExpr entry))
      (make_statetrans st s.(st_statetrans))))
  :: (Valways Valledge (make_stm st s.(st_stm)))
  :: (allocate_regs s.(st_decl)).

(** To start out with, the assumption is made that there is only one
    function/module in the original code. *)

Definition transf_module (f: function) : mon module :=
  do _ <- traverselist transf_instr (Maps.PTree.elements f.(fn_code));
  do start <- decl_fresh_reg 1%nat;
  do rst <- decl_fresh_reg 1%nat;
  do clk <- decl_fresh_reg 1%nat;
  do st <- decl_fresh_reg 32%nat;
  do current_state <- get;
  let mi := make_module_items f.(fn_entrypoint) clk st rst current_state in
  match current_state.(st_fin), current_state.(st_ret) with
  | Some fin, Some rtrn =>
    ret (mkmodule start rst clk fin rtrn f.(fn_params) mi)
  | _, _ => error (Errors.msg "Veriloggen: finish and return signals not generated")
  end.

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

Definition transf_program (d : program) : Errors.res module :=
  match main_function d.(AST.prog_main) d.(AST.prog_defs) with
  | Some f => run_mon init_state (transf_module f)
  | _ => Errors.Error (Errors.msg "Veriloggen: could not find main module")
  end.
