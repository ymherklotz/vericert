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

From coqup Require Import HTL Verilog Coquplib.

From compcert Require Errors Op AST Integers.

Definition node : Type := positive.
Definition reg : Type := positive.
Definition ident : Type := positive.

Inductive statetrans : Type :=
  | StateGoto (p : node)
  | StateCond (c : expr) (t f : node).

Record state: Type := mkstate {
  st_variables: PositiveMap.t (nat * expr);
  st_stm : PositiveMap.t stmnt;
  st_statetrans : PositiveMap.t statetrans;
}.

Definition init_state : state :=
  mkstate (PositiveMap.empty (nat * expr)) (PositiveMap.empty stmnt) (PositiveMap.empty statetrans).

Inductive res (A: Type) (S: Type): Type :=
  | Error: Errors.errmsg -> res A S
  | OK: A -> S -> res A S.

Arguments OK [A S].
Arguments Error [A S].

Definition mon (A: Type) : Type := res A state.

Definition ret {A: Type} (x: A) (s: state) : mon A := OK x s.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
    match f with
    | Error msg => Error msg
    | OK a s => g a
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Definition bindS {A B: Type} (f: mon A) (g: A -> state -> mon B) : mon B :=
  match f with
  | Error msg => Error msg
  | OK a s => g a s
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bindS A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  match f with
  | OK a s' => OK a s'
  | Error _ => g
  end.

Module PTree.
  Export Maps.PTree.

  Fixpoint xtraverse {A B : Type} (f : positive -> A -> state -> mon B)
           (m : t A) (s : state) (i : positive)
           {struct m} : mon (t B) :=
    match m with
    | Leaf => OK Leaf s
    | Node l o r =>
      let newo :=
          match o with
          | None => OK None s
          | Some x =>
            match f (prev i) x s with
            | Error err => Error err
            | OK val s' => OK (Some val) s'
            end
          end in
      match newo with
      | OK no s =>
        do (nl, s') <- xtraverse f l s (xO i);
        do (nr, s'') <- xtraverse f r s' (xI i);
        OK (Node nl no nr) s''
      | Error msg => Error msg
      end
    end.

  Definition traverse {A B : Type} (f : positive -> A -> state -> mon B) m :=
    xtraverse f m init_state xH.

  Definition traverse1 {A B : Type} (f : A -> state -> mon B) := traverse (fun _ => f).

End PTree.

Definition nonblock (dst : reg) (e : expr) := Vnonblock (Vvar dst) e.

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

Definition add_instr (n : node) (n' : node) (s : state) (st : stmnt) : mon node :=
  OK n' (mkstate s.(st_variables)
                 (PositiveMap.add n st s.(st_stm))
                 (PositiveMap.add n (StateGoto n') s.(st_statetrans))).

Definition option_err {A : Type} (str : string) (v : option A) (s : state) : mon A :=
  match v with
  | Some v' => OK v' s
  | _ => Error (Errors.msg str)
  end.

Definition transf_instr (n : node) (i : instruction) (s : state) : mon node :=
  match i with
  | Hnop n' =>
    add_instr n n' s Vskip
  | Hnonblock op args dst n' =>
    match translate_instr op args with
    | Some instr => add_instr n n' s (nonblock dst instr)
    | _ => Error (Errors.msg "Instruction is not implemented.")
    end
  | Hload _ _ _ _ _ => Error (Errors.msg "Loads are not implemented.")
  | Hstore _ _ _ _ _ => Error (Errors.msg "Stores are not implemented.")
  | Hinst _ _ _ _ => Error (Errors.msg "Calls are not implemented.")
  | Htailcall _ _ _ => Error (Errors.msg "Tailcalls are not implemented.")
  | Hcond cond args n1 n2 => Error (Errors.msg "Condition not implemented.")
  | Hjumptable _ _ => Error (Errors.msg "Jumptable not implemented.")
  | Hfinish r =>
    match r with
    | Some x => OK n s
    | None => OK n s
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

Definition make_globals (globals : PositiveMap.t (nat * expr)) : verilog := nil.

Definition make_verilog (s : state) : verilog :=
  let r := 500%positive in
  (make_statetrans r s.(st_statetrans)) :: (make_stm r s.(st_stm))
                                        :: (make_globals s.(st_variables)).

(** To start out with, the assumption is made that there is only one
    function/module in the original code. *)
Definition transf_module (m: module) : Errors.res verilog :=
  match PTree.traverse transf_instr m.(mod_code) with
  | OK _ s => Errors.OK (make_verilog s)
  | Error err => Errors.Error err
  end.

Fixpoint main_module (main : ident) (flist : list (ident * AST.globdef moddecl unit))
         {struct flist} : option module :=
  match flist with
  | (i, AST.Gfun (AST.Internal f)) :: xs =>
    if Pos.eqb i main
    then Some f
    else main_module main xs
  | _ :: xs => main_module main xs
  | nil => None
  end.

Definition transf_program (d : design) : Errors.res verilog :=
  match main_module d.(AST.prog_main) d.(AST.prog_defs) with
  | Some m => transf_module m
  | _ => Errors.Error (Errors.msg "Could not find main module")
  end.
