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

From compcert Require Errors Op AST.

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

(** Translate an instruction to a statement. *)
Definition translate_instr (op : Op.operation) (args : list reg) (dst : reg) : option stmnt :=
  let assign := nonblock dst in
  match op, args with
  | Op.Omove, v::nil => Some (assign (Vvar v))
  | Op.Ointconst n, _ => Some (assign (Vlit (intToValue n)))
  | Op.Oneg, _ => None
  | Op.Osub, _ => None
  | Op.Omul, _ => None
  | Op.Omulimm n, _ => None
  | Op.Omulhs, _ => None
  | Op.Omulhu, _ => None
  | Op.Odiv, _ => None
  | Op.Odivu, _ => None
  | Op.Omod, _ => None
  | Op.Omodu, _ => None
  | Op.Oand, _ => None
  | Op.Oandimm n, _ => None
  | Op.Oor, _ => None
  | Op.Oorimm n, _ => None
  | Op.Oxor, _ => None
  | Op.Oxorimm n, _ => None
  | Op.Onot, _ => None
  | Op.Oshl, _ => None
  | Op.Oshlimm n, _ => None
  | Op.Oshr, _ => None
  | Op.Oshrimm n, _ => None
  | Op.Oshrximm n, _ => None
  | Op.Oshru, _ => None
  | Op.Oshruimm n, _ => None
  | Op.Ororimm n, _ => None
  | Op.Oshldimm n, _ => None
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
    match (translate_instr op args dst) with
    | Some instr => add_instr n n' s instr
    | _ => Error (Errors.msg "Instruction is not implemented.")
    end
  | Hload _ _ _ _ _ => Error (Errors.msg "Load not implemented.")
  | Hstore _ _ _ _ _ => Error (Errors.msg "Store not implemented.")
  | Hinst _ _ _ _ => Error (Errors.msg "Call not implemented.")
  | Htailcall _ _ _ => Error (Errors.msg "Tailcall not implemented.")
  | Hcond _ _ _ _ => Error (Errors.msg "Cond not implemented.")
  | Hjumptable _ _ => Error (Errors.msg "Jumptable not implemented.")
  | Hfinish _ => OK n s
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
