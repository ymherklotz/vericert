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

From coqup Require Import HTL Coquplib.

From compcert Require Import Maps.
From compcert Require Errors.
From compcert Require Import AST RTL.

Record state: Type := mkstate {
  st_nextinst: positive;
  st_instances: instances;
}.

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

Definition init_state : state :=
  mkstate 1%positive empty_instances.

Module PTree.
  Export Maps.PTree.

  Fixpoint xtraverse {A B : Type} (f : positive -> A -> state -> mon B)
           (m : PTree.t A) (s : state) (i : positive)
           {struct m} : mon (PTree.t B) :=
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

Definition transf_instr (pc: node) (rtl: RTL.instruction) (s: state)
  : mon HTL.instruction :=
  match rtl with
  | RTL.Inop n =>
    (** Nop instruction should just become a Skip in Verilog, which is just a
        semicolon. *)
    ret (HTL.Hnop n) s
  | RTL.Iop op args res n =>
    (** Perform an arithmetic operation over registers.  This will just become
        one binary operation in Verilog.  This will contain a list of registers,
        so these will just become a chain of binary operations in Verilog. *)
    ret (HTL.Hnonblock op args res n) s
  | RTL.Iload chunk addr args dst n =>
    (** Load from memory, which will maybe become a load from RAM, however, I'm
        not sure yet how memory will be implemented or how it will formalised
        be. *)
    ret (HTL.Hload chunk addr args dst n) s
  | RTL.Istore chunk addr args src n =>
    (** How memory will be laid out will also affect how stores are handled.  For
        now hopefully these can be ignored, and hopefull they are not used that
        often when they are not required in C. *)
    ret (HTL.Hstore chunk addr args src n) s
  | RTL.Icall sig ros args res n =>
    (** Function call should become a module instantiation with start and end
        signals appropriately wired up. *)
    match ros with
    | inr i =>
      let inst := mkinst i args in
      let newinstances := PTree.set s.(st_nextinst) inst s.(st_instances) in
      ret (HTL.Hinst sig i res n)
          (mkstate ((s.(st_nextinst) + 1)%positive)
                   newinstances)
    | _ => Error (Errors.msg "Function pointers are not supported.")
    end
  | RTL.Itailcall sig ros args =>
    (** Should be converted into a reset of the modules state, setting the
        initial variables correctly.  This would simulate a tailcall as it is
        similar to jumping back to the top of the function in assembly. *)
    match ros with
    | inr i => ret (HTL.Htailcall sig i args) s
    | _ => Error (Errors.msg "Function pointers are not supported.")
    end
  | RTL.Ibuiltin ef args res n =>
    (** Builtin functions will have to supported manually, by implementing the
        Verilog myself. *)
    Error (Errors.msg "builtin functions are not supported.")
  | RTL.Icond cond args n1 n2 =>
    (** Will be converted into two separate processes that are combined by a mux
        at the end, with a start flag that propagates in the construct that should
        be chosen. *)
    ret (HTL.Hcond cond args n1 n2) s
  | RTL.Ijumptable arg tbl =>
    (** A jump to a specific instruction in the list, this will require setting
        the state in the state machine appropriately.  This is trivial to
        implement if no scheduling is involved, but as soon as that isn't the
        case it might be difficult to find that location.  It would help to
        transform the CFG to a few basic blocks first which cannot have any
        branching. *)
    ret (HTL.Hjumptable arg tbl) s
  | RTL.Ireturn r =>
    (** The return value of the function, which will just mean that the finished
        signal goes high and the result is stored in the result register. *)
    ret (HTL.Hfinish r) s
  end.

Definition transf_function (f: function) : Errors.res module :=
  match (PTree.traverse transf_instr f.(fn_code)) with
  | OK code s =>
    Errors.OK (mkmodule
          f.(fn_sig)
          f.(fn_params)
          f.(fn_stacksize)
          code
          s.(st_instances)
          f.(fn_entrypoint))
  | Error err => Errors.Error err
  end.

Definition transf_fundef (fd: fundef) : Errors.res moddecl :=
  transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : Errors.res design :=
  transform_partial_program transf_fundef p.
