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

(** The purpose of the hardware transfer language (HTL) is to create a more
  * hardware-like layout that is still similar to the register transfer language
  * (RTL) that it came from. The main change is that function calls become
  * module instantiations and that we now describe a state machine instead of a
  * control-flow graph.
  *)

From coqup.common Require Import Coquplib.

From compcert Require Import Maps.
From compcert Require Op AST Memory Registers.

Definition node := positive.

Definition reg := Registers.reg.

Definition ident := AST.ident.

Inductive instruction : Type :=
| Hnop : node -> instruction
| Hnonblock : Op.operation -> list reg -> reg -> node -> instruction
  (** [Hnonblock op args res next] Defines a nonblocking assignment to a
      register, using the operation defined in Op.v. *)
| Hload : AST.memory_chunk -> Op.addressing -> list reg -> reg -> node -> instruction
| Hstore : AST.memory_chunk -> Op.addressing -> list reg -> reg -> node -> instruction
| Hinst : AST.signature -> ident -> reg -> node -> instruction
  (** [Hinst sig fun args rst strt end res next] Defines the start of a
      module instantiation, meaning the function will run until the result is
      returned. *)
| Htailcall : AST.signature -> ident -> list reg -> instruction
| Hcond : Op.condition -> list reg -> node -> node -> instruction
| Hjumptable : reg -> list node -> instruction
| Hfinish : option reg -> instruction.

Record inst : Type :=
  mkinst {
    inst_moddecl : ident;
    inst_args : list reg
  }.

Definition code : Type := PTree.t instruction.

Definition instances : Type := PTree.t inst.

Definition empty_instances : instances := PTree.empty inst.

(** Function declaration for VTL also contain a construction which describes the
    functions that are called in the current function. This information is used
    to print out *)
Record module : Type :=
  mkmodule {
    mod_sig : AST.signature;
    mod_params : list reg;
    mod_stacksize : Z;
    mod_code : code;
    mod_insts : instances;
    mod_entrypoint : node
  }.

Definition moddecl := AST.fundef module.

Definition design := AST.program moddecl unit.

Definition modsig (md : moddecl) :=
  match md with
  | AST.Internal m => mod_sig m
  | AST.External ef => AST.ef_sig ef
  end.

(** Describes various transformations that can be applied to HTL. This applies
    the transformation to each instruction in the function and returns the new
    function with the modified instructions. *)
Section TRANSF.

  Variable transf_instr : node -> instruction -> instruction.

  Definition transf_module (m : module) : module :=
    mkmodule
      m.(mod_sig)
      m.(mod_params)
      m.(mod_stacksize)
      (PTree.map transf_instr m.(mod_code))
      m.(mod_insts)
      m.(mod_entrypoint).

End TRANSF.
