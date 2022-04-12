(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

===========
RTLBlockgen
===========

.. coq:: none
|*)

Require compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.

Require Import vericert.common.DecEq.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLBlock.

#[local] Open Scope positive.

(*|
``find_block max nodes index``: Does not need to be sorted, because we use
filter and the max fold function to find the desired element.
|*)

Definition find_block (max: positive) (nodes: list positive) (index: positive) : positive :=
  List.fold_right Pos.min max (List.filter (fun x => (index <=? x)) nodes).

(*Compute find_block 100 (2::94::48::39::19::nil) 40.*)

(*|
.. index::
   triple: abstract interpretation; check instruction; RTLBlockgen

Check Instruction
=================

Check if an instruction is a standard instruction that should be in a basic
block.
|*)

Definition check_instr (n: positive) (istr: RTL.instruction) (istr': instr) :=
  match istr, istr' with
  | RTL.Inop n', RBnop => (n' + 1 =? n)
  | RTL.Iop op args dst n', RBop None op' args' dst' =>
      ceq operation_eq op op' &&
      ceq list_pos_eq args args' &&
      ceq peq dst dst' && (n' + 1 =? n)
  | RTL.Iload chunk addr args dst n', RBload None chunk' addr' args' dst' =>
      ceq memory_chunk_eq chunk chunk' &&
      ceq addressing_eq addr addr' &&
      ceq list_pos_eq args args' &&
      ceq peq dst dst' &&
      (n' + 1 =? n)
  | RTL.Istore chunk addr args src n', RBstore None chunk' addr' args' src' =>
      ceq memory_chunk_eq chunk chunk' &&
      ceq addressing_eq addr addr' &&
      ceq list_pos_eq args args' &&
      ceq peq src src' &&
      (n' + 1 =? n)
  | _, _ => false
  end.

Definition check_cf_instr_body (istr: RTL.instruction) (istr': instr): bool :=
  match istr, istr' with
  | RTL.Iop op args dst _, RBop None op' args' dst' =>
      ceq operation_eq op op' &&
      ceq list_pos_eq args args' &&
      ceq peq dst dst'
  | RTL.Iload chunk addr args dst _, RBload None chunk' addr' args' dst' =>
      ceq memory_chunk_eq chunk chunk' &&
      ceq addressing_eq addr addr' &&
      ceq list_pos_eq args args' &&
      ceq peq dst dst'
  | RTL.Istore chunk addr args src _, RBstore None chunk' addr' args' src' =>
      ceq memory_chunk_eq chunk chunk' &&
      ceq addressing_eq addr addr' &&
      ceq list_pos_eq args args' &&
      ceq peq src src'
  | RTL.Inop _, RBnop
  | RTL.Icall _ _ _ _ _, RBnop
  | RTL.Itailcall _ _ _, RBnop
  | RTL.Ibuiltin _ _ _ _, RBnop
  | RTL.Icond _ _ _ _, RBnop
  | RTL.Ijumptable _ _, RBnop
  | RTL.Ireturn _, RBnop => true
  | _, _ => false
  end.

Definition check_cf_instr (istr: RTL.instruction) (istr': cf_instr) :=
  match istr, istr' with
  | RTL.Inop n, RBgoto n' => (n =? n')
  | RTL.Iop _ _ _ n, RBgoto n' => (n =? n')
  | RTL.Iload _ _ _ _ n, RBgoto n' => (n =? n')
  | RTL.Istore _ _ _ _ n, RBgoto n' => (n =? n')
  | RTL.Icall sig (inl r) args dst n, RBcall sig' (inl r') args' dst' n' =>
      ceq signature_eq sig sig' &&
      ceq peq r r' &&
      ceq list_pos_eq args args' &&
      ceq peq dst dst' &&
      (n =? n')
  | RTL.Icall sig (inr i) args dst n, RBcall sig' (inr i') args' dst' n' =>
      ceq signature_eq sig sig' &&
      ceq peq i i' &&
      ceq list_pos_eq args args' &&
      ceq peq dst dst' &&
      (n =? n')
  | RTL.Itailcall sig (inl r) args, RBtailcall sig' (inl r') args' =>
      ceq signature_eq sig sig' &&
      ceq peq r r' &&
      ceq list_pos_eq args args'
  | RTL.Itailcall sig (inr r) args, RBtailcall sig' (inr r') args' =>
      ceq signature_eq sig sig' &&
      ceq peq r r' &&
      ceq list_pos_eq args args'
  | RTL.Icond cond args n1 n2, RBcond cond' args' n1' n2' =>
      ceq condition_eq cond cond' &&
      ceq list_pos_eq args args' &&
      ceq peq n1 n1' && ceq peq n2 n2'
  | RTL.Ijumptable r ns, RBjumptable r' ns' =>
      ceq peq r r' && ceq list_pos_eq ns ns'
  | RTL.Ireturn (Some r), RBreturn (Some r') =>
      ceq peq r r'
  | RTL.Ireturn None, RBreturn None => true
  | _, _ => false
  end.

Definition is_cf_instr (n: positive) (i: RTL.instruction) :=
  match i with
  | RTL.Inop n' => negb (n' + 1 =? n)
  | RTL.Iop _ _ _ n' => negb (n' + 1 =? n)
  | RTL.Iload _ _ _ _ n' => negb (n' + 1 =? n)
  | RTL.Istore _ _ _ _ n' => negb (n' + 1 =? n)
  | RTL.Icall _ _ _ _ _ => true
  | RTL.Itailcall _ _ _ => true
  | RTL.Ibuiltin _ _ _ _ => true
  | RTL.Icond _ _ _ _ => true
  | RTL.Ijumptable _ _ => true
  | RTL.Ireturn _ => true
  end.

Definition check_present_blocks (c: code) (n: list positive) (max: positive) (i: positive) (istr: RTL.instruction) :=
  let blockn := find_block max n i in
  match c ! blockn with
  | Some istrs =>
      match List.nth_error istrs.(bb_body) (Pos.to_nat blockn - Pos.to_nat i)%nat with
      | Some istr' =>
          if is_cf_instr i istr
          then check_cf_instr istr istrs.(bb_exit) && check_cf_instr_body istr istr'
          else check_instr i istr istr'
      | None => false
      end
  | None => false
  end.

Parameter partition : RTL.function -> Errors.res function.

Definition transl_function (f: RTL.function) :=
  match partition f with
  | Errors.OK f' =>
      let blockids := map fst (PTree.elements f'.(fn_code)) in
      if forall_ptree (check_present_blocks f'.(fn_code) blockids (fold_right Pos.max 1 blockids))
                      f.(RTL.fn_code) then
        Errors.OK
          (mkfunction f.(RTL.fn_sig) f.(RTL.fn_params) f.(RTL.fn_stacksize) f'.(fn_code) f.(RTL.fn_entrypoint))
      else Errors.Error (Errors.msg "check_present_blocks failed")
  | Errors.Error msg => Errors.Error msg
  end.

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program : RTL.program -> Errors.res program :=
  transform_partial_program transl_fundef.
