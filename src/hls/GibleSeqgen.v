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
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSeq.

#[local] Open Scope positive.

Definition check_valid_node (tc: code) (e: node) :=
  match tc ! e with
  | Some _ => true
  | _ => false
  end.

Fixpoint check_code (c: RTL.code) (tc: code) (pc: node) (b: SeqBB.t) :=
  match c ! pc, b with
  | Some (RTL.Inop pc'), RBnop :: (_ :: _ :: _) as b' =>
      check_code c tc pc' b'
  | Some (RTL.Iop op' args' dst' pc'), RBop None op args dst :: (_ :: _ :: _) as b' =>
      ceq operation_eq op op'
      && ceq list_pos_eq args args'
      && ceq peq dst dst'
      && check_code c tc pc' b'
  | Some (RTL.Iload chunk' addr' args' dst' pc'),
    RBload None chunk addr args dst :: (_ :: _ :: _) as b' =>
      ceq memory_chunk_eq chunk chunk'
      && ceq addressing_eq addr addr'
      && ceq list_pos_eq args args'
      && ceq peq dst dst'
      && check_code c tc pc' b'
  | Some (RTL.Istore chunk' addr' args' src' pc'),
    RBstore None chunk addr args src :: (_ :: _ :: _) as b' =>
      ceq memory_chunk_eq chunk chunk'
      && ceq addressing_eq addr addr'
      && ceq list_pos_eq args args'
      && ceq peq src src'
      && check_code c tc pc' b'
  | Some (RTL.Inop pc''), RBnop :: RBexit None (RBgoto pc') :: nil =>
      check_valid_node tc pc'
      && ceq peq pc' pc''
  | Some (RTL.Iop op' args' dst' pc''), RBop None op args dst :: RBexit None (RBgoto pc') :: nil =>
      check_valid_node tc pc'
      && ceq peq pc' pc''
      && ceq operation_eq op op'
      && ceq list_pos_eq args args'
      && ceq peq dst dst'
  | Some (RTL.Iload chunk' addr' args' dst' pc''),
    RBload None chunk addr args dst :: RBexit None (RBgoto pc') :: nil =>
      check_valid_node tc pc'
      && ceq peq pc' pc''
      && ceq memory_chunk_eq chunk chunk'
      && ceq addressing_eq addr addr'
      && ceq list_pos_eq args args'
      && ceq peq dst dst'
  | Some (RTL.Istore chunk' addr' args' src' pc''),
    RBstore None chunk addr args src :: RBexit None (RBgoto pc') :: nil =>
      check_valid_node tc pc'
      && ceq peq pc' pc''
      && ceq memory_chunk_eq chunk chunk'
      && ceq addressing_eq addr addr'
      && ceq list_pos_eq args args'
      && ceq peq src src'
  | Some (RTL.Icall sig' (inl r') args' dst' pc''),
    RBnop :: RBexit None (RBcall sig (inl r) args dst pc') :: nil =>
      check_valid_node tc pc'
      && ceq peq pc' pc''
      && ceq signature_eq sig sig'
      && ceq peq r r'
      && ceq list_pos_eq args args'
      && ceq peq dst dst'
  | Some (RTL.Icall sig' (inr i') args' dst' pc''),
    RBnop :: RBexit None (RBcall sig (inr i) args dst pc') :: nil =>
      check_valid_node tc pc'
      && ceq peq pc' pc''
      && ceq signature_eq sig sig'
      && ceq peq i i'
      && ceq list_pos_eq args args'
      && ceq peq dst dst'
  | Some (RTL.Itailcall sig (inl r) args),
    RBnop :: RBexit None (RBtailcall sig' (inl r') args') :: nil =>
      ceq signature_eq sig sig'
      && ceq peq r r'
      && ceq list_pos_eq args args'
  | Some (RTL.Itailcall sig (inr r) args),
    RBnop :: RBexit None (RBtailcall sig' (inr r') args') :: nil =>
      ceq signature_eq sig sig'
      && ceq peq r r'
      && ceq list_pos_eq args args'
  | Some (RTL.Icond cond args n1 n2), RBnop :: RBexit None (RBcond cond' args' n1' n2') :: nil =>
      check_valid_node tc n1
      && check_valid_node tc n2
      && ceq condition_eq cond cond'
      && ceq list_pos_eq args args'
      && ceq peq n1 n1'
      && ceq peq n2 n2'
  | Some (RTL.Ijumptable r ns), RBnop :: RBexit None (RBjumptable r' ns') :: nil =>
      ceq peq r r'
      && ceq list_pos_eq ns ns'
      && forallb (check_valid_node tc) ns
  | Some (RTL.Ireturn (Some r)), RBnop :: RBexit None (RBreturn (Some r')) :: nil =>
      ceq peq r r'
  | Some (RTL.Ireturn None), RBnop :: RBexit None (RBreturn None) :: nil => true
  | _, _ => false
  end.

Parameter partition : RTL.function -> Errors.res function.

Definition transl_function (f: RTL.function) :=
  match partition f with
  | Errors.OK f' =>
      if check_valid_node f'.(fn_code) f.(RTL.fn_entrypoint) then
        if forall_ptree (check_code f.(RTL.fn_code) f'.(fn_code)) f'.(fn_code) then
          Errors.OK
            (mkfunction f.(RTL.fn_sig) f.(RTL.fn_params) f.(RTL.fn_stacksize) f'.(fn_code) f.(RTL.fn_entrypoint))
        else Errors.Error (Errors.msg "check_present_blocks failed")
      else Errors.Error (Errors.msg "entrypoint does not exists")
  | Errors.Error msg => Errors.Error msg
  end.

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program : RTL.program -> Errors.res program :=
  transform_partial_program transl_fundef.
