(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.micromega.Lia.

Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.RTLParFU.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.FunctionalUnits.

#[local] Open Scope error_monad_scope.

Definition transl_instr (res: resources) (i: RTLBlockInstr.instr): Errors.res (list (Z * RTLParFU.instr)) :=
  match i with
  | RBnop => Errors.OK ((0, FUnop)::nil)
  | RBop po op args d => Errors.OK ((0, FUop po op args d)::nil)
  | RBload po chunk addr args d =>
      match get_ram 0 res with
      | Some (ri, r) =>
          Errors.OK ((0, FUop po Op.Onot (ram_u_en r::nil) (ram_u_en r))
                       :: (0, FUop po (Op.Ointconst (Int.repr 0)) nil (ram_wr_en r))
                       :: (0, FUop po (Op.Olea addr) args (ram_addr r))
                       :: (1, FUop po Op.Omove (ram_d_out r::nil) d)
                       :: nil)
      | _ => Errors.Error (Errors.msg "Could not find RAM")
      end
  | RBstore po chunk addr args d =>
      match get_ram 0 res with
      | Some (ri, r) =>
          Errors.OK ((0, FUop po Op.Onot (ram_u_en r::nil) (ram_u_en r))
                       :: (0, FUop po (Op.Ointconst (Int.repr 1)) nil (ram_wr_en r))
                       :: (0, FUop po Op.Omove (d::nil) (ram_d_in r))
                       :: (0, FUop po (Op.Olea addr) args (ram_addr r))
                       :: nil)
      | _ => Errors.Error (Errors.msg "Could not find RAM")
      end
  | RBsetpred op c args p => Errors.OK ((0, FUsetpred op c args p)::nil)
  end.

Fixpoint transl_cf_instr (i: RTLBlockInstr.cf_instr): RTLParFU.cf_instr :=
  match i with
  | RBcall sig r args d n => FUcall sig r args d n
  | RBtailcall sig r args => FUtailcall sig r args
  | RBbuiltin ef args r n => FUbuiltin ef args r n
  | RBcond c args n1 n2 => FUcond c args n1 n2
  | RBjumptable r ns => FUjumptable r ns
  | RBreturn r => FUreturn r
  | RBgoto n => FUgoto n
  | RBpred_cf po c1 c2 => FUpred_cf po (transl_cf_instr c1) (transl_cf_instr c2)
  end.

Definition list_split {A:Type} (l: list (Z * A)) : (list (Z * A)) * (list (Z * A)) :=
  (filter (fun x => Z.eqb 0 (fst x)) l,
    map (fun x => (Z.pred (fst x), snd x)) (filter (fun x => negb (Z.eqb 0 (fst x))) l)).

Fixpoint map_error {A B : Type} (f : A -> res B) (l : list A) {struct l} : res (list B) :=
  match l with
  | nil => OK nil
  | x::xs =>
    do y <- f x ;
    do ys <- map_error f xs ;
    OK (y::ys)
  end.

Definition transl_bb (res: resources) (bb: RTLPar.bb): RTLParFU.bblock_body :=
  map_error (map_error (fold_right
                          (fun c n => transl_instr res))) bb.

Definition transl_bblock (bb: RTLPar.bblock): RTLParFU.bblock :=
  RTLParFU.mk_bblock (transl_bb (bb_body bb)) (transl_cf_instr (bb_exit bb)).

Definition transl_code (c: RTLPar.code): RTLParFU.code :=
  PTree.map (fun _ => transl_bblock) c.

Definition transl_function (f: RTLPar.function): Errors.res RTLParFU.function :=
  Errors.OK (RTLParFU.mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) (transl_code (fn_code f))
                                 initial_resources (fn_entrypoint f)).

Definition transl_fundef p :=
  transf_partial_fundef transl_function p.

Definition transl_program (p : RTLPar.program) : Errors.res RTLParFU.program :=
  transform_partial_program transl_fundef p.
