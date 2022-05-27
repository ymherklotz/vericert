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
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.RTLParFU.
Require Import vericert.hls.FunctionalUnits.

#[local] Open Scope error_monad_scope.

Definition update {A: Type} (i: positive) (f: option A -> A) (pt: PTree.t A) :=
  PTree.set i (f (pt ! i)) pt.

Definition add_instr (instr_: instr) x :=
  match x with Some i => instr_ :: i | None => instr_ :: nil end.

Definition transl_instr (res: resources) (cycle: positive) (i: Gible.instr)
           (li: Errors.res (list instr * PTree.t (list instr))):
  Errors.res (list instr * PTree.t (list instr)) :=
  do (instr_list, d_tree) <- li;
  match i with
  | RBnop => Errors.OK (FUnop :: instr_list, d_tree)
  | RBop po op args d => Errors.OK (FUop po op args d :: instr_list, d_tree)
  | RBload po chunk addr args d =>
      match get_ram 0 res with
      | Some (ri, r) =>
          Errors.OK (FUop po Op.Onot (ram_u_en r::nil) (ram_u_en r)
                          :: FUop po (Op.Ointconst (Int.repr 0)) nil (ram_wr_en r)
                          :: FUop po (Op.Olea addr) args (ram_addr r)
                          :: FUop po (Op.Oshruimm (Int.repr 2)) ((ram_addr r)::nil) (ram_addr r)
                          :: instr_list, update (Pos.pred cycle)
                                                (add_instr (FUop po Op.Omove (ram_d_out r::nil) d))
                                                d_tree)
      | _ => Errors.Error (Errors.msg "Could not find RAM")
      end
  | RBstore po chunk addr args d =>
      match get_ram 0 res with
      | Some (ri, r) =>
          Errors.OK (FUop po Op.Onot (ram_u_en r::nil) (ram_u_en r)
                          :: FUop po (Op.Ointconst (Int.repr 1)) nil (ram_wr_en r)
                          :: FUop po Op.Omove (d::nil) (ram_d_in r)
                          :: FUop po (Op.Olea addr) args (ram_addr r)
                          :: FUop po (Op.Oshruimm (Int.repr 2)) ((ram_addr r)::nil) (ram_addr r)
                          :: instr_list, d_tree)
      | _ => Errors.Error (Errors.msg "Could not find RAM")
      end
  | RBsetpred op c args p => Errors.OK (FUsetpred op c args p :: instr_list, d_tree)
  | RBexit po cf => Errors.Error (Errors.msg "Wrong.")
  end.

Definition transl_cf_instr (i: Gible.cf_instr): RTLParFU.cf_instr :=
  match i with
  | RBcall sig r args d n => FUcall sig r args d n
  | RBtailcall sig r args => FUtailcall sig r args
  | RBbuiltin ef args r n => FUbuiltin ef args r n
  | RBcond c args n1 n2 => FUcond c args n1 n2
  | RBjumptable r ns => FUjumptable r ns
  | RBreturn r => FUreturn r
  | RBgoto n => FUgoto n
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

Definition transl_op_chain_block (res: resources) (cycle: positive) (instrs: list Gible.instr)
           (state: Errors.res (list (list instr) * PTree.t (list instr)))
  : Errors.res (list (list instr) * PTree.t (list instr)) :=
  do (li, tr) <- state;
  do (li', tr') <- fold_right (transl_instr res cycle) (OK (nil, tr)) instrs;
  OK (li' :: li, tr').

(*Compute transl_op_chain_block initial_resources 10%nat (RBop None (Op.Ointconst (Int.repr 1)) nil 1%positive::RBnop::RBnop::RBnop::nil) (OK (nil, PTree.empty _)).*)

Definition transl_par_block (res: resources) (cycle: positive) (instrs: list (list Gible.instr))
           (state: Errors.res (list (list (list instr)) * PTree.t (list instr)))
  : Errors.res (list (list (list instr)) * PTree.t (list instr)) :=
  do (li, tr) <- state;
  do (li', tr') <- fold_right (transl_op_chain_block res cycle) (OK (nil, tr)) instrs;
  OK (li' :: li, tr').

(*Compute transl_par_block initial_resources 10%nat ((RBop None (Op.Ointconst (Int.repr 1)) nil 1%positive::RBnop::nil)::(RBop None (Op.Ointconst (Int.repr 2)) nil 2%positive::RBnop::nil)::nil) (OK (((FUnop::nil)::nil)::nil, PTree.empty _)).*)

Definition transl_seq_block (res: resources) (b: list (list Gible.instr))
           (a: Errors.res (list (list (list instr)) * PTree.t (list instr) * positive)) :=
  do (litr, n) <- a;
  let (li, tr) := litr in
  do (li', tr') <- transl_par_block res n b (OK (li, tr));
  OK (li', tr', (n+1)%positive).

Definition insert_extra (pt: PTree.t (list instr)) (curr: list (list instr))
         (cycle_bb: (positive * list (list (list instr)))) :=
  let (cycle, bb) := cycle_bb in
  match pt ! cycle with
  | Some instrs => ((cycle + 1)%positive, (curr ++ (map (fun x => x :: nil) instrs)) :: bb)
  | None => ((cycle + 1)%positive, curr :: bb)
  end.

Definition transl_bb (res: resources) (bb: ParBB.t): Errors.res RTLParFU.bblock_body :=
  do (litr, n) <- fold_right (transl_seq_block res) (OK (nil, PTree.empty _, 1%positive)) bb;
  let (li, tr) := litr in
  OK (snd (fold_right (insert_extra tr) (1%positive, nil) li)).

(*Definition transl_bblock (res: resources) (bb: ParBB.t): Errors.res ParBB.t :=
  transl_bb res bb.

Definition error_map_ptree {A B: Type} (f: positive -> A -> res B) (pt: PTree.t A) :=
  do ptl' <- map_error (fun x => do x' <- uncurry f x; OK (fst x, x')) (PTree.elements pt);
  OK (PTree_Properties.of_list ptl').

Definition transl_code (fu: resources) (c: RTLPar.code): res code :=
   error_map_ptree (fun _ => transl_bblock fu) c.

Definition transl_function (f: RTLPar.function): Errors.res RTLParFU.function :=
  let max := RTLPar.max_reg_function f in
  let fu := set_res (Ram (mk_ram
                            (Z.to_nat (RTLBlockInstr.fn_stacksize f))
                            (max+1)%positive
                            (max+3)%positive
                            (max+7)%positive
                            (max+2)%positive
                            (max+6)%positive
                            (max+4)%positive
                            (max+5)%positive
                    )) initial_resources in
  do c' <- transl_code fu (RTLBlockInstr.fn_code f);
  Errors.OK (mkfunction (RTLBlockInstr.fn_sig f)
                        (RTLBlockInstr.fn_params f)
                        (RTLBlockInstr.fn_stacksize f)
                        c'
                        fu
                        (RTLBlockInstr.fn_entrypoint f)).

Definition transl_fundef p :=
  transf_partial_fundef transl_function p.

Definition transl_program (p : RTLPar.program) : Errors.res RTLParFU.program :=
  transform_partial_program transl_fundef p.
*)
