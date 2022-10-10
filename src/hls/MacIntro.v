(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
 * Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.common.AST.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GiblePar.
Require Import vericert.hls.Predicate.

Definition is_adder op :=
  match op with
  | Op.Osub | Op.Osubl => true
  | Op.Olea a | Op.Oleal a => match a with
    | Op.Aindexed2 o => o =? 0
    | Op.Aindexed2scaled s o => (s =? 1) && (o =? 0)
    | _ => false
    end
  (*| Op.Oaddlimm _*) | _ => false
  end.

Definition is_multiplier op :=
  match op with
  | Op.Omul | Op.Omull
  (*| Op.Omulhs | Op.Omulhu | Op.Omullhs | Op.Omullhu*) => true
  (*| Op.Omulimm _ | Op.Omullimm _ *) | _ => false
  end.

#[local] Open Scope positive.

(* Transforms "+ x * y z" into "mac x y z"
 * provided "* y z" isn't used or moved before the addition (currently: is added immediately after)
 * and there is no need to move operations arround (ATM, otherwise liveness analysis is needed)
 *)
Definition intro_mac_instr vregs i (state: option instr * list instr) :=
  let (cell, il) := state in
  match i with
  | RBop p op rl r => if is_adder op
    then (Some i, match cell with Some ic => ic :: il | None => il end)
    else (None,
      match cell with
      | Some (RBop pc opc rlc rc as ic) =>
        if is_multiplier op && in_dec peq r rlc && option_eq pred_op_dec pc p
          && option_eq bool_dec (PTree.get r vregs) (Some true)
        then RBop p Op.Omacl ((remove peq r rlc) ++ rl) rc :: il
        else i :: ic :: il
      | Some ic => i :: ic :: il (* never taken *)
      | None => i :: il
      end)
  | _ => (None, match cell with Some ic => i :: ic :: il | None => i :: il end)
  end.

Definition intro_mac_instr_list vregs il :=
  let (cell, il) := fold_right (intro_mac_instr vregs) (None, nil) il in
  match cell with Some i => i::il | None => il end.

Definition intro_mac_bb vregs := map (map (intro_mac_instr_list vregs)).

Definition transf_bb vregs f_code n bb :=
  PTree.set n (intro_mac_bb vregs bb) f_code.

Definition mark_once_register (ptree: PTree.t bool) (r: Registers.reg) :=
  match PTree.get r ptree with
  | None => PTree.set r true ptree
  | Some true => PTree.set r false ptree
  | Some false => ptree
  end.

Definition input_registers (i: instr) :=
  match i with
  | RBnop => nil
  | RBop _ _ rl _ | RBload _ _ _ rl _ | RBsetpred _ _ rl _ => rl
  | RBstore _ _ _ rl r => r::rl
  | RBexit _ ci => match ci with
    | RBcall _ (inl r) rl _ _ | RBtailcall _ (inr r) rl => r::rl
    | RBbuiltin _ barl _ _ => concat (map (params_of_builtin_arg (A:=_)) barl)
    | RBcall _ (inr _) rl _ _ | RBtailcall _ (inl _) rl | RBcond _ rl _ _ => rl
    | RBjumptable r _ | RBreturn (Some r) => r::nil
    | _ => nil
    end
  end.

Definition read_once_bb (ptree: PTree.t bool) (n: node) (b: ParBB.t) :=
  ParBB.foldl _
    (fun t i => fold_left mark_once_register (input_registers i) t) b ptree.

(* liveness analysis would be better but uniqueness of reading is good enough *)
Definition read_once (f : function) :=
  PTree.fold read_once_bb f.(fn_code) (PTree.empty _).

Definition transf_function (f: function) : function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
             (PTree.fold (transf_bb (read_once f)) f.(fn_code) (PTree.empty _))
             f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
