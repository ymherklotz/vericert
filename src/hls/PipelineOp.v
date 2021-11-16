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

Require Import Coq.Lists.List.

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.verilog.Op.


Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.FunctionalUnits.

Import Option.Notation.

Local Open Scope positive.

Definition div_pos (il: nat * list nat) x :=
  let (i, l) := il in
  match x with
  | RBop _ Odiv _ _ => (S i, i :: l)
  | RBop _ Odivu _ _ => (S i, i :: l)
  | RBop _ Omod _ _ => (S i, i :: l)
  | RBop _ Omodu _ _ => (S i, i :: l)
  | _ => (S i, l)
  end.

Definition div_pos_in_list (il: nat * list (nat * nat)) bb :=
  let (i, l) := il in
  let dp := snd (List.fold_left div_pos bb (0%nat, nil)) in
  (S i, (List.map (fun x => (i, x)) dp) ++ l).

Definition div_pos_in_block (il: nat * list (nat * nat * nat)) bb :=
  let (i, l) := il in
  let dp := snd (List.fold_left div_pos_in_list bb (0%nat, nil)) in
  (S i, (List.map (fun (yx : nat * nat) => let (y, x) := yx in (i, y, x)) dp) ++ l).

Definition find_divs (bb: bblock) :=
  snd (List.fold_left div_pos_in_block bb.(bb_body) (0%nat, nil)).

Fixpoint mapi' {A B: Type} (n: nat) (f: nat -> A -> B) (l: list A): list B :=
  match l with
  | nil => nil
  | a :: b => f n a :: mapi' (S n) f b
  end.

Definition mapi {A B: Type} := @mapi' A B 0.

Definition map_at {A: Type} (n: nat) (f: A -> A) (l: list A): list A :=
  mapi (fun i il =>
          if Nat.eqb n i
          then f il
          else il
       ) l.

Definition map_at_err {A: Type} (n: nat) (f: A -> A) (l: list A): option (list A) :=
  if (Datatypes.length l <=? n)%nat
  then None
  else Some (map_at n f l).

Definition replace_div' sdiv udiv (d: instr) :=
  match d with
  | RBop op Odiv args dst => RBpiped op sdiv args
  | RBop op Odivu args dst => RBpiped op udiv args
  | RBop op Omod args dst => RBpiped op sdiv args
  | RBop op Omodu args dst => RBpiped op udiv args
  | _ => d
  end.

Definition get_sdiv (fu: funct_unit) : option (reg * reg * reg) :=
  match fu with
  | SignedDiv s a b d _ => Some (a, b, d)
  | _ => None
  end.

Definition get_udiv (fu: funct_unit) : option (reg * reg * reg) :=
  match fu with
  | UnsignedDiv s a b d _ => Some (a, b, d)
  | _ => None
  end.

Definition get_smod (fu: funct_unit) : option (reg * reg * reg) :=
  match fu with
  | SignedDiv s a b _ d => Some (a, b, d)
  | _ => None
  end.

Definition get_umod (fu: funct_unit) : option (reg * reg * reg) :=
  match fu with
  | UnsignedDiv s a b _ d => Some (a, b, d)
  | _ => None
  end.

Definition bind3 {A B C D: Type}
           (f: option (A * B * C))
           (g: A -> B -> C -> option D) : option D :=
  match f with
  | Some (a, b, c) => g a b c
  | None => None
  end.

Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).

Definition replace_div_error (fu: funct_units) (bb: bb) (loc: nat * nat * nat) :=
  match loc with
  | (z, y, x) =>
    do sdiv <- fu.(avail_sdiv);
    do udiv <- fu.(avail_udiv);
    do sfu <- PTree.get sdiv fu.(avail_units);
    do ufu <- PTree.get udiv fu.(avail_units);
    do z' <- List.nth_error bb z;
    do y' <- List.nth_error z' y;
    do x' <- List.nth_error y' x;
    let transf := map_at z (map_at y (map_at x (replace_div' sdiv udiv))) bb in
    match x' with
    | RBop op Odiv args dst =>
      do (s1, s2, src) <- get_sdiv sfu;
      map_at_err (z + 32)%nat (fun x => (RBassign op sdiv src dst :: nil) :: x) transf
    | RBop op Odivu args dst =>
      do (s1, s2, src) <- get_udiv ufu;
      map_at_err (z + 32)%nat (fun x => (RBassign op sdiv src dst :: nil) :: x) transf
    | RBop op Omod args dst =>
      do (s1, s2, src) <- get_smod sfu;
      map_at_err (z + 32)%nat (fun x => (RBassign op sdiv src dst :: nil) :: x) transf
    | RBop op Omodu args dst =>
      do (s1, s2, src) <- get_umod ufu;
      map_at_err (z + 32)%nat (fun x => (RBassign op sdiv src dst :: nil) :: x) transf
    | _ => None
    end
  end.

Definition replace_div (fu: funct_units) (bb: bb) loc :=
  match replace_div_error fu bb loc with
  | Some bb' => bb'
  | _ => bb
  end.

Definition transf_code (i: code * funct_units) (bbn: node * bblock) :=
  let (c, fu) := i in
  let (n, bb) := bbn in
  let divs := find_divs bb in
  match divs with
  | nil => (PTree.set n bb c, fu)
  | _ =>
    (PTree.set n (mk_bblock (List.fold_left (replace_div fu) divs bb.(bb_body)) bb.(bb_exit)) c, fu)
  end.

Definition create_fu (r: reg) :=
  let fu := PTree.set 2 (UnsignedDiv 32 (r+5) (r+6) (r+7) (r+8))
      (PTree.set 1 (SignedDiv 32 (r+1) (r+2) (r+3) (r+4)) (PTree.empty _)) in
  mk_avail_funct_units (Some 1) (Some 2) fu.

Definition transf_function (f: function) : function :=
  let fu := create_fu (max_reg_function f) in
  let (c, fu') := List.fold_left transf_code
                                (PTree.elements f.(fn_code))
                                (PTree.empty bblock, fu) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    c
    fu'
    f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
