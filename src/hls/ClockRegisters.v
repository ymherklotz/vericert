(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.FSets.FMapPositive.
Require Import Coq.micromega.Lia.

Require compcert.common.Events.
Require compcert.common.Globalenvs.
Require compcert.common.Smallstep.
Require compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.
Require Import vericert.hls.DHTL.
Require vericert.hls.Verilog.

Require Import vericert.common.Errormonad.
Import ErrorMonad.
Import ErrorMonadExtra.
Import MonadNotation.

#[local] Open Scope monad_scope.

Definition error {A} m := @Errors.Error A (Errors.msg m).

Definition pred := positive.

Inductive lhs : Type :=
| LhsReg : reg -> lhs
| LhsPred : pred -> lhs
.

Definition lhs_eqd (r1 r2: lhs): {r1 = r2} + {r1 <> r2}.
  pose proof peq.
  decide equality.
Defined.

Module R_indexed.
  Definition t := lhs.
  Definition index (rs: t) : positive :=
    match rs with
    | LhsReg r => xO r
    | LhsPred p => xI p
    end.

  Lemma index_inj:  forall (x y: t), index x = index y -> x = y.
  Proof. destruct x; destruct y; crush. Qed.

  Definition eq := lhs_eqd.
End R_indexed.

Module RTree := ITree(R_indexed).

Inductive flat_expr : Type :=
| FVlit : value -> flat_expr
| FVvar : reg -> flat_expr
| FVbinop : Verilog.binop -> flat_expr -> flat_expr -> flat_expr
| FVunop : Verilog.unop -> flat_expr -> flat_expr
| FVternary : flat_expr -> flat_expr -> flat_expr -> flat_expr
.

Inductive flat_stmnt : Type :=
| FVblock : reg -> flat_expr -> flat_stmnt
| FVnonblock : reg -> flat_expr -> flat_stmnt
.

Fixpoint flatten_expr (e: Verilog.expr) : Errors.res flat_expr :=
  match e with
  | Verilog.Vlit v => ret (FVlit v)
  | Verilog.Vvar r => ret (FVvar r)
  | Verilog.Vunop u e => 
    do fe <- flatten_expr e;
    ret (FVunop u fe)
  | Verilog.Vbinop u e1 e2 => 
    do fe1 <- flatten_expr e1;
    do fe2 <- flatten_expr e2;
    ret (FVbinop u fe1 fe2)
  | Verilog.Vternary e1 e2 e3 => 
    do fe1 <- flatten_expr e1;
    do fe2 <- flatten_expr e2;
    do fe3 <- flatten_expr e3;
    ret (FVternary fe1 fe2 fe3)
  | Verilog.Vrange _ _ _ => error "ClockRegisters: Could not translate Vrange"
  | Verilog.Vvari _ _ => error "ClockRegisters: Could not translate Vvari"
  | Verilog.Vinputvar _ => error "ClockRegisters: Could not translate Vinputvar"
  end.

Fixpoint flatten_seq_block (s: Verilog.stmnt) : Errors.res (list flat_stmnt) := 
  match s with
  | Verilog.Vskip => ret nil
  | Verilog.Vseq s1 s2 =>
    do s1' <- flatten_seq_block s1;
    do s2' <- flatten_seq_block s2;
    ret (s1' ++ s2')
  | Verilog.Vblock (Verilog.Vvar r) e => 
    do fe <- flatten_expr e;
    ret (FVblock r fe :: nil)
  (* | Verilog.Vblock (Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2)) e =>  *)
  (*   if Pos.eqb preg r && Int.eq i1 i2 then *)
  (*     match Int.unsigned i1, flatten_expr e with  *)
  (*     | Zpos p, Some fe => Some (FVblock p fe :: nil) *)
  (*     | _, _ => None *)
  (*     end *)
  (*   else None *)
  | Verilog.Vnonblock (Verilog.Vvar r) e => 
    do fe <- flatten_expr e;
    ret (FVnonblock r fe :: nil)
  (* | Verilog.Vnonblock (Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2)) e =>  *)
  (*   if Pos.eqb preg r && Int.eq i1 i2 then *)
  (*     match Int.unsigned i1, flatten_expr e with  *)
  (*     | Zpos p, Some fe => Some (FVnonblock p fe :: nil) *)
  (*     | _, _ => None *)
  (*     end *)
  (*   else None *)
  | _ => error "ClockRegisters: Could not translate seq_block"
  end.

Fixpoint expand_expr (f: flat_expr): Verilog.expr :=
  match f with
  | FVlit l => Verilog.Vlit l
  | FVvar r => Verilog.Vvar r
  | FVbinop b e1 e2 => Verilog.Vbinop b (expand_expr e1) (expand_expr e2)
  | FVunop b e => Verilog.Vunop b (expand_expr e)
  | FVternary e1 e2 e3 => Verilog.Vternary (expand_expr e1) (expand_expr e2) (expand_expr e3)
  end.

Definition expand_assignment (f: flat_stmnt): Verilog.stmnt := 
  match f with
  | FVblock r e => Verilog.Vblock (Verilog.Vvar r) (expand_expr e)
  | FVnonblock r e => Verilog.Vnonblock (Verilog.Vvar r) (expand_expr e)
  end.

Definition fold_seq_block (s: list flat_stmnt): Verilog.stmnt :=
  fold_left (fun a b => Verilog.Vseq a (expand_assignment b)) s Verilog.Vskip.

Fixpoint clock_expr (t: PTree.t flat_expr) (f: flat_expr): flat_expr :=
  match f with
  | FVvar r => 
    match PTree.get r t with
    | Some e => e
    | None => FVvar r
    end
  | FVunop b e => FVunop b (clock_expr t e)
  | FVbinop b e1 e2 => 
    FVbinop b (clock_expr t e1) (clock_expr t e2)
  | FVternary e1 e2 e3 => 
    FVternary (clock_expr t e1) (clock_expr t e2) (clock_expr t e3)
  | _ => f
  end.

Definition clock_assignment (tl: RTree.t flat_expr * list flat_stmnt) (f: flat_stmnt): 
    (RTree.t flat_expr * list flat_stmnt) :=
  let (t, l) := tl in
  match f with
  | FVblock r e => 
    let fe := clock_expr t e in 
    (PTree.set r fe t, l ++ (FVnonblock r fe :: nil))
  | _ => (t, l ++ (f :: nil))
  end.

Definition clock_assignments (s: list flat_stmnt): list flat_stmnt :=
  snd (fold_left clock_assignment s (RTree.empty _, nil)).

Definition clock_stmnt_assignments (s: Verilog.stmnt): Errors.res Verilog.stmnt :=
  do fs <- flatten_seq_block s;
  ret (fold_seq_block (clock_assignments fs)).

Program Definition transf_module (m: DHTL.module) : Errors.res DHTL.module :=
  do dp <- PTree.fold (fun b i a =>
             do tb <- b;
             do a' <- clock_stmnt_assignments a;
             ret (PTree.set i a' tb)) m.(mod_datapath) (Errors.OK (PTree.empty _));
  ret (mkmodule m.(mod_params)
    dp
    m.(mod_entrypoint)
    m.(mod_st)
    m.(mod_stk)
    m.(mod_stk_len)
    m.(mod_finish)
    m.(mod_return)
    m.(mod_start)
    m.(mod_reset)
    m.(mod_clk)
    m.(mod_scldecls)
    m.(mod_arrdecls)
    m.(mod_ram) 
    _
    m.(mod_ordering_wf)
    m.(mod_ram_wf)
    m.(mod_params_wf)).
Next Obligation.
Admitted.

Definition transf_fundef := transf_partial_fundef transf_module.

Definition transf_program (p : DHTL.program) : Errors.res DHTL.program :=
  transform_partial_program transf_fundef p.
