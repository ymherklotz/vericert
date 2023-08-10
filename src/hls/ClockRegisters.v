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
Require Import vericert.common.Monad.
Require Import vericert.common.Optionmonad.
Require vericert.hls.Verilog.

Import OptionExtra.

#[local] Open Scope monad_scope.

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
| FVvar : lhs -> flat_expr
| FVbinop : Verilog.binop -> flat_expr -> flat_expr -> flat_expr
| FVunop : Verilog.unop -> flat_expr -> flat_expr
| FVternary : flat_expr -> flat_expr -> flat_expr -> flat_expr
.

Inductive flat_stmnt : Type :=
| FVblock : lhs -> flat_expr -> flat_stmnt
| FVnonblock : lhs -> flat_expr -> flat_stmnt
.

Fixpoint flatten_expr (preg: reg) (e: Verilog.expr) : option flat_expr :=
  match e with
  | Verilog.Vlit v => Some (FVlit v)
  | Verilog.Vvar r => Some (FVvar (LhsReg r))
  | Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2) =>
    if Pos.eqb preg r && Int.eq i1 i2 then
      match Int.unsigned i1 with
      | Zpos p => Some (FVvar (LhsPred p))
      | _ => None
      end
    else None
  | Verilog.Vunop u e => 
    match flatten_expr preg e with
    | Some fe => Some (FVunop u fe)
    | _ => None
    end
  | Verilog.Vbinop u e1 e2 => 
    match flatten_expr preg e1, flatten_expr preg e2 with
    | Some fe1, Some fe2 => Some (FVbinop u fe1 fe2)
    | _, _ => None
    end
  | Verilog.Vternary e1 e2 e3 => 
    match flatten_expr preg e1, flatten_expr preg e2, flatten_expr preg e3 with
    | Some fe1, Some fe2, Some fe3 => Some (FVternary fe1 fe2 fe3)
    | _, _, _ => None
    end
  | _ => None
  end.

Fixpoint flatten_seq_block (preg: reg) (s: Verilog.stmnt) : option (list flat_stmnt) := 
  match s with
  | Verilog.Vskip => Some nil
  | Verilog.Vseq s1 s2 =>
    match flatten_seq_block preg s1, flatten_seq_block preg s2 with
    | Some s1', Some s2' => 
      Some (s1' ++ s2')
    | _, _ => None
    end
  | Verilog.Vblock (Verilog.Vvar r) e => 
    match flatten_expr preg e with 
    | Some fe => Some (FVblock (LhsReg r) fe :: nil)
    | _ => None
    end
  | Verilog.Vblock (Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2)) e => 
    if Pos.eqb preg r && Int.eq i1 i2 then
      match Int.unsigned i1, flatten_expr preg e with 
      | Zpos p, Some fe => Some (FVblock (LhsPred p) fe :: nil)
      | _, _ => None
      end
    else None
  | Verilog.Vnonblock (Verilog.Vvar r) e => 
    match flatten_expr preg e with 
    | Some fe => Some (FVnonblock (LhsReg r) fe :: nil)
    | _ => None
    end
  | Verilog.Vnonblock (Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2)) e => 
    if Pos.eqb preg r && Int.eq i1 i2 then
      match Int.unsigned i1, flatten_expr preg e with 
      | Zpos p, Some fe => Some (FVnonblock (LhsPred p) fe :: nil)
      | _, _ => None
      end
    else None
  | _ => None
  end.

Fixpoint expand_expr (preg: reg) (f: flat_expr): Verilog.expr :=
  match f with
  | FVlit l => Verilog.Vlit l
  | FVvar (LhsReg r) => Verilog.Vvar r
  | FVvar (LhsPred p) => Verilog.Vrange preg (Verilog.Vlit (Int.repr (Zpos p))) (Verilog.Vlit (Int.repr (Zpos p)))
  | FVbinop b e1 e2 => Verilog.Vbinop b (expand_expr preg e1) (expand_expr preg e2)
  | FVunop b e => Verilog.Vunop b (expand_expr preg e)
  | FVternary e1 e2 e3 => Verilog.Vternary (expand_expr preg e1) (expand_expr preg e2) (expand_expr preg e3)
  end.

Definition expand_assignment (preg: reg) (f: flat_stmnt): Verilog.stmnt := 
  match f with
  | FVblock (LhsReg r) e => Verilog.Vblock (Verilog.Vvar r) (expand_expr preg e)
  | FVnonblock (LhsReg r) e => Verilog.Vnonblock (Verilog.Vvar r) (expand_expr preg e)
  | FVblock (LhsPred p) e => 
    Verilog.Vblock (Verilog.Vrange preg (Verilog.Vlit (Int.repr (Zpos p))) 
      (Verilog.Vlit (Int.repr (Zpos p)))) (expand_expr preg e)
  | FVnonblock (LhsPred p) e => 
    Verilog.Vnonblock (Verilog.Vrange preg (Verilog.Vlit (Int.repr (Zpos p))) 
      (Verilog.Vlit (Int.repr (Zpos p)))) (expand_expr preg e)
  end.

Definition fold_seq_block (preg: reg) (s: list flat_stmnt): Verilog.stmnt :=
  fold_left (fun a b => Verilog.Vseq a (expand_assignment preg b)) s Verilog.Vskip.

Fixpoint clock_expr (t: RTree.t flat_expr) (f: flat_expr): flat_expr :=
  match f with
  | FVvar r => 
    match RTree.get r t with
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
    (RTree.set r fe t, l ++ (FVnonblock r fe :: nil))
  | _ => (t, l ++ (f :: nil))
  end.

Definition clock_assignments (s: list flat_stmnt): list flat_stmnt :=
  snd (fold_left clock_assignment s (RTree.empty _, nil)).

Definition clock_stmnt_assignments (preg: reg) (s: Verilog.stmnt): option Verilog.stmnt :=
  match flatten_seq_block preg s with
  | Some fs => Some (fold_seq_block preg (clock_assignments fs))
  | None => None
  end.

Program Definition transf_module (m: DHTL.module) : option DHTL.module :=
  match (PTree.fold (fun b i a => 
           match b, clock_stmnt_assignments m.(mod_preg) a with 
           | Some tb, Some a' => Some (PTree.set i a' tb)
           | _, _ => None
           end)) m.(mod_datapath) (Some (PTree.empty _)) with
  | Some dp =>
    Some (mkmodule m.(mod_params)
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
      m.(mod_preg)
      m.(mod_scldecls)
      m.(mod_arrdecls)
      m.(mod_ram) 
      _
      m.(mod_ordering_wf)
      m.(mod_ram_wf)
      m.(mod_params_wf))
  | _ => None
  end.
Next Obligation.
Admitted.

Definition transl_module (m : DHTL.module) : Errors.res DHTL.module :=
  Verilog.handle_opt (Errors.msg "ClockRegisters: not translated") (transf_module m).

Definition transl_fundef := transf_partial_fundef transl_module.

Definition transl_program (p : DHTL.program) : Errors.res DHTL.program :=
  transform_partial_program transl_fundef p.
