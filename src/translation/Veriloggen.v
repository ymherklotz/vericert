(*
 * Vericert: Verified high-level synthesis.
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

From compcert Require Import Maps.
From compcert Require Import Errors.
From compcert Require Import AST.
From vericert Require Import Vericertlib AssocMap ValueInt Statemonad.
From vericert Require Import HTL Verilog.

Record state: Type := mkstate {
                  st_freshreg : reg;
                  st_regmap : PTree.t reg;
                    }.

Module VerilogState <: State.
  Definition st := state.

  Definition st_prop (st1 st2 : state) := True.

  Lemma st_refl : forall (s : state), st_prop s s.
  Proof. constructor. Qed.

  Lemma st_trans : forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
  Proof. constructor. Qed.
End VerilogState.
Export VerilogState.

Module VerilogMonad := Statemonad(VerilogState).
Export VerilogMonad.

Module VerilogMonadExtra := Monad.MonadExtra(VerilogMonad).
Import VerilogMonadExtra.
Export MonadNotation.

Definition renumber_reg (r : reg) : mon reg :=
  do st <- get;
  match PTree.get r st.(st_regmap) with
  | Some reg' => ret reg'
  | None =>
    do _ <- set (mkstate (Pos.succ st.(st_freshreg)) st.(st_regmap)) (fun _ => I);
    ret st.(st_freshreg)
  end.

Definition transl_datapath_fun (a : Verilog.node * HTL.datapath_stmnt) :=
  let (n, s) := a in
  (Verilog.Vlit (posToValue n),
   match s with
   | HTL.HTLcall m args dst => Verilog.Vskip (* inline_call m args *)
   | HTL.HTLVstmnt s => s
   end).

Definition transl_datapath st := map transl_datapath_fun st.

Definition transl_ctrl_fun (a : Verilog.node * Verilog.stmnt) :=
  let (n, stmnt) := a
  in (Verilog.Vlit (posToValue n), stmnt).

Definition transl_ctrl st := map transl_ctrl_fun st.

Definition scl_to_Vdecl_fun (a : reg * (option Verilog.io * Verilog.scl_decl)) :=
  match a with (r, (io, Verilog.VScalar sz)) => (Verilog.Vdecl io r sz) end.

Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

Definition arr_to_Vdeclarr_fun (a : reg * (option Verilog.io * Verilog.arr_decl)) :=
  match a with (r, (io, Verilog.VArray sz l)) => (Verilog.Vdeclarr io r sz l) end.

Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

Definition find_module (program : HTL.program) (name : ident) : mon HTL.module :=
  match option_map snd (find (fun named_module => Pos.eqb (fst named_module) name) program.(prog_defs)) with
  | Some (Gfun (Internal f)) => ret f
  | _ => error (Errors.msg "Veriloggen: Could not find definition for called module")
  end.

Fixpoint renumber_edge (edge : Verilog.edge) :=
  match edge with
  | Vposedge r =>
    do r' <- renumber_reg r;
    ret (Vposedge r')
  | Vnegedge r =>
    do r' <- renumber_reg r;
    ret (Vposedge r')
  | Valledge => ret Valledge
  | Voredge e1 e2 =>
    do e1' <- renumber_edge e1;
    do e2' <- renumber_edge e2;
    ret (Voredge e1' e2')
  end.

Definition renumber_declaration (decl : Verilog.declaration) :=
  match decl with
  | Vdecl io reg sz =>
    do reg' <- renumber_reg reg;
    ret (Vdecl io reg' sz)
  | Vdeclarr io reg sz len =>
    do reg' <- renumber_reg reg;
    ret (Vdeclarr io reg' sz len)
  end.


Fixpoint renumber_expr (expr : Verilog.expr) :=
  match expr with
  | Vlit val => ret (Vlit val)
  | Vvar reg =>
    do reg' <- renumber_reg reg;
    ret (Vvar reg')
  | Vvari reg e =>
    do reg' <- renumber_reg reg;
    do e' <- renumber_expr e;
    ret (Vvari reg' e')
  | Vinputvar reg =>
    do reg' <- renumber_reg reg;
    ret (Vvar reg')
  | Vbinop op e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    ret (Vbinop op e1' e2')
  | Vunop op e =>
    do e' <- renumber_expr e;
    ret (Vunop op e)
  | Vternary e1 e2 e3 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    do e3' <- renumber_expr e3;
    ret (Vternary e1' e2' e3')
  end.

Fixpoint renumber_stmnt (stmnt : Verilog.stmnt) :=
  match stmnt with
  | Vskip => ret Vskip
  | Vseq s1 s2 =>
    do s1' <- renumber_stmnt s1;
    do s2' <- renumber_stmnt s2;
    ret (Vseq s1' s2')
  | Vcond e s1 s2 =>
    do e' <- renumber_expr e;
    do s1' <- renumber_stmnt s1;
    do s2' <- renumber_stmnt s2;
    ret (Vcond e' s1' s2')
  | Vcase e cs def =>
    do e' <- renumber_expr e;
    do cs' <- sequence (map
                            (fun (c : (Verilog.expr * Verilog.stmnt)) =>
                           let (c_expr, c_stmnt) := c in
                           do expr' <- renumber_expr c_expr;
                           do stmnt' <- renumber_stmnt c_stmnt;
                           ret (expr', stmnt')) cs);
    do def' <- match def with
              | None => ret None
              | Some d => do def' <- renumber_stmnt d; ret (Some def')
              end;
    ret (Vcase e' cs' def')
  | Vblock e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    ret (Vblock e1' e2')
  | Vnonblock e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    ret (Vnonblock e1' e2')
  end.

Definition renumber_module_item (item : Verilog.module_item) :=
  match item with
  | Vdeclaration decl =>
    do decl' <- renumber_declaration decl;
    ret (Vdeclaration decl')
  | Valways edge stmnt =>
    do edge' <- renumber_edge edge;
    do stmnt' <- renumber_stmnt stmnt;
    ret (Valways edge' stmnt')
  | Valways_ff edge stmnt =>
    do edge' <- renumber_edge edge;
    do stmnt' <- renumber_stmnt stmnt;
    ret (Valways edge' stmnt')
  | Valways_comb edge stmnt =>
    do edge' <- renumber_edge edge;
    do stmnt' <- renumber_stmnt stmnt;
    ret (Valways edge' stmnt')
  end.


Definition renumber_module (m : Verilog.module) : mon Verilog.module :=
  do mod_start' <- renumber_reg (Verilog.mod_start m);
  do mod_reset' <- renumber_reg (Verilog.mod_reset m);
  do mod_clk' <- renumber_reg (Verilog.mod_clk m);
  do mod_finish' <- renumber_reg (Verilog.mod_finish m);
  do mod_return' <- renumber_reg (Verilog.mod_return m);
  do mod_st' <- renumber_reg (Verilog.mod_st m);
  do mod_stk' <- renumber_reg (Verilog.mod_stk m);
  do mod_args' <- traverselist renumber_reg (Verilog.mod_args m);
  let mod_body' := (Verilog.mod_body m) in

  ret (Verilog.mkmodule
     mod_start'
     mod_reset'
     mod_clk'
     mod_finish'
     mod_return'
     mod_st'
     mod_stk'
     (Verilog.mod_stk_len m)
     mod_args'
     mod_body'
     (Verilog.mod_entrypoint m)).


Definition called_functions : (list (Verilog.node * HTL.datapath_stmnt)) -> list ident :=
  flat_map (fun (a : (positive * HTL.datapath_stmnt)) =>
          let (n, stmt) := a in
          match stmt with
          | HTL.HTLcall fn _ _ => fn::nil
          | _ => nil
          end).

(* FIXME Remove the fuel parameter (recursion limit)*)
Fixpoint transf_module (fuel : nat) (program : HTL.program) (m : HTL.module) : mon Verilog.module :=
  match fuel with
  | O => error (Errors.msg "Veriloggen: transl_module ran out of fuel")
  | S fuel' =>
    let case_el_ctrl := transl_ctrl (PTree.elements (HTL.mod_controllogic m)) in
    let case_el_data := transl_datapath (PTree.elements (HTL.mod_datapath m)) in

    (* Inlining *)
    let inline_names := called_functions (PTree.elements (HTL.mod_datapath m)) in
    do inline_modules <- traverselist (find_module program) inline_names;
    do translated_modules <- traverselist (transf_module fuel' program) inline_modules;
    do renumbered_modules <- traverselist renumber_module translated_modules;

    let body :=
        Valways (Vposedge (HTL.mod_clk m)) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                                  (Vnonblock (Vvar (HTL.mod_st m)) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                                  (Vcase (Vvar (HTL.mod_st m)) case_el_ctrl (Some Vskip)))
                :: Valways (Vposedge (HTL.mod_clk m)) (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip))
                :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements (HTL.mod_arrdecls m))
                                                         ++ scl_to_Vdecl (AssocMap.elements (HTL.mod_scldecls m)))
                ++ List.flat_map (fun m => (Verilog.mod_body m)) renumbered_modules in

    ret (Verilog.mkmodule
       (HTL.mod_start m)
       (HTL.mod_reset m)
       (HTL.mod_clk m)
       (HTL.mod_finish m)
       (HTL.mod_return m)
       (HTL.mod_st m)
       (HTL.mod_stk m)
       (HTL.mod_stk_len m)
       (HTL.mod_params m)
       body
       (HTL.mod_entrypoint m)
        )
  end.

Definition transl_module (prog : HTL.program) (m : HTL.module) :=
  run_mon (mkstate xH (PTree.empty reg)) (transf_module 10 prog m).

Definition transl_fundef (prog : HTL.program) := transf_partial_fundef (transl_module prog).
Definition transl_program (prog : HTL.program) := transform_partial_program (transl_fundef prog) prog.
