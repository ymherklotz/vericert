(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *               2021 Michalis Pardalos <mpardalos@gmail.com>
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
Require Import compcert.common.Errors.

Require Import vericert.common.Maps.
Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.HTL.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Import ListNotations.

Local Open Scope error_monad_scope.

Record renumber_state: Type :=
  mk_renumber_state {
    st_freshreg : reg;
    st_regmap : PTree.t reg;
  }.

Module RenumberState <: State.
  Definition st := renumber_state.

  Definition st_prop (st1 st2 : st) := True.

  Lemma st_refl : forall (s : st), st_prop s s.
  Proof. constructor. Qed.

  Lemma st_trans : forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
  Proof. constructor. Qed.
End RenumberState.

Module VerilogMonad := Statemonad(RenumberState).

Module VerilogMonadExtra := Monad.MonadExtra(VerilogMonad).

Section RENUMBER.
  Export RenumberState.
  Export VerilogMonad.
  Import VerilogMonadExtra.
  Export MonadNotation.

  Definition renumber_reg (r : reg) : mon reg :=
    do st <- get;
    match PTree.get r st.(st_regmap) with
    | Some reg' => ret reg'
    | None =>
      do tt <- set (mk_renumber_state (Pos.succ st.(st_freshreg)) (PTree.set r st.(st_freshreg) st.(st_regmap))) (fun _ => I);
      ret st.(st_freshreg)
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
    | Vrange r e1 e2 =>
      do e1' <- renumber_expr e1;
      do e2' <- renumber_expr e2;
      do r' <- renumber_reg r;
      ret (Vrange r e1 e2)
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
    do mod_body' <- traverselist renumber_module_item (Verilog.mod_body m);

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

  Definition renumber_all_modules
             (modules : PTree.t Verilog.module)
             (start_reg : reg)
             (clk : reg) : Errors.res (PTree.t Verilog.module) :=

    run_mon (mk_renumber_state start_reg (PTree.empty reg))
            (VerilogMonadExtra.traverse_ptree1 (fun m =>
                  do st <- VerilogMonad.get;
                  do _ <- VerilogMonad.set
                       (mk_renumber_state (st_freshreg st)
                                          (PTree.set (mod_clk m) clk
                                                     (PTree.empty reg)))
                       (fun _ => I);
                  renumber_module m)
           modules).
End RENUMBER.


Section TRANSLATE.
  Local Open Scope error_monad_scope.

  Definition transl_datapath_fun (modmap : PTree.t Verilog.module) (a : Verilog.node * HTL.datapath_stmnt) :=
    let (n, s) := a in
    let node := Verilog.Vlit (posToValue n) in
    match s with
    | HTL.HTLfork mod_name args =>
      do m <- handle_opt (Errors.msg "module does not exist") (modmap ! mod_name);
      let reset_mod := Vnonblock (Vvar (Verilog.mod_reset m)) (posToLit 1) in
      let zipped_args := List.combine (Verilog.mod_args m) args in
      let assign_args :=
          List.fold_left (fun (acc : stmnt) (a : reg * reg) => let (to, from) := a in
                                                            Vseq acc (Vnonblock (Vvar to) (Vvar from)))
                         zipped_args Vskip in
      OK (node, Vseq reset_mod assign_args)
    | HTL.HTLjoin mod_name dst =>
      do m <- handle_opt (Errors.msg "module does not exist") (modmap ! mod_name);
      let set_result := Vnonblock (Vvar dst) (Vvar (Verilog.mod_return m)) in
      let stop_reset := Vnonblock (Vvar (Verilog.mod_reset m)) (Vlit (ZToValue 0)) in
      OK (node, Vseq stop_reset set_result)
    | HTL.HTLDataVstmnt s => OK (node, s)
    end.

  Definition transl_datapath modmap st := Errors.mmap (transl_datapath_fun modmap) st.

  Definition transl_ctrl_fun (modmap : PTree.t Verilog.module) (a : Verilog.node * HTL.control_stmnt) : Errors.res (Verilog.expr * Verilog.stmnt):=
    let (n, s) := a in
    let node := Verilog.Vlit (posToValue n) in
    match s with
    | HTL.HTLwait mod_name status expr =>
      do mod_body <- handle_opt (Errors.msg "module does not exist") (PTree.get mod_name modmap);
      let is_done := Vbinop Veq (Vvar (Verilog.mod_finish mod_body)) (Vlit (posToValue 1)) in
      let continue := Vnonblock (Vvar status) expr in
      Errors.OK (node, Verilog.Vcond is_done continue Vskip)
    | HTL.HTLCtrlVstmnt s => Errors.OK (node, s)
    end.

  Definition transl_ctrl modmap st := Errors.mmap (transl_ctrl_fun modmap) st.

  Definition scl_to_Vdecl_fun (a : reg * (option Verilog.io * Verilog.scl_decl)) :=
    match a with (r, (io, Verilog.VScalar sz)) => (Verilog.Vdecl io r sz) end.

  Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

  Definition arr_to_Vdeclarr_fun (a : reg * (option Verilog.io * Verilog.arr_decl)) :=
    match a with (r, (io, Verilog.VArray sz l)) => (Verilog.Vdeclarr io r sz l) end.

  Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

  Definition called_functions (stmnts : list (Verilog.node * HTL.datapath_stmnt)) : list ident :=
    List.nodup Pos.eq_dec (Option.map_option (fun (a : (positive * HTL.datapath_stmnt)) =>
                                   let (n, stmt) := a in
                                   match stmt with
                                   | HTL.HTLfork fn _ => Some fn
                                   | _ => None
                                   end) stmnts).

  Definition find_module (program : HTL.program) (name : ident) : Errors.res HTL.module :=
    match option_map snd (find (fun named_module => Pos.eqb (fst named_module) name) program.(prog_defs)) with
    | Some (Gfun (Internal f)) => OK f
    | _ => Error (msg "Veriloggen: Could not find definition for called module")
    end.

  Definition max_reg_module (m : HTL.module) : positive :=
    fold_left Pos.max (
    [ HTL.mod_st m
    ; HTL.mod_stk m
    ; HTL.mod_finish m
    ; HTL.mod_return m
    ; HTL.mod_start m
    ; HTL.mod_reset m
    ; HTL.mod_clk m
    ] ++ HTL.mod_params m ++ map fst (PTree.elements (mod_scldecls m)) ++ map fst (PTree.elements (mod_arrdecls m))) 1%positive.

  Definition prog_modmap (p : HTL.program) :=
    PTree_Properties.of_list (Option.map_option
                            (fun a => match a with
                                   | (ident, (Gfun (Internal f))) => Some (ident, f)
                                   | _ => None
                                   end)
                            p.(prog_defs)).

  (** Clean up declarations for an inlined module. Make IO decls into reg, and remove the clk declaration *)
  Definition clean_up_decl (clk : reg) (it : Verilog.module_item) :=
    match it with
    | Vdeclaration (Vdecl (Some _) reg sz) =>
      if Pos.eqb reg clk
      then None
      else Some (Vdeclaration (Vdecl None reg sz))
    | Vdeclaration (Vdeclarr (Some _) reg sz len) =>
      Some (Vdeclaration (Vdeclarr None reg sz len))
    | _ => Some it
    end.

  (* FIXME Remove the fuel parameter (recursion limit)*)
  Fixpoint transf_module (fuel : nat) (program : HTL.program) (m : HTL.module) : res Verilog.module :=
    match fuel with
    | O => Error (msg "Veriloggen: transf_module recursion too deep")
    | S fuel' =>

      let inline_start_reg := max_reg_module m in
      let inline_names := called_functions (PTree.elements (HTL.mod_datapath m)) in
      let htl_modules := PTree.filter
                       (fun m _ => List.existsb (Pos.eqb m) inline_names)
                       (prog_modmap program) in
      do translated_modules <- PTree.traverse (fun _ => transf_module fuel' program) htl_modules;
      do renumbered_modules <- renumber_all_modules translated_modules (max_reg_module m) (HTL.mod_clk m);
      let cleaned_modules := PTree.map1 (map_body (Option.map_option (clean_up_decl (HTL.mod_clk m))))
                                        renumbered_modules in

      do case_el_ctrl <- transl_ctrl renumbered_modules (PTree.elements (HTL.mod_controllogic m));
      do case_el_data <- transl_datapath renumbered_modules (PTree.elements (HTL.mod_datapath m));

      let body : list Verilog.module_item:=
          Valways (Vposedge (HTL.mod_clk m)) (Vcond (Vbinop Veq (Vvar (HTL.mod_reset m)) (Vlit (ZToValue 1)))
                                                    (Vseq
                                                      (Vnonblock (Vvar (HTL.mod_st m)) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                                      (Vnonblock (Vvar (HTL.mod_finish m)) (Vlit (ZToValue 0))))
                                                    (Vcase (Vvar (HTL.mod_st m)) case_el_ctrl (Some Vskip)))
                  :: Valways (Vposedge (HTL.mod_clk m)) (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip))
                  :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements (HTL.mod_arrdecls m))
                                                           ++ scl_to_Vdecl (AssocMap.elements (HTL.mod_scldecls m)))
                  ++ List.flat_map Verilog.mod_body (List.map snd (PTree.elements cleaned_modules)) in

      OK (Verilog.mkmodule
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

  Definition transl_fundef (prog : HTL.program) := transf_partial_fundef (transf_module 10 prog).
  Definition transl_program (prog : HTL.program) := transform_partial_program (transl_fundef prog) prog.

End TRANSLATE.
