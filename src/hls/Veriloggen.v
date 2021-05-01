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

Section APPLY_MAPPING.
  Local Open Scope assocmap.
  Local Open Scope error_monad_scope.

  Variable externctrl : AssocMap.t (ident * controlsignal).
  Variable modmap : PTree.t HTL.module.

  Definition get_mod_signal (m : HTL.module) (signal : HTL.controlsignal) :=
    match signal with
    | ctrl_finish => OK (HTL.mod_finish m)
    | ctrl_return => OK (HTL.mod_return m)
    | ctrl_start => OK (HTL.mod_start m)
    | ctrl_reset => OK (HTL.mod_reset m)
    | ctrl_clk => OK (HTL.mod_clk m)
    | ctrl_param idx =>
      match List.nth_error (HTL.mod_params m) idx with
      | Some r => OK r
      | None => Error (msg "Module does not have nth parameter")
      end
    end.

  Definition reg_apply_map (r : Verilog.reg) : res reg :=
    match externctrl ! r with
    | None => OK r
    | Some (m, signal) =>
      match modmap ! m with
      | None => Error (msg "Veriloggen: Could not find definition for called module")
      | Some othermod => get_mod_signal othermod signal
      end
    end.

  Fixpoint expr_apply_map (expr : Verilog.expr) {struct expr} : res Verilog.expr :=
    match expr with
    | Vlit n =>
      OK (Vlit n)
    | Vvar r =>
      do r' <- reg_apply_map r;
      OK (Vvar r')
    | Vvari r e =>
      do r' <- reg_apply_map r;
      do e' <- expr_apply_map e;
      OK (Vvari r e)
    | Vrange r e1 e2 =>
      do r' <- reg_apply_map r;
      do e1' <- expr_apply_map e1;
      do e2' <- expr_apply_map e2;
      OK (Vrange r' e1' e2')
    | Vinputvar r =>
      do r' <- reg_apply_map r;
      OK (Vinputvar r')
    | Vbinop op e1 e2 =>
      do e1' <- expr_apply_map e1;
      do e2' <- expr_apply_map e2;
      OK (Vbinop op e1' e2')
    | Vunop op e =>
      do e' <- expr_apply_map e;
      OK (Vunop op e')
    | Vternary e1 e2 e3 =>
      do e1' <- expr_apply_map e1;
      do e2' <- expr_apply_map e2;
      do e3' <- expr_apply_map e3;
      OK (Vternary e1' e2' e3')
    end.

  Definition mmap_option {A B} (f : A -> res B) (opt : option A) : res (option B) :=
    match opt with
    | None => OK None
    | Some a => do a' <- f a; OK (Some a')
    end.

  Definition cases_apply_map_ (stmnt_apply_map_ : Verilog.stmnt -> res Verilog.stmnt) :=
    fix cases_apply_map (cs : list (Verilog.expr * Verilog.stmnt)) :=
      match cs with
      | nil => OK nil
      | (c_e, c_s) :: tl =>
        do c_e' <- expr_apply_map c_e;
        do c_s' <- stmnt_apply_map_ c_s;
        do tl' <- cases_apply_map tl;
        OK ((c_e', c_s') :: tl')
      end.

  Fixpoint stmnt_apply_map (stmnt : Verilog.stmnt) {struct stmnt} : res Verilog.stmnt :=
    match stmnt with
    | Vskip => OK Vskip
    | Vseq s1 s2 =>
      do s1' <- stmnt_apply_map s1;
      do s2' <- stmnt_apply_map s2;
      OK (Vseq s1' s2')
    | Vcond e s1 s2 =>
      do e' <- expr_apply_map e;
      do s1' <- stmnt_apply_map s1;
      do s2' <- stmnt_apply_map s2;
      OK (Vcond e' s1' s2')
    | Vcase e cases def =>
      do e' <- expr_apply_map e;
      do cases' <- cases_apply_map_ stmnt_apply_map cases;
      do def' <- mmap_option (fun x => stmnt_apply_map x) def;
      OK (Vcase e' cases' def')
    | Vblock e1 e2 =>
      do e1' <- expr_apply_map e1;
      do e2' <- expr_apply_map e2;
      OK (Vblock e1' e2')
    | Vnonblock e1 e2 =>
      do e1' <- expr_apply_map e1;
      do e2' <- expr_apply_map e2;
      OK (Vnonblock e1' e2')
    end.

  (* Unused. Defined for completeness *)
  Definition cases_apply_map := cases_apply_map_ stmnt_apply_map.
End APPLY_MAPPING.

Section TRANSLATE.
  Local Open Scope error_monad_scope.

  Definition transl_datapath_fun externctrl modmap (a : Verilog.node * HTL.datapath_stmnt) :=
    let (n, s) := a in
    let node := Verilog.Vlit (posToValue n) in
    do stmnt <- stmnt_apply_map externctrl modmap s;
    OK (node, stmnt).

  Definition transl_datapath externctrl modmap st := Errors.mmap (transl_datapath_fun externctrl modmap) st.

  Definition transl_ctrl_fun externctrl modmap (a : Verilog.node * HTL.control_stmnt) : Errors.res (Verilog.expr * Verilog.stmnt):=
    let (n, s) := a in
    let node := Verilog.Vlit (posToValue n) in
    do stmnt <- stmnt_apply_map externctrl modmap s;
    OK (node, stmnt).

  Definition transl_ctrl externctrl modmap st := Errors.mmap (transl_ctrl_fun externctrl modmap) st.

  Definition scl_to_Vdecl_fun (a : reg * (option Verilog.io * Verilog.scl_decl)) :=
    match a with (r, (io, Verilog.VScalar sz)) => (Verilog.Vdecl io r sz) end.

  Definition scl_to_Vdecl scldecl := map scl_to_Vdecl_fun scldecl.

  Definition arr_to_Vdeclarr_fun (a : reg * (option Verilog.io * Verilog.arr_decl)) :=
    match a with (r, (io, Verilog.VArray sz l)) => (Verilog.Vdeclarr io r sz l) end.

  Definition arr_to_Vdeclarr arrdecl := map arr_to_Vdeclarr_fun arrdecl.

  Definition called_functions (main_name : ident) (m : HTL.module) : list ident :=
    (* remove duplicates *)
    List.nodup Pos.eq_dec
               (* Take just the module name *)
               (List.map (Basics.compose fst snd)
                         (* Remove the main module if it's referenced *)
                         (List.filter (fun it => negb (Pos.eqb (fst (snd it)) main_name))
                                      (PTree.elements (HTL.mod_externctrl m)))).

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
  Fixpoint transf_module (fuel : nat) (prog : HTL.program) (externclk : option reg) (m : HTL.module) : res Verilog.module :=
    match fuel with
    | O => Error (msg "Veriloggen: transf_module recursion too deep")
    | S fuel' =>

      let inline_start_reg := max_reg_module m in
      let inline_names := called_functions (AST.prog_main prog) m in
      let modmap := prog_modmap prog in
      let htl_modules := PTree.filter
                       (fun m _ => List.existsb (Pos.eqb m) inline_names)
                       modmap in
      do translated_modules <- PTree.traverse (fun _ => transf_module fuel' prog externclk) htl_modules;
      let cleaned_modules := PTree.map1 (map_body (Option.map_option (clean_up_decl (HTL.mod_clk m))))
                                        translated_modules in


      do case_el_ctrl <- transl_ctrl (HTL.mod_externctrl m) modmap (PTree.elements (HTL.mod_controllogic m));
      do case_el_data <- transl_datapath (HTL.mod_externctrl m) modmap (PTree.elements (HTL.mod_datapath m));

      let externctrl := HTL.mod_externctrl m in
      do rst <- reg_apply_map externctrl modmap (HTL.mod_reset m);
      do st <- reg_apply_map externctrl modmap (HTL.mod_st m);
      do finish <- reg_apply_map externctrl modmap (HTL.mod_finish m);
      let clk := match externclk with
                 | None => HTL.mod_clk m
                 | Some c => c
                 end in
      let clk_decl := scl_to_Vdecl_fun (clk, (Some Vinput, VScalar 1)) in

      let body : list Verilog.module_item:=
          Valways (Vposedge clk) (Vcond (Vbinop Veq (Vvar rst) (Vlit (ZToValue 1)))
                                                    (Vseq
                                                      (Vnonblock (Vvar st) (Vlit (posToValue (HTL.mod_entrypoint m))))
                                                      (Vnonblock (Vvar finish) (Vlit (ZToValue 0))))
                                                    (Vcase (Vvar st) case_el_ctrl (Some Vskip)))
                  :: Valways (Vposedge clk) (Vcase (Vvar (HTL.mod_st m)) case_el_data (Some Vskip))
                  :: Vdeclaration clk_decl
                  :: List.map Vdeclaration (arr_to_Vdeclarr (AssocMap.elements (HTL.mod_arrdecls m))
                                                           ++ scl_to_Vdecl (AssocMap.elements (HTL.mod_scldecls m)))
                  ++ List.flat_map Verilog.mod_body (List.map snd (PTree.elements cleaned_modules)) in

      OK (Verilog.mkmodule
               (HTL.mod_start m)
               (HTL.mod_reset m)
               (HTL.mod_finish m)
               clk
               (HTL.mod_return m)
               (HTL.mod_st m)
               (HTL.mod_stk m)
               (HTL.mod_stk_len m)
               (HTL.mod_params m)
               body
               (HTL.mod_entrypoint m)
                )
    end.

  Definition transl_fundef (prog : HTL.program) := transf_partial_fundef (transf_module 10 prog None).
  Definition transl_program (prog : HTL.program) := transform_partial_program (transl_fundef prog) prog.

End TRANSLATE.
