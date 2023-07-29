(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

From vericert Require
     Verilog
     Compiler
     GibleSeqgen
     GibleSeq
     GiblePar
     Gible
     HTLgen
     (*Pipeline*)
     HLSOpts
     Predicate
     Bourdoncle
.

From Coq Require DecidableClass.

From compcert Require
    Coqlib
    Wfsimpl
    Decidableplus
    AST
    Iteration
    Floats
    SelectLong
    Selection
    RTLgen
    Inlining
    ValueDomain
    Tailcall
    Allocation
    Bounds
    Ctypes
    Csyntax
    Ctyping
    Clight
    Compiler
    Parser
    Initializers.

From cohpred_theory Require
    Smtpredicate.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOCamlInt63.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Decidable *)

Extraction Inline DecidableClass.Decidable_witness DecidableClass.decide
   Decidableplus.Decidable_and Decidableplus.Decidable_or
   Decidableplus.Decidable_not Decidableplus.Decidable_implies.

(* Wfsimpl *)
Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* Selection *)

Extract Constant Selection.compile_switch => "Switchaux.compile_switch".
Extract Constant Selection.if_conversion_heuristic => "Selectionaux.if_conversion_heuristic".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".
Extract Inlined Constant Inlining.inlining_info => "Inliningaux.inlining_info".
Extract Inlined Constant Inlining.inlining_analysis => "Inliningaux.inlining_analysis".
Extraction Inline Inlining.ret Inlining.bind.

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
Extract Constant Compopts.optim_for_size =>
  "fun _ -> !Clflags.option_Osize".
Extract Constant Compopts.va_strict =>
  "fun _ -> false".
Extract Constant Compopts.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Compopts.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".
Extract Constant Compopts.optim_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".
Extract Constant Compopts.optim_constprop =>
  "fun _ -> !Clflags.option_fconstprop".
Extract Constant Compopts.optim_CSE =>
  "fun _ -> !Clflags.option_fcse".
Extract Constant Compopts.optim_redundancy =>
  "fun _ -> !Clflags.option_fredundancy".
Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".

Extract Constant HLSOpts.optim_if_conversion =>
  "fun _ -> !VericertClflags.option_fif_conv".
Extract Constant HLSOpts.optim_ram =>
  "fun _ -> !VericertClflags.option_fram".

(* Compiler *)
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant driver.Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_GibleSeq => "PrintGibleSeq.print_if".
Extract Constant Compiler.print_GiblePar => "PrintGiblePar.print_if".
Extract Constant Compiler.print_HTL => "PrintHTL.print_if".
Extract Constant Compiler.print_DHTL => "PrintDHTL.print_if".
Extract Constant Compiler.print_LTL => "PrintLTL.print_if".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
Extract Constant Compiler.time  => "Timing.time_coq".

Extract Constant Vericertlib.debug_print => "print_newline".

(*Extraction Inline Compiler.apply_total Compiler.apply_partial.*)

(* Cabs *)
Extract Constant Cabs.loc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Inlined Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

(* Processor-specific extraction directives *)

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int Uint63.

(* Cutting the dependency to R. *)
Extract Inlined Constant Defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Binary.FF2R => "fun _ -> assert false".
Extract Inlined Constant Binary.B2R => "fun _ -> assert false".
Extract Inlined Constant Bracket.inbetween_loc => "fun _ -> assert false".

(*Extract Constant Pipeline.pipeline => "pipelining.pipeline".*)
Extract Constant GibleSeqgen.partition => "Partition.partition".
Extract Constant GiblePargen.schedule => "Schedule.schedule_fn".
Extract Constant Abstr.print_forest => "(PrintAbstr.print_forest stdout)".

Extract Constant Smtpredicate.pred_verit_unsat => "Cohpred.smt_certificate".

(* Loop normalization *)
Extract Constant IfConversion.build_bourdoncle => "BourdoncleAux.build_bourdoncle".
(*Extract Constant IfConversion.get_if_conv_t => "(fun _ -> [Maps.PTree.empty; Maps.PTree.empty; Maps.PTree.empty])".*)

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

Cd "src/extraction".
Separate Extraction
         Verilog.module vericert.Compiler.transf_hls
         vericert.Compiler.transf_hls_temp
         GibleSeqgen.transl_program Gible.successors_instr
         HTLgen.tbl_to_case_expr
         Predicate.sat_pred_simple
         Verilog.stmnt_to_list
         Bourdoncle.bourdoncle

   Smtpredicate.check_smt_total

   Compiler.transf_c_program Compiler.transf_cminor_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Ctypes.merge_attributes Ctypes.remove_attributes 
   Ctypes.build_composite_env Ctypes.layout_struct
   Initializers.transl_init Initializers.constval
   Csyntax.Eindex Csyntax.Epreincr Csyntax.Eselection
   Ctyping.typecheck_program
   Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
   Ctyping.eselection
   Ctypes.make_program
   Clight.type_of_function
   Conventions1.callee_save_type Conventions1.is_float_reg
   Conventions1.int_caller_save_regs Conventions1.float_caller_save_regs
   Conventions1.int_callee_save_regs Conventions1.float_callee_save_regs
   Conventions1.dummy_int_reg Conventions1.dummy_float_reg
   Conventions1.allocatable_registers
   RTL.instr_defs RTL.instr_uses
   Machregs.mregs_for_operation Machregs.mregs_for_builtin
   Machregs.two_address_op Machregs.is_stack_reg
   Machregs.destroyed_at_indirect_call
   AST.signature_main
   Floats.Float32.from_parsed Floats.Float.from_parsed
   Globalenvs.Senv.invert_symbol
   Parser.translation_unit_file.
