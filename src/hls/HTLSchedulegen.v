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
From compcert Require Errors Globalenvs Integers.
From compcert Require Import AST.
From vericert Require Import RTLBlock Verilog HTL Vericertlib AssocMap ValueInt Statemonad.

Parameter transl_module : function -> Errors.res module.

Definition transl_fundef := transf_partial_fundef transl_module.

Definition main_is_internal (p : RTLBlock.program) : bool :=
  let ge := Globalenvs.Genv.globalenv p in
  match Globalenvs.Genv.find_symbol ge p.(AST.prog_main) with
  | Some b =>
    match Globalenvs.Genv.find_funct_ptr ge b with
    | Some (AST.Internal _) => true
    | _ => false
    end
  | _ => false
  end.

Definition transl_program (p : RTLBlock.program) : Errors.res HTL.program :=
  if main_is_internal p
  then transform_partial_program transl_fundef p
  else Errors.Error (Errors.msg "Main function is not Internal.").
