(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <git@yannherklotz.com>
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

open Printf
open Clflags
open Camlcoq
open Datatypes
open Coqlib
open Maps
open AST

type if_conv_t = (BinNums.positive * BinNums.positive) list PTree.t

(** [function_oracle func_data func] should implement the inlining definitions
    that are then provided to the verified algorithm. *)
let function_oracle func_data func = func_data

let fundefs_oracle current_data = function
  | (id, Gfun f) ->
     (match PTree.get id current_data with
      | Some func_data ->
         let result_data = function_oracle func_data f in
         PTree.set id result_data current_data
      | _ -> current_data)
  | _ -> current_data

let if_conversion_oracle prog : if_conv_t =
  List.fold_left fundefs_oracle PTree.empty prog.prog_defs
