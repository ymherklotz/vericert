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

val pprint_stmnt : int -> Verilog.stmnt -> string

val pprint_expr : Verilog.expr -> string

val print_value : out_channel -> ValueInt.value -> unit

val print_program : bool -> out_channel -> Verilog.program -> unit

val print_result : out_channel -> (BinNums.positive * ValueInt.value) list -> unit

val print_io : Verilog.io option -> (string * bool)
