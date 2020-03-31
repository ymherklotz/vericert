(* 
 * CoqUp: Verified high-level synthesis.
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

open Verilog
open Datatypes

open Camlcoq

open Printf

let concat = String.concat ""

let indent i = String.make (2 * i) ' '

let fold_map f s = List.map f s |> concat

let pstr pp = fprintf pp "%s"

let pprint_binop = function
  | Vadd -> " + "
  | Vsub -> " - "
  | Vmul -> " * "
  | Vdiv -> " / "
  | Vmod -> " % "
  | Vlt -> " < "
  | Vgt -> " > "
  | Vle -> " <= "
  | Vge -> " >= "
  | Veq -> " == "
  | Vne -> " != "
  | Vand -> " & "
  | Vor -> " | "
  | Vxor -> " ^ "
  | Vshl -> " << "
  | Vshr -> " >> "

let unop = function
  | Vneg -> " ~ "
  | Vnot -> " ! "

let register a = P.to_int a

let literal l = sprintf "%d'd%d" (Nat.to_int l.vsize) (Z.to_int (valueToZ l))

let rec pprint_expr = function
  | Vlit l -> literal l
  | Vvar s -> sprintf "reg_%d" (register s)
  | Vunop (u, e) -> concat ["("; unop u; pprint_expr e; ")"]
  | Vbinop (op, a, b) -> concat ["("; pprint_expr a; pprint_binop op; pprint_expr b; ")"]
  | Vternary (c, t, f) -> concat ["("; pprint_expr c; " ? "; pprint_expr t; " : "; pprint_expr f; ")"]

let rec pprint_stmnt i =
  let pprint_case (e, s) = concat [indent (i + 1); pprint_expr e; ":\n"; pprint_stmnt (i + 2) s]
  in function
  | Vskip -> concat [indent i; ";\n"]
  | Vseq s -> concat [indent i; "begin\n"; fold_map (pprint_stmnt (i+1)) s; indent i; "end\n"]
  | Vcond (e, st, sf) -> concat [indent i; "if ("; pprint_expr e; ")\n";
                                pprint_stmnt (i + 1) st; indent i; "else\n";
                                pprint_stmnt (i + 1) sf]
  | Vcase (e, es) -> concat [indent i; "case ("; pprint_expr e; ")\n";
                            fold_map pprint_case es; indent i; "endcase\n"]
  | Vblock (a, b) -> concat [indent i; pprint_expr a; " = "; pprint_expr b; ";\n"]
  | Vnonblock (a, b) -> concat [indent i; pprint_expr a; " <= "; pprint_expr b; ";\n"]

let print_program pp v = pstr pp (fold_map (pprint_stmnt 0) v)
