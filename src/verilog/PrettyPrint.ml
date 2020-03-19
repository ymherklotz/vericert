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

open Extraction.VerilogAST

let concat = String.concat ""

let indent i = String.make (2 * i) ' '

let fold_map f s = List.map f s |> concat

let rec pprint_value = function
  | VBool l -> if l then "1" else "0"
  (* Assume that array is flat if it's a literal, should probably be changed to a nat or int *)
  | VArray a -> concat [List.length a |> string_of_int; "'b"; fold_map pprint_value a]

let pprint_binop = function
  | Plus -> " + "
  | Minus -> " - "
  | Times -> " * "
  | Divide -> " / "
  | LT -> " < "
  | GT -> " > "
  | LE -> " <= "
  | GE -> " >= "
  | Eq -> " == "
  | And -> " & "
  | Or -> " | "
  | Xor -> " ^ "

let rec pprint_expr = function
  | Lit l -> pprint_value l
  | Var s -> List.to_seq s |> String.of_seq
  | Neg e -> concat ["(-"; pprint_expr e; ")"]
  | BinOp (op, a, b) -> concat ["("; pprint_expr a; pprint_binop op; pprint_expr b; ")"]
  | Ternary (c, t, f) -> concat ["("; pprint_expr c; " ? "; pprint_expr t; " : "; pprint_expr f; ")"]

let rec pprint_stmnt i =
  let pprint_case (e, s) = concat [indent (i + 1); pprint_expr e; ":\n"; pprint_stmnt (i + 2) s]
  in function
  | Skip -> concat [indent i; ";\n"]
  | Block s -> concat [indent i; "begin\n"; fold_map (pprint_stmnt (i+1)) s; indent i; "end\n"]
  | Cond (e, st, sf) -> concat [indent i; "if ("; pprint_expr e; ")\n";
                                pprint_stmnt (i + 1) st; indent i; "else\n";
                                pprint_stmnt (i + 1) sf]
  | Case (e, es) -> concat [indent i; "case ("; pprint_expr e; ")\n";
                            fold_map pprint_case es; indent i; "endcase\n"]
  | Blocking (a, b) -> concat [indent i; pprint_expr a; " = "; pprint_expr b; ";\n"]
  | Nonblocking (a, b) -> concat [indent i; pprint_expr a; " <= "; pprint_expr b; ";\n"]

let prettyprint = fold_map (pprint_stmnt 0)
