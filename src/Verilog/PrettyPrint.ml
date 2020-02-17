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
  | Xor -> "^"

let rec pprint_expr = function
  | Lit l -> pprint_value l
  | Var s -> List.to_seq s |> String.of_seq
  | Neg e -> concat ["(-"; pprint_expr e; ")"]
  | BinOp (op, a, b) -> concat ["("; pprint_expr a; pprint_binop op; pprint_expr b; ")"]
  | Ternary (c, t, f) -> concat ["("; pprint_expr c; " ? "; pprint_expr t; " : "; pprint_expr f; ")"]

let rec pprint_stmnt i =
  let pprint_case (e, s) = concat [indent (i + 1); pprint_expr e; ":\n"; pprint_stmnt (i+2) s]
  in function
  | Skip -> concat [indent i; ";\n"]
  | Block s -> concat [indent i; "begin\n"; fold_map (pprint_stmnt (i+1)) s; indent i; "end\n"]
  | Cond (e, st, sf) -> concat [indent i; "if ("; pprint_expr e; ")\n";
                                pprint_stmnt (i + 1) st; indent i; "else\n";
                                pprint_stmnt (i + 1) sf]
  | Case (e, es) -> concat [indent i; "case ("; pprint_expr e; ")\n";
                            fold_map pprint_case es; indent i; "endcase"]
  | Blocking (a, b) -> concat [indent i; pprint_expr a; " = "; pprint_expr b; ";\n"]
  | Nonblocking (a, b) -> concat [indent i; pprint_expr a; " <= "; pprint_expr b; ";\n"]

let prettyprint = fold_map (pprint_stmnt 0)
