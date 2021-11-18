(* Note: this file is used by SliceToString, so it must not include it *)

open Camlcoq
open BinNums
open BinPos
open Maps
open RTL
open BourdoncleIterator
module B = Bourdoncle

type node = P.t

let int_of_positive p =
  let i = P.to_int p in
    i - 1

let positive_of_int n = P.of_int (n+1)

(* Functions copied from SliceToString to avoid mutual inclusion *)
let nodeToString (p : P.t) : string =
  Int.to_string (P.to_int p)
let rec cleanListToString' (aToString: 'a -> string) (l : 'a list) =
  match l with
  | [] -> ""
  | e :: r -> " " ^ (aToString e) ^ (cleanListToString' aToString r)
let cleanListToString (aToString: 'a -> string) (l : 'a list) =
  match l with
  | [] -> "[]"
  | [e] -> "(" ^ (aToString e) ^ ")"
  | e :: r -> "(" ^ (aToString e) ^ (cleanListToString' aToString r) ^ ")"
let rec bourdoncleToString (b : B.bourdoncle) : string =
  match b with
    | B.I n -> (nodeToString n)
    | B.L (h, lb) -> cleanListToString bourdoncleToString ((B.I h) :: lb)
let bourdoncleListToString (l : B.bourdoncle list) : string =
  cleanListToString bourdoncleToString l

(* Dummy type to avoid redefining existing functions *)
type instr = | Inop

let build_cfg f =
  let entry = int_of_positive f.fn_entrypoint in
  let max = PTree.fold (fun m n _ -> max m (int_of_positive n)) f.fn_code 0 in
  (* nodes are between 1 and max+1 *)
  let succ = Array.make (max+1) [] in
  let _ = PTree.fold (fun () n ins ->
			succ.(int_of_positive n) <-
        let inop : instr = Inop in
			  match ins with
			    | RTL.Inop j -> [(int_of_positive j, inop)]
			    | RTL.Iop (op,args,dst,j) -> [(int_of_positive j, Inop)]
			    | RTL.Iload (_,_,_,dst,j) -> [(int_of_positive j, Inop)]
			    | RTL.Istore (_,_,_,_,j) -> [(int_of_positive j, Inop)]
			    | RTL.Icall (_,_,_,dst,j) -> [(int_of_positive j, Inop)]
			    | RTL.Itailcall _ -> []
			    | RTL.Ibuiltin (_,_,dst,j) -> [(int_of_positive j, Inop)]
			    | RTL.Icond (c,args,j,k) -> [(int_of_positive j, Inop);(int_of_positive k, Inop)]
			    | RTL.Ijumptable (_,tbl) -> List.map (fun j -> (int_of_positive j, inop)) tbl
			    | RTL.Ireturn _ -> []) f.fn_code () in
    { entry = entry; succ = succ }

let rec build_bourdoncle' (bl : bourdoncle list) : B.bourdoncle list =
  match bl with
    | [] -> []
    | (I i) :: r -> B.I (positive_of_int i) :: (build_bourdoncle' r)
    | (L ((I h) :: l, _)) :: r -> B.L (positive_of_int h, build_bourdoncle' l) :: (build_bourdoncle' r)
    | _ -> failwith "Assertion error: invalid bourdoncle ist"

let build_bourdoncle'' (f : coq_function) : B.bourdoncle =
  let cfg = build_cfg f in
  match build_bourdoncle' (get_bourdoncle cfg) with
    | [] -> failwith "assertion error: empty bourdoncle"
    | l ->
      begin
        match l with
          | B.I h :: r -> B.L (h, r)
          | B.L (_, _) :: _ ->
            begin
              Printf.printf "ASSERTION ERROR: invalid program structure (too many bourdoncles)\n";
              Printf.printf "Head should be an element, but it is a list\n";
              Printf.printf "Failed at: %s\n" (bourdoncleListToString l);
              failwith "assertion error"
            end
          | _ -> failwith "assertion error : ???"
      end

(* Auxiliary function for build_order *)
let rec linearize (b : B.bourdoncle) : node list =
  match b with
    | B.I n -> [n]
    | B.L (h, l) -> List.fold_left (fun l0 b' -> l0 @ (linearize b')) [h] l

let succ_pos = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Pos.succ p)

let rec build_order' (l : node list) (count : coq_N) : coq_N PTree.t =
  match l with
    | [] -> PTree.empty
    | n :: r -> PTree.set n count (build_order' r (succ_pos count))

let build_order (b : B.bourdoncle) : coq_N PMap.t =
  let bo = build_order' (linearize b) (succ_pos N0) in
  (succ_pos N0, bo)

let build_bourdoncle (f : coq_function) : (B.bourdoncle * coq_N PMap.t) =
  let b = build_bourdoncle'' f in
  let bo = build_order b in
  (b, bo)
