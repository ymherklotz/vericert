(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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
open Kildall
open Op
open Gible
open Predicate
open GibleSeq
open GibleSeq
open GiblePar
open GiblePar
open HTL
open Verilog
open HTLgen
open HTLMonad
open HTLMonadExtra

module SS = Set.Make(P)

type svtype =
  | BBType of int
  | VarType of int * int

type sv = {
  sv_type: svtype;
  sv_num: int;
}

let print_sv v =
  match v with
  | { sv_type = BBType bbi; sv_num = n } -> sprintf "bb%d_%d" bbi n
  | { sv_type = VarType (bbi, i); sv_num = n } -> sprintf "var%dn%d_%d" bbi i n

module G = Graph.Persistent.Digraph.ConcreteLabeled(struct
  type t = sv
  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
end)(struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = 0
end)

module GDot = Graph.Graphviz.Dot(struct
    let graph_attributes _ = []
    let default_vertex_attributes _ = []
    let vertex_name = print_sv
    let vertex_attributes _ = []
    let get_subgraph _ = None
    let default_edge_attributes _ = []
    let edge_attributes _ = []

    include G
  end)

module DFG = Graph.Persistent.Digraph.ConcreteLabeled(struct
  type t = int * instr
  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
end)(struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = 0
end)

module DFGSimp = Graph.Persistent.Graph.Concrete(struct
    type t = int * instr
    let compare = compare
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let convert dfg =
  DFG.fold_vertex (fun v g -> DFGSimp.add_vertex g v) dfg DFGSimp.empty
  |> DFG.fold_edges (fun v1 v2 g -> DFGSimp.add_edge (DFGSimp.add_edge g v1 v2) v2 v1) dfg

let reg r = sprintf "r%d" (P.to_int r)
let print_pred r = sprintf "p%d" (P.to_int r)

let print_instr = function
  | RBnop -> ""
  | RBload (_, _, _, _, r) -> sprintf "load(%s)" (reg r)
  | RBstore (_, _, _, _, r) -> sprintf "store(%s)" (reg r)
  | RBsetpred (_, _, _, p) -> sprintf "setpred(%s)" (print_pred p)
  | RBexit _ -> sprintf "exit"
  | RBop (_, op, args, d) ->
    (match op, args with
    | Omove, [r1] -> sprintf "%s=%s" (reg d) (reg r1)
    | Ointconst n, _ -> sprintf "%s=%ld" (reg d) (camlint_of_coqint n)
    | Olongconst n, _ -> sprintf "%s=%LdL" (reg d) (camlint64_of_coqint n)
    | Ofloatconst n, _ -> sprintf "%s=%.15F" (reg d) (camlfloat_of_coqfloat n)
    | Osingleconst n, _ -> sprintf "%s=%.15Ff" (reg d) (camlfloat_of_coqfloat32 n)
    | Oindirectsymbol id, _ -> sprintf "%s=&%s" (reg d) (extern_atom id)
    | Ocast8signed, [r1] -> sprintf "%s=int8signed(%s)" (reg d) (reg r1)
    | Ocast8unsigned, [r1] -> sprintf "%s=int8unsigned(%s)" (reg d) (reg r1)
    | Ocast16signed, [r1] -> sprintf "%s=int16signed(%s)" (reg d) (reg r1)
    | Ocast16unsigned, [r1] -> sprintf "%s=int16unsigned(%s)" (reg d) (reg r1)
    | Oneg, [r1] -> sprintf "%s=-%s" (reg d) (reg r1)
    | Osub, [r1;r2] -> sprintf "%s=%s-%s" (reg d) (reg r1) (reg r2)
    | Omul, [r1;r2] -> sprintf "%s=%s*%s" (reg d) (reg r1) (reg r2)
    | Omulimm n, [r1] -> sprintf "%s=%s*%ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Omulhs, [r1;r2] -> sprintf "%s=mulhs(%s,%s)" (reg d) (reg r1) (reg r2)
    | Omulhu, [r1;r2] -> sprintf "%s=mulhu(%s,%s)" (reg d) (reg r1) (reg r2)
    | Odiv, [r1;r2] -> sprintf "%s=%s /s %s" (reg d) (reg r1) (reg r2)
    | Odivu, [r1;r2] -> sprintf "%s=%s /u %s" (reg d) (reg r1) (reg r2)
    | Omod, [r1;r2] -> sprintf "%s=%s %%s %s" (reg d) (reg r1) (reg r2)
    | Omodu, [r1;r2] -> sprintf "%s=%s %%u %s" (reg d) (reg r1) (reg r2)
    | Oand, [r1;r2] -> sprintf "%s=%s & %s" (reg d) (reg r1) (reg r2)
    | Oandimm n, [r1] -> sprintf "%s=%s & %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oor, [r1;r2] -> sprintf "%s=%s | %s" (reg d) (reg r1) (reg r2)
    | Oorimm n, [r1] ->  sprintf "%s=%s | %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oxor, [r1;r2] -> sprintf "%s=%s ^ %s" (reg d) (reg r1) (reg r2)
    | Oxorimm n, [r1] -> sprintf "%s=%s ^ %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Onot, [r1] -> sprintf "%s=not(%s)" (reg d) (reg r1)
    | Oshl, [r1;r2] -> sprintf "%s=%s << %s" (reg d) (reg r1) (reg r2)
    | Oshlimm n, [r1] -> sprintf "%s=%s << %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshr, [r1;r2] -> sprintf "%s=%s >>s %s" (reg d) (reg r1) (reg r2)
    | Oshrimm n, [r1] -> sprintf "%s=%s >>s %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshrximm n, [r1] -> sprintf "%s=%s >>x %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshru, [r1;r2] -> sprintf "%s=%s >>u %s" (reg d) (reg r1) (reg r2)
    | Oshruimm n, [r1] -> sprintf "%s=%s >>u %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Ororimm n, [r1] -> sprintf "%s=%s ror %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshldimm n, [r1;r2] -> sprintf "%s=(%s, %s) << %ld" (reg d) (reg r1) (reg r2) (camlint_of_coqint n)
    | Olea addr, [r1] -> sprintf "%s=addr[%s]" (reg d) (reg r1)
    | Olea addr, [r1;r2] -> sprintf "%s=addr[%s,%s]" (reg d) (reg r1) (reg r2)
    | Olea addr, [r1;r2;r3] -> sprintf "%s=addr[%s,%s,%s]" (reg d) (reg r1) (reg r2) (reg r3)
    | Omakelong, [r1;r2] -> sprintf "%s=makelong(%s,%s)" (reg d) (reg r1) (reg r2)
    | Olowlong, [r1] -> sprintf "%s=lowlong(%s)" (reg d) (reg r1)
    | Ohighlong, [r1] -> sprintf "%s=highlong(%s)" (reg d) (reg r1)
    | Ocast32signed, [r1] -> sprintf "%s=long32signed(%s)" (reg d) (reg r1)
    | Ocast32unsigned, [r1] -> sprintf "%s=long32unsigned(%s)" (reg d) (reg r1)
    | Onegl, [r1] -> sprintf "%s=-l %s" (reg d) (reg r1)
    | Osubl, [r1;r2] -> sprintf "%s=%s -l %s" (reg d) (reg r1) (reg r2)
    | Omull, [r1;r2] -> sprintf "%s=%s *l %s" (reg d) (reg r1) (reg r2)
    | Omullimm n, [r1] -> sprintf "%s=%s *l %Ld" (reg d) (reg r1) (camlint64_of_coqint n)
    | Omullhs, [r1;r2] -> sprintf "%s=mullhs(%s,%s)" (reg d) (reg r1) (reg r2)
    | Omullhu, [r1;r2] -> sprintf "%s=mullhu(%s,%s)" (reg d) (reg r1) (reg r2)
    | Odivl, [r1;r2] -> sprintf "%s=%s /ls %s" (reg d) (reg r1) (reg r2)
    | Odivlu, [r1;r2] -> sprintf "%s=%s /lu %s" (reg d) (reg r1) (reg r2)
    | Omodl, [r1;r2] -> sprintf "%s=%s %%ls %s" (reg d) (reg r1) (reg r2)
    | Omodlu, [r1;r2] -> sprintf "%s=%s %%lu %s" (reg d) (reg r1) (reg r2)
    | Oandl, [r1;r2] -> sprintf "%s=%s &l %s" (reg d) (reg r1) (reg r2)
    | Oandlimm n, [r1] -> sprintf "%s=%s &l %Ld" (reg d) (reg r1) (camlint64_of_coqint n)
    | Oorl, [r1;r2] -> sprintf "%s=%s |l %s" (reg d) (reg r1) (reg r2)
    | Oorlimm n, [r1] ->  sprintf "%s=%s |l %Ld" (reg d) (reg r1) (camlint64_of_coqint n)
    | Oxorl, [r1;r2] -> sprintf "%s=%s ^l %s" (reg d) (reg r1) (reg r2)
    | Oxorlimm n, [r1] -> sprintf "%s=%s ^l %Ld" (reg d) (reg r1) (camlint64_of_coqint n)
    | Onotl, [r1] -> sprintf "%s=notl(%s)" (reg d) (reg r1)
    | Oshll, [r1;r2] -> sprintf "%s=%s <<l %s" (reg d) (reg r1) (reg r2)
    | Oshllimm n, [r1] -> sprintf "%s=%s <<l %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshrl, [r1;r2] -> sprintf "%s=%s >>ls %s" (reg d) (reg r1) (reg r2)
    | Oshrlimm n, [r1] -> sprintf "%s=%s >>ls %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshrxlimm n, [r1] -> sprintf "%s=%s >>lx %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oshrlu, [r1;r2] -> sprintf "%s=%s >>lu %s" (reg d) (reg r1) (reg r2)
    | Oshrluimm n, [r1] -> sprintf "%s=%s >>lu %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Ororlimm n, [r1] -> sprintf "%s=%s rorl %ld" (reg d) (reg r1) (camlint_of_coqint n)
    | Oleal addr, args -> sprintf "%s=addr" (reg d)
    | Onegf, [r1] -> sprintf "%s=negf(%s)" (reg d) (reg r1)
    | Oabsf, [r1] -> sprintf "%s=absf(%s)" (reg d) (reg r1)
    | Oaddf, [r1;r2] -> sprintf "%s=%s +f %s" (reg d) (reg r1) (reg r2)
    | Osubf, [r1;r2] -> sprintf "%s=%s -f %s" (reg d) (reg r1) (reg r2)
    | Omulf, [r1;r2] -> sprintf "%s=%s *f %s" (reg d) (reg r1) (reg r2)
    | Odivf, [r1;r2] -> sprintf "%s=%s /f %s" (reg d) (reg r1) (reg r2)
    | Onegfs, [r1] -> sprintf "%s=negfs(%s)" (reg d) (reg r1)
    | Oabsfs, [r1] -> sprintf "%s=absfs(%s)" (reg d) (reg r1)
    | Oaddfs, [r1;r2] -> sprintf "%s=%s +fs %s" (reg d) (reg r1) (reg r2)
    | Osubfs, [r1;r2] -> sprintf "%s=%s -fs %s" (reg d) (reg r1) (reg r2)
    | Omulfs, [r1;r2] -> sprintf "%s=%s *fs %s" (reg d) (reg r1) (reg r2)
    | Odivfs, [r1;r2] -> sprintf "%s=%s /fs %s" (reg d) (reg r1) (reg r2)
    | Osingleoffloat, [r1] -> sprintf "%s=singleoffloat(%s)" (reg d) (reg r1)
    | Ofloatofsingle, [r1] -> sprintf "%s=floatofsingle(%s)" (reg d) (reg r1)
    | Ointoffloat, [r1] -> sprintf "%s=intoffloat(%s)" (reg d) (reg r1)
    | Ofloatofint, [r1] -> sprintf "%s=floatofint(%s)" (reg d) (reg r1)
    | Ointofsingle, [r1] -> sprintf "%s=intofsingle(%s)" (reg d) (reg r1)
    | Osingleofint, [r1] -> sprintf "%s=singleofint(%s)" (reg d) (reg r1)
    | Olongoffloat, [r1] -> sprintf "%s=longoffloat(%s)" (reg d) (reg r1)
    | Ofloatoflong, [r1] -> sprintf "%s=floatoflong(%s)" (reg d) (reg r1)
    | Olongofsingle, [r1] -> sprintf "%s=longofsingle(%s)" (reg d) (reg r1)
    | Osingleoflong, [r1] -> sprintf "%s=singleoflong(%s)" (reg d) (reg r1)
    | Ocmp c, args -> sprintf "%s=cmp" (reg d)
    | Osel (c, ty), r1::r2::args -> sprintf "%s=sel" (reg d)
    | _, _ -> sprintf "N/a")

module DFGDot = Graph.Graphviz.Dot(struct
    let graph_attributes _ = []
    let default_vertex_attributes _ = []
    let vertex_name (i, instr) = sprintf "\"%d:%s\"" i (print_instr instr)
    let vertex_attributes _ = []
    let get_subgraph _ = None
    let default_edge_attributes _ = []
    let edge_attributes (_, e, _) = [`Label (string_of_int e)]

    include DFG
  end)

module DFGDfs = Graph.Traverse.Dfs(DFG)

module IMap = Map.Make (struct
  type t = int

  let compare = compare
end)

let gen_vertex instrs i = (i, List.nth instrs i)

(** The DFG type defines a list of instructions with their data dependencies as [edges], which are
   the pairs of integers that represent the index of the instruction in the [nodes].  The edges
   always point from left to right. *)

let print_list f out_chan a =
  fprintf out_chan "[ ";
  List.iter (fprintf out_chan "%a " f) a;
  fprintf out_chan "]"

let print_tuple out_chan a =
  let l, r = a in
  fprintf out_chan "(%d,%d)" l r

(*let print_dfg out_chan dfg =
  fprintf out_chan "{ nodes = %a, edges = %a }"
    (print_list PrintRTLBlockInstr.print_bblock_body)
    dfg.nodes (print_list print_tuple) dfg.edges*)

let print_dfg = DFGDot.output_graph

let read_process command =
  let buffer_size = 2048 in
  let buffer = Buffer.create buffer_size in
  let string = Bytes.create buffer_size in
  let in_channel = Unix.open_process_in command in
  let chars_read = ref 1 in
  while !chars_read <> 0 do
    chars_read := input in_channel string 0 buffer_size;
    Buffer.add_substring buffer (Bytes.to_string string) 0 !chars_read
  done;
  ignore (Unix.close_process_in in_channel);
  Buffer.contents buffer

let multiply_dest = ref SS.empty

let comb_delay = function
  | RBnop -> 0
  | RBop (_, op, args, d) ->
     (if SS.mem d !multiply_dest || List.exists (fun x -> SS.mem x !multiply_dest) args (* false *) then
        (match op with
         | Odiv | Odivu | Omod | Omodu -> 576
         | _ -> 48)
      else
        (match op with
         | Omove -> 16

         | Ointconst _
           | Olongconst _ -> 16

         | Ocast8signed
           | Ocast8unsigned
           | Ocast16signed
           | Ocast16unsigned -> 16

         | Oneg
           | Onot -> 16

         | Oor
           | Oand
           | Oxor -> 16

         | Oorimm _
           | Oandimm _
           | Oxorimm _ -> 16

         | Omul
           | Omulimm _
           | Omulhs
           | Omulhu -> 48

         | Odiv
           | Odivu
           | Omod
           | Omodu -> 576

         | _ -> 16))
  (* | RBop (_, op, args, d) -> *)
  (*    (if SS.mem d !multiply_dest || List.exists (fun x -> SS.mem x !multiply_dest) args (\* false *\) then *)
  (*       (match op with *)
  (*        | Odiv | Odivu | Omod | Omodu -> 576 *)
  (*        | _ -> 48) *)
  (*     else *)
  (*       (match op with *)
  (*        | Omove -> 1 *)

  (*        | Ointconst _ *)
  (*          | Olongconst _ -> 1 *)

  (*        | Ocast8signed *)
  (*          | Ocast8unsigned *)
  (*          | Ocast16signed *)
  (*          | Ocast16unsigned -> 8 *)

  (*        | Oneg *)
  (*          | Onot -> 8 *)

  (*        | Oor *)
  (*          | Oand *)
  (*          | Oxor -> 8 *)

  (*        | Oorimm _ *)
  (*          | Oandimm _ *)
  (*          | Oxorimm _ -> 8 *)

  (*        | Omul *)
  (*          | Omulimm _ *)
  (*          | Omulhs *)
  (*          | Omulhu -> 32 *)

  (*        | Odiv *)
  (*          | Odivu *)
  (*          | Omod *)
  (*          | Omodu -> 576 *)

  (*        | _ -> 8)) *)
  | RBexit (Some _, _) -> 16
  | RBexit _ -> 4
  (** Because of the limiations of memory generation we add a large combinational
      delay for loads and stores. *)
  | RBload _ -> 64
  | RBstore _ -> 64
  | RBsetpred (Some _op, _, _, _) -> 16
  | RBsetpred (None, _, _, _) -> 8

let pipeline_stages = function
  | RBload _ -> 1 (* TODO: Set back to 2 when memory inferrence is fixed. *)
  | RBstore _ -> 1
  | RBop (_, op, _, _) ->
     (match op with
      | Odiv -> 32
      | Odivu -> 32
      | Omod -> 32
      | Omodu -> 32
      | _ -> 0)
  | _ -> 0

(** Add a dependency if it uses a register that was written to previously. *)
let add_dep map i tree dfg curr =
  match PTree.get curr tree with
  | None -> dfg
  | Some ip ->
    let ipv = (List.nth map ip) in
    DFG.add_edge_e dfg (ipv, comb_delay (snd (List.nth map i)), List.nth map i)

(** This function calculates the dependencies of each instruction.  The nodes correspond to previous
   registers that were allocated and show which instruction caused it.

   This function only gathers the RAW constraints, and will therefore only be active for operations
   that modify registers, which is this case only affects loads and operations. *)
let accumulate_RAW_deps map dfg curr =
  let i, dst_map, graph = dfg in
  let acc_dep_instruction rs dst =
    ( i + 1,
      PTree.set dst i dst_map,
      List.fold_left (add_dep map i dst_map) graph rs
    )
  in
  let acc_dep_instruction_nodst rs =
    ( i + 1,
      dst_map,
    List.fold_left (add_dep map i dst_map) graph rs)
  in
  match curr with
  | RBop (op, _, rs, dst) -> acc_dep_instruction rs dst
  | RBload (op, _mem, _addr, rs, dst) -> acc_dep_instruction rs dst
  | RBsetpred (_op, _mem, rs, _p) -> acc_dep_instruction_nodst rs
  | RBstore (op, _mem, _addr, rs, src) -> acc_dep_instruction_nodst (src :: rs)
  | RBexit (_, RBcall (_, _, rs, _, _)) -> acc_dep_instruction_nodst rs
  | RBexit (_, RBtailcall (_, _, rs)) -> acc_dep_instruction_nodst rs
  | RBexit (_, RBcond (_, rs, _, _)) -> acc_dep_instruction_nodst rs
  | RBexit (_, RBjumptable (r, _)) -> acc_dep_instruction_nodst [r]
  | RBexit (_, RBreturn (Some r)) -> acc_dep_instruction_nodst [r]
  | _ -> (i + 1, dst_map, graph)

(** Finds the next write to the [dst] register.  This is a small optimisation so that only one
   dependency is generated for a data dependency. *)
let rec find_next_dst_write i dst i' curr =
  let check_dst dst' curr' =
    if dst = dst' then Some (i, i')
    else find_next_dst_write i dst (i' + 1) curr'
  in
  match curr with
  | [] -> None
  | RBop (_, _, _, dst') :: curr' -> check_dst dst' curr'
  | RBload (_, _, _, _, dst') :: curr' -> check_dst dst' curr'
  | _ :: curr' -> find_next_dst_write i dst (i' + 1) curr'

let rec find_all_next_dst_read i dst i' curr =
  let check_dst rs curr' =
    if List.exists (fun x -> x = dst) rs
    then (i, i') :: find_all_next_dst_read i dst (i' + 1) curr'
    else find_all_next_dst_read i dst (i' + 1) curr'
  in
  match curr with
  | [] -> []
  | RBop (_, _, rs, _) :: curr' -> check_dst rs curr'
  | RBload (_, _, _, rs, _) :: curr' -> check_dst rs curr'
  | RBstore (_, _, _, rs, src) :: curr' -> check_dst (src :: rs) curr'
  | RBsetpred (_, _, rs, _) :: curr' -> check_dst rs curr'
  | RBexit (_, RBcall (_, _, rs, _, _)) :: curr' -> check_dst rs curr'
  | RBexit (_, RBtailcall (_, _, rs)) :: curr' -> check_dst rs curr'
  | RBexit (_, RBcond (_, rs, _, _)) :: curr' -> check_dst rs curr'
  | RBexit (_, RBjumptable (r, _)) :: curr' -> check_dst [r] curr'
  | RBexit (_, RBreturn (Some r)) :: curr' -> check_dst [r] curr'
  | _ :: curr' -> check_dst [] curr'

let drop i lst =
  let rec drop' i' lst' =
    match lst' with
    | _ :: ls -> if i' = i then ls else drop' (i' + 1) ls
    | [] -> []
  in
  if i = 0 then lst else drop' 1 lst

let take i lst =
  let rec take' i' lst' =
    match lst' with
    | l :: ls -> if i' = i then [ l ] else l :: take' (i' + 1) ls
    | [] -> []
  in
  if i = 0 then [] else take' 1 lst

let rec next_store i = function
  | [] -> None
  | RBstore (_, _, _, _, _) :: _ -> Some i
  | _ :: rst -> next_store (i + 1) rst

let rec next_load i = function
  | [] -> None
  | RBload (_, _, _, _, _) :: _ -> Some i
  | _ :: rst -> next_load (i + 1) rst

let accumulate_RAW_mem_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBload (_, _, _, _, _) -> (
      match next_store 0 (take i instrs |> List.rev) with
      | None -> dfg
      | Some d -> DFG.add_edge_e dfg ((gen_vertex instrs (i - d - 1)), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i)) )
  | _ -> dfg

let accumulate_WAR_mem_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBstore (_, _, _, _, _) -> (
      match next_load 0 (take i instrs |> List.rev) with
      | None -> dfg
      | Some d -> DFG.add_edge_e dfg ((gen_vertex instrs (i - d - 1)), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i)) )
  | _ -> dfg

let accumulate_WAW_mem_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBstore (_, _, _, _, _) -> (
      match next_store 0 (take i instrs |> List.rev) with
      | None -> dfg
      | Some d -> DFG.add_edge_e dfg ((gen_vertex instrs (i - d - 1)), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i)))
  | _ -> dfg

(** Predicate dependencies. *)

let rec in_predicate p p' =
  match p' with
  | Plit p'' -> P.to_int p = P.to_int (snd p'')
  | Pand (p1, p2) -> in_predicate p p1 || in_predicate p p2
  | Por (p1, p2) -> in_predicate p p1 || in_predicate p p2
  | Ptrue -> false
  | Pfalse -> false

let get_predicate = function
  | RBop (p, _, _, _) -> p
  | RBload (p, _, _, _, _) -> p
  | RBstore (p, _, _, _, _) -> p
  | RBsetpred (p, _, _, _) -> p
  | RBexit (p, _) -> p
  | _ -> None

let rec next_setpred p i = function
  | [] -> None
  | RBsetpred (_, _, _, p') :: rst ->
    if in_predicate p' p then
      Some i
    else
      next_setpred p (i + 1) rst
  | _ :: rst -> next_setpred p (i + 1) rst

let rec next_preduse p i instr=
  let next p' rst =
    if in_predicate p p' then
      Some i
    else
      next_preduse p (i + 1) rst
  in
  match instr with
  | [] -> None
  | RBload (Some p', _, _, _, _) :: rst -> next p' rst
  | RBstore (Some p', _, _, _, _) :: rst -> next p' rst
  | RBop (Some p', _, _, _) :: rst -> next p' rst
  | RBsetpred (Some p', _, _, _) :: rst -> next p' rst
  | RBexit (Some p', _) :: rst -> next p' rst
  | _ :: rst -> next_load (i + 1) rst

let accumulate_RAW_pred_deps instrs dfg curri =
  let i, curr = curri in
  match get_predicate curr with
  | Some p -> (
      match next_setpred p 0 (take i instrs |> List.rev) with
      | None -> dfg
      | Some d -> DFG.add_edge_e dfg ((gen_vertex instrs (i - d - 1)), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i)) )
  | _ -> dfg

let accumulate_WAR_pred_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBsetpred (_, _, _, p) -> (
      match next_preduse p 0 (take i instrs |> List.rev) with
      | None -> dfg
      | Some d -> DFG.add_edge_e dfg ((gen_vertex instrs (i - d - 1)), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i)) )
  | _ -> dfg

let accumulate_WAW_pred_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBsetpred (_, _, _, p) -> (
      match next_setpred (Plit (true, p)) 0 (take i instrs |> List.rev) with
      | None -> dfg
      | Some d -> DFG.add_edge_e dfg ((gen_vertex instrs (i - d - 1)), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i)) )
  | _ -> dfg

(** This function calculates the WAW dependencies, which happen when two writes are ordered one
   after another and therefore have to be kept in that order.  This accumulation might be redundant
   if register renaming is done before hand, because then these dependencies can be avoided. *)
let accumulate_WAW_deps instrs dfg curri =
  let i, curr = curri in
  let dst_dep dst =
    match find_next_dst_write i dst (i + 1) (drop (i + 1) instrs) with
    | Some (a, b) -> DFG.add_edge_e dfg ((gen_vertex instrs a), comb_delay (snd (gen_vertex instrs b)), (gen_vertex instrs b))
    | _ -> dfg
  in
  match curr with
  | RBop (_, _, _, dst) -> dst_dep dst
  | RBload (_, _, _, _, dst) -> dst_dep dst
  | RBstore (_, _, _, _, _) -> (
      match next_store (i + 1) (drop (i + 1) instrs) with
      | None -> dfg
      | Some i' -> DFG.add_edge_e dfg ((gen_vertex instrs i), comb_delay (snd (gen_vertex instrs i')), (gen_vertex instrs i')) )
  | _ -> dfg

let accumulate_pre_exit_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBexit (_, _) ->
    List.fold_left (fun ndfg -> function (i', instr') ->
        if i' < i
        then DFG.add_edge_e ndfg ((gen_vertex instrs i'), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i))
        else ndfg
      ) dfg (List.mapi (fun i x -> (i, x)) instrs)
  | _ -> dfg

let accumulate_post_exit_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBexit (_, _) ->
    List.fold_left (fun ndfg -> function (i', instr') ->
        if i' > i
        then DFG.add_edge_e ndfg ((gen_vertex instrs i), comb_delay (snd (gen_vertex instrs i')), (gen_vertex instrs i'))
        else ndfg
      ) dfg (List.mapi (fun i x -> (i, x)) instrs)
  | _ -> dfg

(** At the moment, because of the limitations of the memory generation pass, all
    the loads and stores need to be placed into their own cycles. *)

let accumulate_pre_mem_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBstore _
  | RBload _ ->
    List.fold_left (fun ndfg -> function (i', instr') ->
        if i' < i
        then DFG.add_edge_e ndfg ((gen_vertex instrs i'), comb_delay (snd (gen_vertex instrs i)), (gen_vertex instrs i))
        else ndfg
      ) dfg (List.mapi (fun i x -> (i, x)) instrs)
  | _ -> dfg

let accumulate_post_mem_deps instrs dfg curri =
  let i, curr = curri in
  match curr with
  | RBstore _
  | RBload _ ->
    List.fold_left (fun ndfg -> function (i', instr') ->
        if i' > i
        then DFG.add_edge_e ndfg ((gen_vertex instrs i), comb_delay (snd (gen_vertex instrs i')), (gen_vertex instrs i'))
        else ndfg
      ) dfg (List.mapi (fun i x -> (i, x)) instrs)
  | _ -> dfg

let accumulate_WAR_deps instrs dfg curri =
  let i, curr = curri in
  let dst_dep dst =
    let dep_list = find_all_next_dst_read i dst 0 (take i instrs |> List.rev)
        |> List.map (function (d, d') -> (i - d' - 1, d))
    in
    List.fold_left (fun g ->
        function (d, d') -> DFG.add_edge_e g ((gen_vertex instrs d), comb_delay (snd (gen_vertex instrs d')), (gen_vertex instrs d'))) dfg dep_list
  in
  match curr with
  | RBop (_, _, _, dst) -> dst_dep dst
  | RBload (_, _, _, _, dst) -> dst_dep dst
  | _ -> dfg

let assigned_vars vars = function
  | RBnop -> vars
  | RBop (_, _, _, dst) -> dst :: vars
  | RBload (_, _, _, _, dst) -> dst :: vars
  | RBstore (_, _, _, _, _) -> vars
  | RBsetpred (_, _, _, _) -> vars
  | RBexit (_, _) -> vars

(** To be able to properly eliminate dependencies on control-flow, one needs to be able to handle
    comparisons of a register that has a value in one version, and no value in the other, which the
    checker currently does not. *)

let get_pred = function
  | RBnop -> None
  | RBop (op, _, _, _) -> op
  | RBload (op, _, _, _, _) -> op
  | RBstore (op, _, _, _, _) -> op
  (* | RBexit (op, _) -> op *)
  | RBexit (op, _) -> None
  | RBsetpred (op, _, _, _) -> op

let independant_pred p p' =
  match sat_pred_simple (Pand (p, p')) with
  | None -> true
  | _ -> false

let check_dependent op1 op2 =
  match op1, op2 with
  | Some p, Some p' -> not (independant_pred p p')
  | _, _ -> true

let remove_unnecessary_deps graph =
  let is_dependent v1 v2 g =
    let (_, instr1) = v1 in
    let (_, instr2) = v2 in
    if check_dependent (get_pred instr1) (get_pred instr2)
    then g
    else DFG.remove_edge g v1 v2
  in
  DFG.fold_edges is_dependent graph graph

let gather_multiply_destinations =
  List.iter (fun a -> 
    match a with
    | RBop (_, Omul, _, d)
    | RBop (_, Omulimm _, _, d)
    | RBop (_, Omulhs, _, d)
    | RBop (_, Omulhu, _, d) -> 
       multiply_dest := SS.add d !multiply_dest
    | _ -> ()
    )
  
  (* DFG.fold_edges_e (function (a, el, c) -> fun dfg -> *)
  (*     match get_predicate (snd c), assigned_vars [] (snd c) with *)
  (*     | Some _, [d] ->  *)
  (*        (if SS.mem d multiply_regs && el <= 64 then *)
  (*           DFG.add_edge_e (DFG.remove_edge_e dfg (a, el, c)) (a, 64, c) *)
  (*         else dfg) *)
  (*     | None, [d] ->  *)
  (*        (if SS.mem d multiply_regs && el <= 48 then *)
  (*           DFG.add_edge_e (DFG.remove_edge_e dfg (a, el, c)) (a, 48, c) *)
  (*         else dfg) *)
  (*     | _ -> dfg *)
  (*   ) dfg dfg *)

(** All the nodes in the DFG have to come after the source of the basic block, and should terminate
   before the sink of the basic block.  After that, there should be constraints for data
   dependencies between nodes. *)
let gather_bb_constraints debug bb =
  let ibody = List.mapi (fun i a -> (i, a)) bb in
  let dfg = List.fold_left (fun dfg v -> DFG.add_vertex dfg v) DFG.empty ibody in
  let _, _, dfg' =
    List.fold_left (accumulate_RAW_deps ibody)
      (0, PTree.empty, dfg)
      bb
  in
  let dfg'' = List.fold_left (fun dfg f -> List.fold_left (f bb) dfg ibody) dfg'
      [ accumulate_WAW_deps;
        accumulate_WAR_deps;
        accumulate_RAW_mem_deps;
        accumulate_WAR_mem_deps;
        accumulate_WAW_mem_deps;
        accumulate_RAW_pred_deps;
        accumulate_WAR_pred_deps;
        accumulate_WAW_pred_deps;
        accumulate_pre_exit_deps;
        accumulate_post_exit_deps;
        (* accumulate_post_mem_deps; *)
        (* accumulate_pre_mem_deps; *)
      ]
  in
  let dfg''' = remove_unnecessary_deps dfg'' in
  (* let dfg'''' = update_mult_edges bb dfg''' in *)
  (List.length bb, dfg''', GibleSeq.all_successors bb)

let encode_var bbn n i = { sv_type = VarType (bbn, n); sv_num = i }
let encode_bb bbn i = { sv_type = BBType bbn; sv_num = i }

let add_initial_sv n dfg constr =
  let add_initial_sv' (i, instr) g =
    let pipes = pipeline_stages instr in
    if pipes > 0 then
      List.init pipes (fun i' -> i')
      |> List.fold_left (fun g i' ->
          G.add_edge_e g (encode_var n i i', -1, encode_var n i (i'+1))
        ) g
    else g
  in
  DFG.fold_vertex add_initial_sv' dfg constr

let add_super_nodes n dfg =
  DFG.fold_vertex (function v1 -> fun g ->
      (if DFG.in_degree dfg v1 = 0
       then G.add_edge_e g (encode_bb n 0, 0, encode_var n (fst v1) 0)
       else g) |>
      (fun g' ->
         if DFG.out_degree dfg v1 = 0
         then G.add_edge_e g' (encode_var n (fst v1) (pipeline_stages (snd v1)),
                               0, encode_bb n 1)
         else g')) dfg

let add_data_deps n =
  DFG.fold_edges_e (function ((i1, instr1), _, (i2, _)) -> fun g ->
      let end_sv = pipeline_stages instr1 in
      G.add_edge_e g (encode_var n i1 end_sv, 0, encode_var n i2 0)
    )

let add_ctrl_deps n succs constr =
  List.fold_left (fun g n' ->
      G.add_edge_e g (encode_bb n 1, -1, encode_bb n' 0)
    ) constr succs

module BFDFG = Graph.Path.BellmanFord(DFG)(struct
    include DFG
    type t = int
    let weight = DFG.E.label
    let compare = compare
    let add = (+)
    let zero = 0
  end)

module TopoDFG = Graph.Topological.Make(DFG)

let negate_graph constr =
  DFG.fold_edges_e (function (v1, e, v2) -> fun g ->
      DFG.add_edge_e g (v1, -e, v2)
    ) constr DFG.empty

let add_cycle_constr maxf n dfg constr =
  let negated_dfg = negate_graph dfg in
  let max_initial_del = DFG.fold_vertex (fun v1 g ->
      if DFG.in_degree dfg v1 = 0
      then max g (comb_delay (snd v1))
      else g) dfg 0 in
  let longest_path v = BFDFG.all_shortest_paths negated_dfg v
                       |> BFDFG.H.to_seq |> List.of_seq
                       |> List.map (function (x, y) -> (x, y - comb_delay (snd v) (* - max_initial_del *))) in
  let constrained_paths = List.filter (function (_, m) -> - m > maxf) in
  (* Printf.printf "########## %d ##########\n" n; *)
  (* let graph = open_out (sprintf "constr_graph_%d.dot" n) in *)
  (* fprintf graph "%a\n" print_dfg dfg; *)
  (* close_out graph; *)
  List.fold_left (fun g -> function (v, v', w) ->
      G.add_edge_e g (encode_var n (fst v) 0,
                      - (int_of_float (Float.ceil (Float.div (float_of_int w) (float_of_int maxf))) - 1),
                      encode_var n (fst v') 0)
    ) constr (DFG.fold_vertex (fun v l ->
      List.append l (longest_path v |> (* (function l -> printf "path::\n"; List.iter (function (a, x) -> *)
          (* printf "%s -(%d)-> %s\n" (print_instr (snd v)) (-x) (print_instr (snd a))) l; l) |>  *)constrained_paths |>
                     List.map (function (v', w) -> (v, v', - w)))
    ) dfg [])

type resource =
  | Mem
  | SDiv
  | UDiv

type resources = {
  res_mem: DFG.V.t list;
  res_udiv: DFG.V.t list;
  res_sdiv: DFG.V.t list;
}

let find_resource = function
  | RBload _ -> Some Mem
  | RBstore _ -> Some Mem
  | RBop (_, op, _, _) ->
    ( match op with
      | Odiv -> Some SDiv
      | Odivu -> Some UDiv
      | Omod -> Some SDiv
      | Omodu -> Some UDiv
      | _ -> None )
  | _ -> None

let add_resource_constr n dfg constr =
  let res = TopoDFG.fold (function (i, instr) ->
    function {res_mem = ml; res_sdiv = sdl; res_udiv = udl} as r ->
    match find_resource instr with
    | Some SDiv -> {r with res_sdiv = (i, instr) :: sdl}
    | Some UDiv -> {r with res_udiv = (i, instr) :: udl}
    | Some Mem -> {r with res_mem = (i, instr) :: ml}
    | None -> r
    ) dfg {res_mem = []; res_sdiv = []; res_udiv = []}
  in
  let get_constraints l g = List.fold_left (fun gv v' ->
      match gv with
      | (g, None) -> (g, Some v')
      | (g, Some v) ->
        (G.add_edge_e g (encode_var n (fst v) 0, -1, encode_var n (fst v') 0), Some v')
    ) (g, None) l |> fst
  in
  get_constraints (List.rev res.res_mem) constr
  |> get_constraints (List.rev res.res_udiv)
  |> get_constraints (List.rev res.res_sdiv)

let gather_cfg_constraints (c: GibleSeq.code) constr curr =
  let (n, dfg) = curr in
  match PTree.get (P.of_int n) c with
  | None -> assert false
  | Some bb ->
    add_super_nodes n dfg constr
    |> add_initial_sv n dfg
    |> add_data_deps n dfg
    |> add_ctrl_deps n (GibleSeq.all_successors bb
                        |> List.map P.to_int
                        |> List.filter (fun n' -> n' < n))
    |> add_cycle_constr 64 n dfg
    |> add_resource_constr n dfg

let rec intersperse s = function
  | [] -> []
  | [ a ] -> [ a ]
  | x :: xs -> x :: s :: intersperse s xs

let print_objective constr =
  let vars = G.fold_vertex (fun v1 l ->
      match v1 with
      | { sv_type = VarType _; sv_num = 0 } -> print_sv v1 :: l
      | _ -> l
    ) constr []
  in
  "min: " ^ String.concat "" (intersperse " + " vars) ^ ";\n"

let print_lp constr =
  print_objective constr ^
  (G.fold_edges_e (function (e1, w, e2) -> fun s ->
       s ^ sprintf "%s - %s <= %d;\n" (print_sv e1) (print_sv e2) w
     ) constr "" |>
   G.fold_vertex (fun v1 s ->
       s ^ sprintf "int %s;\n" (print_sv v1)
     ) constr)

let update_schedule v = function Some l -> Some (v :: l) | None -> Some [ v ]

let parse_soln (tree, bbtree) s =
  let r = Str.regexp "var\\([0-9]+\\)n\\([0-9]+\\)_0[ ]+\\([0-9]+\\)" in
  let bb = Str.regexp "bb\\([0-9]+\\)_\\([0-9]+\\)[ ]+\\([0-9]+\\)" in
  let upd s = IMap.update
            (Str.matched_group 1 s |> int_of_string)
            (update_schedule
               ( Str.matched_group 2 s |> int_of_string,
                 Str.matched_group 3 s |> int_of_string ))
  in
  if Str.string_match r s 0
  then (upd s tree, bbtree)
  else
    (if Str.string_match bb s 0
     then (tree, upd s bbtree)
     else (tree, bbtree))

let solve_constraints constr =
  let (fn, oc) = Filename.open_temp_file "vericert_" "_lp_solve" in
  (* let (fn, oc) = ("vericert_lp_solve.txt", open_out "vericert_lp_solve.txt") in *)
  fprintf oc "%s\n" (print_lp constr);
  close_out oc;

  let res = Str.split (Str.regexp_string "\n") (read_process ("lp_solve " ^ fn))
            |> drop 3
            |> List.fold_left parse_soln (IMap.empty, IMap.empty)
  in
  (*Sys.remove fn;*) res

let subgraph dfg l =
  let dfg' = List.fold_left (fun g v -> DFG.add_vertex g v) DFG.empty l in
  List.fold_left (fun g v ->
      List.fold_left (fun g' v' ->
          let edges = DFG.find_all_edges dfg v v' in
          List.fold_left DFG.add_edge_e g' edges
        ) g l
    ) dfg' l

let rec all_successors dfg v =
  List.concat (List.fold_left (fun l v ->
      all_successors dfg v :: l
    ) [] (DFG.succ dfg v))

let order_instr dfg =
  DFG.fold_vertex (fun v li ->
      if DFG.in_degree dfg v = 0
      then (List.map snd (v :: all_successors dfg v)) :: li
      else li
    ) dfg []

let combine_bb_schedule schedule s =
  let i, st = s in
  IMap.update st (update_schedule i) schedule

(**let add_el dfg i l =
  List.*)

let check_in el =
  List.exists (List.exists ((=) el))

let all_dfs dfg =
  let roots = DFG.fold_vertex (fun v li ->
      if DFG.in_degree dfg v = 0 then v :: li else li
    ) dfg [] in
  let dfg' = DFG.fold_edges (fun v1 v2 g -> DFG.add_edge g v2 v1) dfg dfg in
  List.fold_left (fun a el ->
      if check_in el a then a else
        (DFGDfs.fold_component (fun v l -> v :: l) [] dfg' el) :: a) [] roots

let range s e =
  List.init (e - s) (fun i -> i)
  |> List.map (fun x -> x + s)

let remove_nop = function
  | RBnop -> []
  | a -> [a]

let separate_mem_operations l =
  let added = ref false in
  List.concat_map (fun par_list ->
      List.fold_left (fun new_l seq_list ->
          match List.concat_map remove_nop seq_list with
          | [RBload _] | [RBstore _] -> (added := true; new_l @ [[seq_list]])
          (* | [3] -> (added := true; new_l @ [[seq_list]]) *)
          | [] -> new_l
          | seq_list' ->
             ((if !added then (added := false; new_l @ [[seq_list']])
               else
                 (match List.rev new_l with
                  | [] -> [[seq_list']]
                  | new_lx :: new_ly -> List.rev ((new_lx @ [seq_list']) :: new_ly))))
        ) [] par_list
    ) l

let print_list_curly f out_chan a =
  fprintf out_chan "{ ";
  List.iter (fprintf out_chan "%a " f) a;
  fprintf out_chan "}"

let print_nested = print_list (print_list_curly (print_list (fun a b -> fprintf a "%d" b)))

(* let _ = *)
(*   printf "%a\n" print_nested (separate_mem_operations [[[1]; [1; 3]; [3]; [2]; [3]; [2]]]) *)

(** Should generate the [RTLPar] code based on the input [RTLBlock] description. *)
let transf_rtlpar c c' schedule =
  let f i bb : ParBB.t =
    match bb with
    | bb_body' ->
    (* | { bb_body = bb_body'; bb_exit = ctrl_flow } -> *)
      let dfg = match PTree.get i c' with None -> assert false | Some x -> x in
      let bb_st_e =
        let m = IMap.find (P.to_int i) (snd schedule) in
        (List.assq 0 m, List.assq 1 m) in
      let i_sched = IMap.find (P.to_int i) (fst schedule) in
      let i_sched_tree =
        List.fold_left combine_bb_schedule IMap.empty i_sched
      in
      let body = IMap.to_seq i_sched_tree |> List.of_seq |> List.map snd
                 |> List.map (List.map (fun x -> (x, List.nth bb_body' x)))
      in
      let body2 = List.fold_left (fun x b ->
          match IMap.find_opt b i_sched_tree with
          | Some i -> i :: x
          | None -> [] :: x
        ) [] (range (fst bb_st_e) (snd bb_st_e + 1))
        |> List.map (List.map (fun x -> (x, List.nth bb_body' x)))
        |> List.rev
      in
      (*let final_body = List.map (fun x -> subgraph dfg x |> order_instr) body in*)
      let final_body2 = List.map (fun x -> subgraph dfg x
                                           |> (fun x ->
                                               all_dfs x
                                               |> List.map (subgraph x)
                                               |> List.map (fun y ->
                                                   TopoDFG.fold (fun i l -> snd i :: l) y []
                                                   |> List.rev))) body2
                                           (*|> (fun x -> TopoDFG.fold (fun i l -> snd i :: l) x [])
                                           |> List.rev) body2*)
      in
      (separate_mem_operations final_body2)
  in
  PTree.map f c

let schedule entry (c : GibleSeq.code) =
  let debug = true in
  let transf_graph (_, dfg, _) = dfg in
  let _ = PTree.map1 gather_multiply_destinations c in
  (* SS.iter (fun a -> Printf.printf "%s\n" (reg a)) !multiply_dest; *)
  let c' = PTree.map1 (fun x -> gather_bb_constraints false x |> transf_graph) c in
  (*let _ = if debug then PTree.map (fun r o -> printf "##### %d #####\n%a\n\n" (P.to_int r) print_dfg o) c' else PTree.empty in*)
  let cgraph = PTree.elements c'
               |> List.map (function (x, y) -> (P.to_int x, y))
               |> List.fold_left (gather_cfg_constraints c) G.empty
  in
  (* let graph = open_out "constr_graph.dot" in *)
  (* fprintf graph "%a\n" GDot.output_graph cgraph; *)
  (* close_out graph; *)
  let schedule' = solve_constraints cgraph in
  (**IMap.iter (fun a b -> printf "##### %d #####\n%a\n\n" a (print_list print_tuple) b) schedule';*)
  (**printf "Schedule: %a\n" (fun a x -> IMap.iter (fun d -> fprintf a "%d: %a\n" d (print_list print_tuple)) x) schedule';*)
  transf_rtlpar c c' schedule'

(* let rec find_reachable_states c e = *)
(*   match PTree.get e c with *)
(*   | Some bb -> *)
(*     e :: List.fold_left (fun x a -> List.concat [x; find_reachable_states c a]) [] *)
(*       (all_successors bb |> List.filter (fun x -> P.lt x e)) *)
(*   | None -> assert false *)

let add_to_tree c nt i =
  match PTree.get i c with
  | Some p -> PTree.set i p nt
  | None -> assert false

let schedule_fn (f : GibleSeq.coq_function) : GiblePar.coq_function =
  let scheduled = schedule f.fn_entrypoint f.fn_code in
  (* let reachable = find_reachable_states scheduled f.fn_entrypoint *)
  (*                 |> List.to_seq |> SS.of_seq |> SS.to_seq |> List.of_seq in *)
  { fn_sig = f.fn_sig;
    fn_params = f.fn_params;
    fn_stacksize = f.fn_stacksize;
    fn_code = scheduled (*List.fold_left (add_to_tree scheduled) PTree.empty reachable*);
    fn_entrypoint = f.fn_entrypoint
  }
