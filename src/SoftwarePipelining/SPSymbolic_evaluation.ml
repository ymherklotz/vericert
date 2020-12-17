(***********************************************************************)
(*                                                                     *)
(*                        Compcert Extensions                          *)
(*                                                                     *)
(*                       Jean-Baptiste Tristan                         *)
(*                                                                     *)
(*  All rights reserved.  This file is distributed under the terms     *)
(*  described in file ../../LICENSE.                                   *)
(*                                                                     *)
(***********************************************************************)


open Registers
open Op
open AST
open Base_types

type symbolic_value =
  | Sreg of reg
  | Sop of operation * symbolic_value list
  | Sload of memory_chunk * addressing * symbolic_value list * symbolic_mem
      
and symbolic_mem =
  | Smem 
  | Sstore of memory_chunk * addressing * symbolic_value list * symbolic_value * symbolic_mem

module State = Map.Make (struct type t = reg let compare = compare end)

module Cons = Set.Make (struct type t = symbolic_value let compare = compare end)

type symbolic_state = symbolic_value State.t * Cons.t

let initial_state = State.empty 
let initial_mem = Smem
let initial_cons = Cons.empty

exception Not_straight
  	
let find res st =
  try State.find res st
  with 
    | Not_found -> Sreg res

let rec get_args st = function
  | CList.Coq_nil -> []
  | CList.Coq_cons (arg,args) -> find arg st :: get_args st args
      
let rec symbolic_evaluation st sm cs = function
  | [] -> (st,sm,cs)
  | Inop :: l -> symbolic_evaluation st sm cs l

  | Iop (Omove, CList.Coq_cons (src,CList.Coq_nil), dst) :: l ->  
      symbolic_evaluation (State.add dst (find src st) st) sm cs l      

  | Iop (op, args, dst) :: l -> 
      let sym_val = Sop (op,get_args st args) in
      symbolic_evaluation (State.add dst sym_val st) sm (Cons.add sym_val cs) l

  | Iload (chunk, mode, args, dst) :: l  -> 
      let sym_val = Sload (chunk, mode, get_args st args, sm) in
      symbolic_evaluation (State.add dst sym_val st) sm (Cons.add sym_val cs) l

  | Istore (chunk, mode, args, src) :: l -> 
      let sym_mem = Sstore (chunk, mode, get_args st args, find src st, sm) in
      symbolic_evaluation st sym_mem cs l

  | _ :: l -> raise Not_straight

type osv =
  | Oresource of resource
  | Oop of operation 
  | Oload of memory_chunk * addressing 
  | Ostore of memory_chunk * addressing 

let string_of_osv = function
  | Oresource (Reg r) -> Printf.sprintf "reg %i" (Int32.to_int (Camlcoq.camlint_of_positive r))
  | Oresource Mem -> "mem" 
  | Oop op -> string_of_op op
  | Oload (mc,addr) -> "load" 
  | Ostore (mc,addr) -> "store"

type ident = int

module S = Graph.Persistent.Digraph.Abstract
  (struct type t = osv * ident end)

let name_of_vertex v = 
  let (osv,id) = S.V.label v in
  Printf.sprintf "%i" id 

let string_of_vertex v = 
  let (osv,_) = S.V.label v in
  Printf.sprintf "%s" (string_of_osv osv)

module DisplayTree = struct
  include S
  let vertex_name v =  name_of_vertex v
  let graph_attributes _ = [] 
  let default_vertex_attributes _ = []
  let vertex_attributes v = [`Label (string_of_vertex v)]
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end
module DotTree = Graph.Graphviz.Dot(DisplayTree)

let dot_output_ss g f = 
  let oc = open_out f in
  DotTree.output_graph oc g; 
  close_out oc

module Build = Graph.Builder.P (S)
module Op = Graph.Oper.Make (Build)

let counter = ref 0 

let rec convert_sv_rec sv graph = 
  incr counter;
  match sv with
    | Sreg res ->
	let node = S.V.create (Oresource (Reg res), !counter) in
	let graph = S.add_vertex graph node in
	(graph,node)
	  
    | Sop (op, svl) ->
	let node = S.V.create (Oop op, !counter) in
	let (graph, node_l) = List.fold_right (fun sv (graph,node_l) ->
						 let (graph,node) = convert_sv_rec sv graph in
						 graph, node :: node_l
					      ) svl (graph,[]) in
	let graph = S.add_vertex graph node in
	let graph = List.fold_right (fun n graph ->
				       S.add_edge graph node n
				    ) node_l graph in
	(graph,node)
	  
	  
    | Sload (mc,addr,svl,sm) -> 
	let node = S.V.create (Oload (mc, addr), !counter) in
	let (graph, node_l) = List.fold_right (fun sv (graph,node_l) ->
						 let (graph,node) = convert_sv_rec sv graph in
						 graph, node :: node_l
					      ) svl (graph,[]) in
	let (graph,node_m) = convert_sm_rec sm graph in  
	let graph = S.add_vertex graph node in
	let graph = List.fold_right (fun n graph ->
				       S.add_edge graph node n
				    ) node_l graph in
	let graph = S.add_edge graph node node_m in 
	(graph,node)
	  	  	  
and convert_sm_rec sm graph =
  incr counter;
  match sm with 
    | Smem ->
	let node = S.V.create (Oresource Mem, !counter) in
	let graph = S.add_vertex graph node in
	(graph,node)
	    
    | Sstore (mc,addr,svl,sv,sm) ->
	let node = S.V.create (Ostore (mc, addr), !counter) in
	let (graph, node_l) = List.fold_right (fun sv (graph,node_l) ->
						 let (graph,node) = convert_sv_rec sv graph in
						 graph, node :: node_l
					      ) svl (graph,[]) in
	let (graph, n) = convert_sv_rec sv graph in
	let (graph, node_m) = convert_sm_rec sm graph in
	let graph = S.add_vertex graph node in
	let graph = List.fold_right (fun n graph ->
				       S.add_edge graph node n
				    ) node_l graph in
	let graph = S.add_edge graph node n in
	let graph = S.add_edge graph node node_m in
	(graph,node)
	  	  
let convert_sv sv = convert_sv_rec sv S.empty
let convert_sm sm = convert_sm_rec sm S.empty

let convert_sym st sm regs =
  let graph = State.fold (fun res sv g ->
			    if (not (List.mem res regs)) then g
			    else 
			      let (graph,head) = convert_sv sv in
			      incr counter;
			      let src = S.V.create (Oresource (Reg res), !counter) in
			      let graph = S.add_vertex graph src in
			      let graph = S.add_edge graph src head in
			      Op.union g graph
			 ) st S.empty
  in 
  let graph' = 
    let (graph,head) = convert_sm sm in
    incr counter;
    let src = S.V.create (Oresource Mem, !counter) in
    let graph = S.add_vertex graph src in
    let graph = S.add_edge graph src head in
    graph
  in
  Op.union graph graph'
    
let display_st name l regs =
  let (st,sm,_) = symbolic_evaluation initial_state initial_mem initial_cons l in
  let g = convert_sym st sm regs in
  let addr = Debug.name ^ name in
  dot_output_ss g addr  ;
  ignore (Sys.command ("(dot -Tpng " ^ addr ^ " -o " ^ addr  ^ ".png ; rm -f " ^ addr ^ ") & ")) (* & *)
  

let symbolic_equivalence (st1,sm1,cs1) (st2,sm2,cs2) regs =
  Printf.printf "|cs1| = %i - |cs2| = %i \n" (Cons.cardinal cs1) (Cons.cardinal cs2);
  (List.fold_right (fun res b ->
		     find res st1 = find res st2 && b
		  ) regs true
  && sm1 = sm2
  && Cons.equal cs1 cs2)

let symbolic_evaluation = symbolic_evaluation initial_state initial_mem initial_cons

let symbolic_condition i l =
  match i with
    | Icond (cond,args) ->
	let args = to_caml_list args in
	let (st,sm,cs) = symbolic_evaluation l in
	(cond,List.map (fun r -> find r st) args)
    | _ -> failwith "Not a condition !\n"  
