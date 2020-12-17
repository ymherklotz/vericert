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


open Basic
open IMS
open MVE
open RTL

let clean t = 

  let rec clean_rec i =
    match i with 
      | 0 -> []
      | n -> 
	  begin
	    match t.(i - 1) with
	      | None -> clean_rec (i - 1)
	      | Some inst -> inst :: clean_rec (i - 1) 
	  end
  in
  let l = List.rev (clean_rec (Array.length t)) in
  List.hd l :: (List.filter (fun e -> not (is_cond e)) (List.tl l))

let print_nodes = List.iter (fun n -> Printf.printf "%s \n" (string_of_node n))  
 
(* random heuristic *)
 
let find node schedule opt =
  try NI.find node schedule with
    | Not_found -> opt

let random ddg schedule = 
  let unscheduled = G.fold_vertex (fun node l ->
				     match find node schedule None with 
				       | Some v -> l
				       | None -> node :: l 
				  ) ddg [] in
  let bound = List.length unscheduled in 
  Random.self_init (); 
  List.nth unscheduled (Random.int bound)

(* tought heuristics *)
 
module Topo = Graph.Topological.Make (G)
module Scc = Graph.Components.Make (G)

let order = ref []

let pipeliner ddg =  
  order := List.flatten (Scc.scc_list ddg);
  let (sched,ii) = IMS.pipeliner ddg random in
  let (steady,prolog,epilog,min,unroll,entrance,way_out) = MVE.mve ddg sched ii in
  let steady_state = clean steady in
  if min <= 0 then None 
  else
    Some {steady_state = steady_state; prolog = prolog; epilog = epilog; min = min; unrolling = unroll;
	 ramp_up = entrance; ramp_down = way_out}
      

let main f = 
  Basic.apply_pipeliner f pipeliner ~debug:false

  

