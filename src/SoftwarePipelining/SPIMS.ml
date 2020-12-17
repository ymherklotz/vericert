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


open Graph.Pack.Digraph
open Basic

module NI = Map.Make (struct type t = G.V.t let compare = compare end)

let find key map def =
  try NI.find key map 
  with
    | Not_found -> def

let unpack v = 
  match v with
    | Some v -> v
    | None -> failwith "unpack abusif"
 
let dep_latency edge = 
  match edge_type edge with
    | IntraRAW | InterRAW -> latency (G.E.src edge)
    | _ -> 1

let estart ddg schedule node ii =
  let preds = G.pred_e ddg node in
  let starts = List.map (fun edge ->
			   match find (G.E.src edge) schedule None with
			     | Some t -> 
				 let start = t + dep_latency edge - ii * distance edge in
				 (*Printf.printf "start : %i \n" start;*)
				 if start < 0 then 0 else start 
			     | None -> 0
			) preds in
  List.fold_left (fun max e -> if max > e then max else e) 0 starts
    
let resource_conflict time mrt ii =
  match Array.get mrt (time mod ii) with 
    | None -> false
    | Some v -> true
	 
let rec scan_time time maxtime mrt ii =
    if time <= maxtime
    then 
      begin
	if resource_conflict time mrt ii
	then scan_time (time + 1) maxtime mrt ii
	else Some time
      end
    else None
      
let finished ddg schedule = 
  let unscheduled = G.fold_vertex (fun node l ->
				     match find node schedule None with
				       | Some v -> l
				       | None -> node :: l
				  ) ddg [] in
  (* Printf.printf "R %i R \n" (List.length unscheduled); *)
  if List.length unscheduled = 0 then true else false

let bad_successors ddg schedule node ii =
  let succs = G.succ_e ddg node in (* Le succs_ddg initial *) 
(*   let reftime = NI.find node schedule in *)
(*   let succs_sched = NI.fold (fun node time succs ->  *)
(* 			 if time > reftime then node :: succs else succs *)
(* 		      ) schedule [] in *)
(*  let succs = List.filter (fun edge -> List.mem (G.E.dst edge) succs_sched) succs_ddg in*)
  List.fold_right (fun edge bad ->
		     match find (G.E.dst edge) schedule None with
		       | Some t ->
			   if unpack (NI.find node schedule) + dep_latency edge - ii * distance edge > t
			   then (G.E.dst edge) :: bad
			   else bad
		       | None -> bad
		  ) succs []
    
let get_condition ddg = 
  let cond = G.fold_vertex (fun node cond ->
			      if is_cond node then Some node else cond
			   ) ddg None in
  match cond with
    | Some cond -> cond
    | None -> failwith "The loop does not contain a condition. Aborting\n"

let modulo_schedule heightr ddg min_ii max_interval =
  
  let ii = ref (min_ii - 1) in 
  let notfound = ref true in
  let sched = ref NI.empty in

  let cond = get_condition ddg in

  while (!ii < max_interval && !notfound) do
    (* Printf.printf "."; flush stdout;  *)
    ii := !ii + 1;
    (* Printf.printf "NOUVEAU II %i \n" !ii; *)
    let budget = ref (G.nb_vertex ddg * 10) in
    let lasttime = ref NI.empty in
    let schedtime = ref (NI.add cond (Some 0) NI.empty) in
    let mrt = Array.make !ii None in
    Array.set mrt 0 (Some cond);

    while (!budget > 0 && not (finished ddg !schedtime)) do (* Pretty inefficient *)
      budget := !budget - 1; 
      let h = heightr ddg !schedtime in
      let mintime = estart ddg !schedtime h !ii in
      (* Printf.printf "tmin (%s) = %i \n" (string_of_node h) mintime; *)
      let maxtime = mintime + !ii -1 in
      let time =  
	match scan_time mintime maxtime mrt !ii with
	  | Some t -> t
	  | None -> (*Printf.printf "backtrack" ; *)
	      if mintime = 0 then 1 + find h !lasttime 0
	      else max mintime (1 + find h !lasttime 0)
      in
      (* Printf.printf "Chosen time for %s : %i \n" (string_of_node h) time; *)
      schedtime := NI.add h (Some time) !schedtime;
      lasttime := NI.add h time !lasttime; 
      
      let killed = bad_successors ddg !schedtime h !ii in
      List.iter (fun n -> (* Printf.printf "Killing %s" (string_of_node n) ; *)schedtime := NI.add n None !schedtime) killed;
      
      begin
	match Array.get mrt (time mod !ii) with
	  | None -> Array.set mrt (time mod !ii) (Some h)
	  | Some n -> 
	      begin
		(*Printf.printf "Deleting : %s \n" (string_of_node n); *)
		(* Printf.printf "."; *)
		schedtime := NI.add n None !schedtime;
		Array.set mrt (time mod !ii) (Some h)
	      end
      end;
      (* if finished ddg !schedtime then Printf.printf "Fini ! \n" *)
    
    done;
    
    let success = G.fold_vertex (fun node b ->
				   b &&
				     match find node !schedtime None with
				       | Some _ -> true
				       | None -> false
				) ddg true in
    
    if success then (notfound := false; sched := !schedtime);
    
  done;
  
  if (not !notfound) 
  then (!sched,!ii)
  else failwith "IMS failure"
    
  
let res_m_ii ddg =
  G.nb_vertex ddg

let pipeliner ddg heightr =
  let mii = res_m_ii ddg in
  let (schedule,ii) = modulo_schedule heightr ddg mii (10 * mii) in
  (NI.fold (fun n v map -> 
	     match v with
	       | Some v -> NI.add n v map
	       | None -> failwith "pipeliner: schedule unfinished"
	  ) schedule NI.empty,ii)

let print_schedule sched =
  NI.iter (fun node time ->
	      Printf.fprintf Debug.dc "%s |---> %i \n" (string_of_node node) time
	   ) sched
    
