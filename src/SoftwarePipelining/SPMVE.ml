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

module Mult = Map.Make (struct type t = reg let compare = compare end)
 
let size_of_map1 m = 
  NI.fold (fun key v size -> size + 1) m 0

let size_of_map2 m = 
  Mult.fold (fun key v size -> size + 1) m 0

let sched_max_time sched = 
  NI.fold (fun node time max ->
	     if time > max then time else max
	  ) sched 0 

let print_table t s =
  Printf.fprintf Debug.dc "%s : \n" s;
  let string_of_node_ev node = 
    match node with
      | Some node -> string_of_node node
      | None -> "_"
  in
  Array.iteri (fun i node -> Printf.fprintf Debug.dc "%i :: %s \n" i (string_of_node_ev node)) t

let durations ddg sched ii =
  
  G.fold_vertex (fun node mult ->
		   match written node with 
		     | None -> mult
		     | Some r -> 
			 let raw_succs = get_succs_raw ddg node in
			 let durations = List.map (fun succ -> 
						     let d = NI.find succ sched - NI.find node sched in
						     if d >= 0 then d 
						     else ((sched_max_time sched - NI.find node sched) + NI.find succ sched)
						  ) raw_succs in
			 let duration = List.fold_left (fun max e -> if max > e then max else e) 0 durations in
			 Mult.add r ((duration / ii) + 1) mult (* cette division est surement fdausse*)
		) ddg Mult.empty

let minimizer qi ur =
  
  let rec fill n = 
    if n <= ur then n :: fill (n + 1) else []
  in

  let l = fill qi in
  let l = List.map (fun e -> (e,ur mod e)) l in
  let l = List.filter (fun e -> snd e = 0) l in
  let l = List.map fst l in
  List.fold_left (fun min e -> if min < e then min else e) ur l
  
let multiplicity ddg sched ii =
  let qs = durations ddg sched ii in
(*   Printf.printf "Quantite de variables necessaires : \n"; *)
(*   Mult.iter (fun key mu -> print_reg key ; Printf.printf " |-> %i\n" mu) qs; *)
  let unroll = Mult.fold (fun reg mult max ->
			    if mult > max then mult else max
			 ) qs 0 in
  let mult = Mult.fold (fun reg mult mult -> 
			 Mult.add reg (minimizer (Mult.find reg qs) unroll) mult 
		      ) qs Mult.empty 
  in
  (mult,unroll)
 
let mve_kernel t ddg sched ii mult unroll =
  
  let regs = Array.make ii (fresh_regs 0) in  
  for i = 0 to (ii - 1) do
    let fregs = fresh_regs unroll in
    Array.iter print_reg  fregs;
    Printf.fprintf Debug.dc "\n"; 
    Array.set regs i fregs
  done;

  let used_regs = ref [] in

  let index r i = Mult.find r mult - ( ((i / ii) + 1) mod Mult.find r mult) in
(*   let pos i node inst =  *)
(*     let separation =  *)
(*       let b= NI.find node sched - NI.find inst sched in *)
(*       if b >= 0 then b *)
(*       else ((sched_max_time sched - NI.find inst sched) + NI.find node sched)  *)
(*     in *)
(*     (i + separation) mod (ii * unroll) in   *)

  let new_t = Array.copy t in

  for i = 0 to (Array.length t - 1) do
    (* print_table new_t "Nouvelle table"; *)
    match t.(i),new_t.(i) with
      | Some insti, Some insti_mod ->
	  begin 
	    match written insti with
	      | None -> ()
	      | Some r -> 
		  begin
		    let new_reg = 
		      if Mult.find r mult = 0 then r 
		      else regs.(i mod ii).(index r i - 1) in
		    if (not (List.mem (r,new_reg) !used_regs)) then used_regs := (r,new_reg) :: !used_regs;
		    let inst = reforge_writes insti_mod new_reg in 
		    Printf.fprintf Debug.dc "Reecriture : %s --> %s \n" (string_of_node insti) (string_of_node inst);  
		    Array.set new_t i (Some inst);
		    let succs = get_succs_raw ddg insti in 
		    List.iter (fun node ->

		(* 		 let lifetime =  *)
(* 				   let d = NI.find node sched - NI.find insti sched in *)
(* 				   if d >= 0 then d  *)
(* 				   else ((sched_max_time sched - NI.find insti sched) + 1 + NI.find node sched) *)
(* 				 in *)
				 

				 (* ___Version 1___ *)
				 (* let lifetime = lifetime / ii in *)
(* 				 let schedtime =  *)
(* 				   ((NI.find node sched) mod ii) (\* Position dans le premier bloc *\) *)
(* 				   + (ii * (i / ii))           (\* Commencement du bloc ou on travail *\) *)
(* 				   + (ii * lifetime )     (\* Decalage (Mult.find r mult - 1)  *\) *)
(* 				   + ((if (NI.find node sched mod ii) < (NI.find insti sched mod ii) then 0 else 0) * ii) *)
(* 				 in *)

				 (* Printf.printf "seed = %i - bloc = %i - slide = %i - corr = %i - id = %i \n" *)
(* 				    ((NI.find node sched) mod ii) *)
(* 			 	   (ii * (i / ii)) (ii * lifetime) *)
(* 				 ((if (NI.find node sched mod ii) < (NI.find insti sched mod ii) then 1 else 0 ) * ii)  *)
(* 				 id; *)
(* 			 	 Printf.printf "Successeur a traiter : %s ooo %i ooo\n" (string_of_node node) (Mult.find r mult); *)

				 (* ___Version 2___ *)
	 			 let schedtime = 
				   if (NI.find node sched > NI.find insti sched)
				   then i + (NI.find node sched - NI.find insti sched) 
				   else i - NI.find insti sched + ii + NI.find node sched
				     (* let delta = NI.find insti sched - NI.find node sched in *)
(* 				     (i - delta) + (((delta / ii) + 1) * ii) (\* (i - delta) + ii*\) *)
				 in

				 (*   then  *)

				 Printf.fprintf Debug.dc "i = %i - def = %i - use = %i - time = %i \n"
				   i (NI.find insti sched) (NI.find node sched) schedtime;
				 

 				 (* let id = pos i node insti in *)
				 let id = schedtime mod (unroll * ii) (* le tout modulo la tabl *) in
				 let id = (id + (unroll * ii)) mod (unroll * ii) in 
 			 	 Printf.fprintf Debug.dc "Positions to treat : %i \n" id; 
				 let insttt = match new_t.(id) with
				   | Some inst -> inst
				   | None -> failwith "There should be an instruction" 
				 in
				 let inst = reforge_reads insttt r new_reg in
				 Array.set new_t id (Some inst)
			      ) succs
		  end
	  end
      | None, _ -> ()
      | _, None -> failwith "MVE : qqch mal compris"
  done;
  new_t,!used_regs

let crunch_and_unroll sched ii ur =
  let steady_s = Array.make ii None in
  NI.iter (fun inst time -> 
	     Array.set steady_s (time mod ii) (Some inst) 
	  ) sched;
  (* Printf.printf "Etat stable : \n"; *)
(*   let string_of_node_ev node =  *)
(*     match node with *)
(*       | Some node -> string_of_node node *)
(*       | None -> "_" *)
(*   in   *)
(*   Array.iteri (fun i node -> Printf.printf "%i :: %s \n" i (string_of_node_ev node)) steady_s; *)
  let steady = Array.make (ii * ur) None in
  for i = 0 to (ur - 1) do
    for time = 0 to (ii - 1) do
      Array.set steady (time + i * ii) (steady_s.(time)) 
    done
  done;
  steady

let compute_iteration_table sched ii =
  let t = Array.make ii None in
  NI.iter (fun node time ->
	     Array.set t (NI.find node sched mod ii) (Some ((NI.find node sched / ii) + 1))
	  ) sched;
  t

let compute_prolog steady min ii unroll schedule it =
 
  let prolog = ref [] in
  let prolog_piece = ref [] in

  for i = (min - 1) downto 0 do
    
    let index = ((ii * (unroll - (min - i)))) mod (unroll * ii)  in
    prolog_piece := [];

    for j = 0 to (ii - 1) do (* copie du sous tableau *)
      (* Printf.printf "i : %i - j : %i - index : %i \n" i j index; *)
      match steady.(index + j), it.(j) with
	| Some inst , Some iter ->
	    if iter <= (i + 1) then prolog_piece := inst :: !prolog_piece; (* i + 1 au lieu de i *)
	| None, _ -> ()
	| _, _ -> failwith "compute_prolog: quelquechose est mal compris"
    done;

    prolog := List.rev (!prolog_piece) @ !prolog
  done;

  !prolog


let compute_epilog steady min ii unroll schedule it = 
 
  let epilog = ref [] in 

  for i = 0 to (min - 1) do
    let index = (i mod unroll) * ii in
    for j = 0 to (ii - 1) do 
      match steady.(index + j), it.(j) with
	| Some inst , Some iter ->
	    if iter > (i + 1) then epilog := inst :: !epilog;  
	| None, _ -> ()
	| _, _ -> failwith "compute_prolog: quelquechose est mal compris"
    done;
  done;
  List.rev (!epilog)
      
let entrance = List.map (fun (a,b) -> (b,a)) 

let way_out prolog epilog used_regs =
  let l = List.rev (prolog @ epilog) in
  
  let rec way_out_rec l wo =
    match l with
      | [] -> wo
      | i :: l -> 
	  begin
	    match written i with
	      | Some r -> 
		  let mov = List.find (fun (a,b) -> r = b) used_regs in
		  if List.mem mov wo 
		  then way_out_rec l wo
		  else way_out_rec l (mov :: wo)
	      | None -> way_out_rec l wo
	  end
  in
  
  way_out_rec l []

let mve ddg sched ii =
  assert (size_of_map1 sched = G.nb_vertex ddg);
  Printf.fprintf Debug.dc "L'intervalle d'initiation est de : %i \n" ii;
  Printf.fprintf Debug.dc "L'ordonnancement est le suivant : \n";
  print_schedule sched;
  let (mult,unroll) = multiplicity ddg sched ii in  
  let unroll = unroll in  (* changer pour tester, default doit etre egal a unroll *)
  Printf.fprintf Debug.dc "Table de multiplicite : \n";
  Mult.iter (fun key mu -> print_reg key ; Printf.fprintf Debug.dc " |-> %i\n" mu) mult;
  Printf.fprintf Debug.dc "Taux de deroulement de : %i \n" unroll;
  let steady_state = crunch_and_unroll sched ii unroll in
  let (steady_state,used_regs) = mve_kernel steady_state ddg sched ii mult unroll in
  print_table steady_state "Table finale"; 
  let min = ((sched_max_time sched) / ii) + 1 in
  Printf.fprintf Debug.dc "min : %i \n" min; 
  let iteration_table = compute_iteration_table sched ii in
  Printf.fprintf Debug.dc "Table d'iteration \n";
  Array.iteri (fun i elt ->
		 match elt with
		   | Some elt ->
		       Printf.fprintf Debug.dc "%i : %i\n" i elt
		   | None -> Printf.fprintf Debug.dc "%i : _ \n" i
	      ) iteration_table;
  let prolog = compute_prolog steady_state min ii unroll sched iteration_table in
  let prolog = List.filter (fun e -> not (is_cond e)) prolog in
  let epilog = compute_epilog steady_state min ii unroll sched iteration_table in
  let epilog = List.filter (fun e -> not (is_cond e)) epilog in
  Printf.fprintf Debug.dc "Prologue: \n"; 
  List.iter (fun node -> Printf.fprintf Debug.dc "%s \n" (string_of_node node)) prolog; 
  Printf.fprintf Debug.dc "Epilogue: \n"; 
  List.iter (fun node -> Printf.fprintf Debug.dc "%s \n" (string_of_node node)) epilog;  
  let way_out = way_out prolog epilog used_regs in
  (steady_state,prolog,epilog,min - 1,unroll,entrance used_regs, way_out)


  
