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


open Lengauer
open RTL
open Camlcoq
open Graph.Pack.Digraph
open Op
open Registers
open Mem
open AST
open Base_types
open Symbolic_evaluation

type node = instruction * int
module G = Graph.Persistent.Digraph.AbstractLabeled
  (struct type t = node end)
  (struct type t = int let compare = compare let default = 0 end)
module Topo = Graph.Topological.Make (G) 
module Index = Map.Make (struct type t = int let compare = compare end)

let string_of_instruction node =
  match G.V.label node with
  | (Inop,n) -> Printf.sprintf "%i nop" n
  | (Iop (op, args, dst),n) -> Printf.sprintf "%i r%i := %s %s" n (to_int dst) (string_of_op op) (string_of_args args)
  | (Iload (chunk, mode, args, dst),n) -> Printf.sprintf "%i r%i := load %s" n (to_int dst) (string_of_args args)
  | (Istore (chunk, mode, args, src),n) -> Printf.sprintf "%i store %i %s" n (to_int src) (string_of_args args)
  | (Icall (sign, id, args, dst),n) -> Printf.sprintf "%i call" n
  | (Itailcall (sign, id, args),n) -> Printf.sprintf "%i tailcall" n
  | (Ialloc (dst, size),n) -> Printf.sprintf "%i %i := alloc" n (to_int dst)
  | (Icond (cond, args),n) -> Printf.sprintf "%i cond %s %s" n (string_of_cond cond) (string_of_args args)
  | (Ireturn (res),n) -> Printf.sprintf "%i return" n

let string_of_node = string_of_instruction

module Display = struct
  include G
  let vertex_name v = print_inst (V.label v)
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes v = [`Label (string_of_instruction v)]
  let default_edge_attributes _ = []
  let edge_attributes e = [`Label (string_of_int (G.E.label e))]
  let get_subgraph _ = None
end
module Dot_ = Graph.Graphviz.Dot(Display)

let dot_output g f = 
  let oc = open_out f in
  Dot_.output_graph oc g; 
  close_out oc

let display g name =
  let addr = Debug.name ^ name in
  dot_output g addr  ;
  ignore (Sys.command ("(dot -Tpng " ^ addr ^ " -o " ^ addr  ^ ".png ; rm -f " ^ addr ^ ") & "))

(******************************************)
 
type cfg = {graph : G.t; start : G.V.t}


(* convert traduit un graphe RTL compcert en un graphe RTL ocamlgraph*)

let convert f  = 

  let make_node inst key =
    let inst = inst_coq_to_caml inst in
    G.V.create (inst, to_int key)
  in

  let (graph, index) = Maps.PTree.fold (fun (g,m) key inst -> 
			 let node = make_node inst key in
			 (G.add_vertex g node, Index.add (to_int key) node m)
		      ) f.fn_code (G.empty,Index.empty) 
  in

  let succ = RTL.successors f in
  let rec link n succs g =
    match succs with
      | CList.Coq_nil -> g
      | CList.Coq_cons (pos,CList.Coq_nil) -> 
	  G.add_edge g (Index.find (to_int n) index) (Index.find (to_int pos) index)
      | CList.Coq_cons (pos1, (CList.Coq_cons (pos2,CList.Coq_nil))) ->
	  let g = G.add_edge_e g (G.E.create (Index.find (to_int n) index) 1 (Index.find (to_int pos1) index)) in
	  G.add_edge_e g (G.E.create (Index.find (to_int n) index) 2 (Index.find (to_int pos2) index))
      | _ -> failwith "convert : trop de successeurs"
	 
  in

  let graph = Maps.PTree.fold ( fun g key inst ->
				  link key (succ key) g
			      ) f.fn_code graph
  in
  
  {graph = graph; start = Index.find (to_int (f.fn_entrypoint)) index}
 
 
let convert_back g =
   
    G.fold_vertex (fun node m ->
	 	     let v = G.V.label node in
		     match (fst v) with
		       | Icond (_,_) ->
			   begin
			     let l = 
			       match G.succ_e g node with
				 | [e1;e2] -> 
				     if G.E.label e1 > G.E.label e2 
				     then [G.E.dst e2;G.E.dst e1]
				     else [G.E.dst e1;G.E.dst e2]
				 | _ -> failwith "convert_back: nombre de successeurs incoherent"
			     in
			     let succs = List.map (fun s -> to_binpos (snd (G.V.label s))) l in
			     Maps.PTree.set (to_binpos (snd v)) (inst_caml_to_coq (fst v) succs) m
			   end
		       | _ ->
			   let succs = List.map (fun s -> to_binpos (snd (G.V.label s))) (G.succ g node) in
			   Maps.PTree.set (to_binpos (snd v)) (inst_caml_to_coq (fst v) succs) m
		  ) g Maps.PTree.empty

 
  

(* dominator_tree calcule l arbre de domination grace au code de FP *)
let dominator_tree f =
    
  let module X =
    struct 
      type node = G.V.t
      let n = G.nb_vertex f.graph 
      let index (node : G.V.t) = snd(G.V.label node) - 1
      let successors fu n =
	List.iter fu (G.succ f.graph n) 
      let predecessors fu n = 
	List.iter fu (G.pred f.graph n)
      let start = f.start 
    end
  in 

  let module Y = Lengauer.Run (X) 

  in 
 
  Y.dominator
 

   
(* detect_loops, find the loops in the graph and returns the list of nodes in it,
   in dominating order !!! This is of great importance, we suppose that it is ordered
   when we build the dependency graph *)
let detect_loops graph dom_tree =
  
  let rec is_dominating v1 v2 l = (* does v1 dominates v2 *)
    match dom_tree v2 with
      | None -> None
      | Some v -> if v1 = v then Some (v :: l) else is_dominating v1 v (v :: l)
  in

  G.fold_edges (fun v1 v2 loops -> 
		  match is_dominating v2 v1 [v1] with
		    | None -> loops
		    | Some loop -> (v2,loop) :: loops
	       ) graph []
    
let print_index node =
  Printf.printf "%i " (snd (G.V.label node))

let print_instruction node = 
  match G.V.label node with
  | (Inop,n) -> Printf.printf "%i : Inop \n" n 
  | (Iop (op, args, dst),n) -> Printf.printf "%i : Iop  \n" n  
  | (Iload (chunk, mode, args, dst),n) -> Printf.printf "%i : Iload \n" n    
  | (Istore (chunk, mode, args, src),n) -> Printf.printf "%i : Istore \n" n    
  | (Icall (sign, id, args, dst),n) -> Printf.printf "%i : Icall \n" n   
  | (Itailcall (sign, id, args),n) -> Printf.printf "%i : Itailcall \n" n   
  | (Ialloc (dst, size),n) -> Printf.printf "%i : Ialloc \n" n  
  | (Icond (cond, args),n) -> Printf.printf "%i : Icond \n" n    
  | (Ireturn (res),n) -> Printf.printf "%i : Ireturn \n" n   
 
let is_rewritten node r = 
  match fst (G.V.label node) with
    | Inop -> false
    | Iop (op, args, dst) -> if dst = r then true else false
    | Iload (chunk, mode, args, dst) -> if dst = r then failwith "J'ai degote une boucle ZARBI !!!" else false
    | Istore (chunk, mode, args, src) -> false
    | Icall (sign, id, args, dst) -> failwith "call in a loop"
    | Itailcall (sign, id, args) -> failwith "tailcall in a loop"
    | Ialloc (dst, size) -> if dst = r then failwith "J'ai degote une boucle ZARBI !!!" else false
    | Icond (cond, args) -> false 
    | Ireturn (res) -> failwith "return in a loop"

let is_variant r loop = 
  List.fold_right (fun node b -> 
		     is_rewritten node r || b
		  ) loop false


let is_pipelinable loop = (* true if loop is innermost and without control *)
 
  let is_acceptable node =
    match fst (G.V.label node) with
      | Icall _ | Itailcall _ | Ireturn _ | Icond _ | Ialloc _ | Iop ((Ocmp _),_,_)-> false
      | _ -> true
  in
	  
  let is_branching node = 
    match fst (G.V.label node) with
      | Icond _ -> true
      | _ -> false
  in

  let is_nop node = 
    match fst (G.V.label node) with
      | Inop -> true
      | _ -> false
  in

  let is_OK_aux l =
    List.fold_right (fun n b -> is_acceptable n && b) l true
  in

  let is_bounded node loop =
    match G.V.label node with
      | (Icond (cond, args),n) -> 
	  let args = to_caml_list args in
	  begin
	    match args with 
	      | [] -> false
	      | r :: [] -> not (is_variant r loop) 
	      | r1 :: r2 :: [] ->
		  begin
		    match is_variant r1 loop, is_variant r2 loop with
		      | true, true -> false
		      | false, true -> true
		      | true, false -> true
		      | false, false -> false
		  end
	      | _ -> false
	  end
      | _ -> false
  in

  match loop with
    | v1 :: v2 :: l -> is_nop v1 && is_branching v2 && is_OK_aux l && is_bounded v2 loop
    | _ -> false
 
let print_loops loops = 
  List.iter (fun loop -> print_index (fst(loop));
	                 print_newline ();
	                 List.iter print_index (snd(loop));
			 print_newline ();
			 if is_pipelinable (snd(loop)) then print_string "PIPELINABLE !" else print_string "WASTE";
			 print_newline ();
			 List.iter print_instruction (snd(loop));
			 print_newline ()
	    ) loops
 
(* type resource = Reg of reg | Mem *)
module Sim = Map.Make (struct type t = resource let compare = compare end)

let map_get key map =
  try Some (Sim.find key map) 
  with
    | Not_found -> None

let rec to_res l = 
  match l with
    | CList.Coq_nil -> []
    | CList.Coq_cons (e,l) -> Reg e :: to_res l

let resources_reads_of node = 
  match fst (G.V.label node) with
    | Inop -> []
    | Iop (op, args, dst) -> to_res args 
    | Iload (chunk, mode, args, dst) -> Mem :: (to_res args) 
    | Istore (chunk, mode, args, src) -> Mem :: Reg src :: (to_res args)
    | Icall (sign, id, args, dst) -> failwith "Resource read of call"
    | Itailcall (sign, id, args) -> failwith "Resource read of tailcall"
    | Ialloc (dst, size) -> [Mem] 
    | Icond (cond, args) -> to_res args
    | Ireturn (res) -> failwith "Resource read of return"
    
let resources_writes_of node = 
  match fst (G.V.label node) with
    | Inop -> []
    | Iop (op, args, dst) -> [Reg dst]
    | Iload (chunk, mode, args, dst) -> [Reg dst]
    | Istore (chunk, mode, args, src) -> [Mem]
    | Icall (sign, id, args, dst) -> failwith "Resource read of call"
    | Itailcall (sign, id, args) -> failwith "Resource read of tailcall"
    | Ialloc (dst, size) -> (Reg dst) :: [Mem]
    | Icond (cond, args) -> []
    | Ireturn (res) -> failwith "Resource read of return"
 
let build_intra_dependency_graph loop =
  
  let rec build_aux graph read write l = 
    match l with
      | [] -> (graph,(read,write))
      | v :: l-> 
	  let g = G.add_vertex graph v in
	  let reads = resources_reads_of v in
	  let writes = resources_writes_of v in
	  (* dependances RAW *)
	  let g = List.fold_right (fun r g -> 
				     match map_get r write with
				       | Some n -> G.add_edge_e g (G.E.create n 1 v)
				       | None -> g
				  ) reads g in
	  (* dependances WAR *)
	  let g = List.fold_right (fun r g ->
				     match map_get r read with
				       | Some l -> List.fold_right (fun n g -> G.add_edge_e g (G.E.create n 2 v)) l g
				       | None -> g
				  ) writes g in
	  (* dependances WAW *)
	  let g = List.fold_right (fun r g ->
				     match map_get r write with
				       | Some n -> G.add_edge_e g (G.E.create n 3 v)
				       | None -> g
				  ) writes g in
	  let write = List.fold_right (fun r m -> Sim.add r v m) writes write in
	  let read_tmp = List.fold_right (fun r m -> 
					    match map_get r read with
					      | Some al -> Sim.add r (v :: al) m
					      | None -> Sim.add r (v :: []) m
					 ) reads read 
	  in
	  let read = List.fold_right (fun r m -> Sim.add r [] m) writes read_tmp in 
	  
	  build_aux g read write l
  in

  build_aux G.empty Sim.empty Sim.empty (List.tl loop) 
  
let build_inter_dependency_graph loop =

  let rec build_aux2 graph read write l = 
    match l with
      | [] -> graph
      | v :: l-> 
	  let g = graph in
	  let reads = resources_reads_of v in
	  let writes = resources_writes_of v in
	  (* dependances RAW *)
	  let g = List.fold_right (fun r g -> 
				     match map_get r write with
				       | Some n -> (* if n = v then g else *) G.add_edge_e g (G.E.create n 4 v)
				       | None -> g
				  ) reads g in
	  (* dependances WAR *)
	  let g = List.fold_right (fun r g ->
				     match map_get r read with
				       | Some l -> List.fold_right 
					   (fun n g -> (* if n = v then g else *) G.add_edge_e g (G.E.create n 5 v)) l g
				       | None -> g
				  ) writes g in
	  (* dependances WAW *)
	  let g = List.fold_right (fun r g ->
				     match map_get r write with
				       | Some n -> (* if n = v then g else *) G.add_edge_e g (G.E.create n 6 v)
				       | None -> g
				  ) writes g in
	  let write = List.fold_right (fun r m -> Sim.remove r m) writes write in
	  let read = List.fold_right (fun r m -> Sim.remove r m) writes read in

	  
	  build_aux2 g read write l
  in

  let (g,(r,w)) = build_intra_dependency_graph loop in
  build_aux2 g r w (List.tl loop)
 
(* patch_graph prepare le graphe pour la boucle commencant au noeud entry 
   qui a une borne de boucle bound et pour un software pipelining
   de au minimum min tours et de deroulement ur *)
(* this is rather technical so we give many comments *)

(*   let n1 = G.V.create (Iop ((Ointconst ur),to_coq_list [],r1),next_pc) in *)
(*   let next_pc = next_pc + 1 in *)
(*   let n2 = G.V.create (Iop (Odiv,to_coq_list [bound;r1],r2),next_pc) in *)
(*   let next_pc = next_pc + 1 in *)
(*   let n3 = G.V.create (Iop ((Omulimm ur),to_coq_list [r2],r3),next_pc) in *)
(*   let next_pc = next_pc + 1 in *)
(*   let n4 = G.V.create (Iop (Osub,to_coq_list [bound;r3],r4),next_pc) in *)
(*   let next_pc = next_pc + 1 in *)
(*   let n5 = G.V.create (Iop (Omove,to_coq_list [r3],bound),next_pc) in (\* retouchee, [r3],bound *\) *)


let patch_graph graph entry lastone loop bound min ur r1 r2 r3 r4 next_pc prolog epilog ramp_up ramp_down =

  (* 1. Break the edge that enters the loop, except for the backedge *)
  let preds_e = G.pred_e graph entry in
  let wannabes = List.map G.E.src preds_e in 
  let wannabes = List.filter (fun e -> not (e = lastone)) wannabes in
  let graph = List.fold_right (fun e g -> G.remove_edge_e g e) preds_e graph in
  let graph = G.add_edge graph lastone entry in
  
  (* 2. Add the test for minimal iterations and link it*)

  let cond = G.V.create (Icond ((Ccompimm (Integers.Cle,min)),to_coq_list [bound]), next_pc) in
  let graph = G.add_vertex graph cond in
  let next_pc = next_pc + 1 in

  (* 3. Link its predecessors and successors *)
  (* It is false in case there is a condition that points to the entry:
     inthis case, the edge should not be labeled with 0 !*)
 
  let graph = List.fold_right (fun n g -> G.add_edge g n cond) wannabes graph in
  let graph = G.add_edge_e graph (G.E.create cond 1 entry) in

  
  (* 4. Add the div and modulo code, link it *)
  let n1 = G.V.create (Iop ((Ointconst ur),to_coq_list [],r1),next_pc) in
  let next_pc = next_pc + 1 in
  let n2 = G.V.create (Iop (Odiv,to_coq_list [bound;r1],r2),next_pc) in
  let next_pc = next_pc + 1 in
  let n3 = G.V.create (Iop (Omove,to_coq_list [bound],r4),next_pc) in
  let next_pc = next_pc + 1 in
  let n4 = G.V.create (Iop ((Omulimm ur ),to_coq_list [r2],r3),next_pc) in
  let next_pc = next_pc + 1 in
  let n5 = G.V.create (Iop ((Oaddimm (Camlcoq.z_of_camlint (Int32.of_int (-1)))),to_coq_list [r3],bound),next_pc) in (* retouchee, [r3],bound *)
  let next_pc = next_pc + 1 in
  let graph = G.add_vertex graph n1 in
  let graph = G.add_vertex graph n2 in
  let graph = G.add_vertex graph n3 in
  let graph = G.add_vertex graph n4 in
  let graph = G.add_vertex graph n5 in
  let graph = G.add_edge_e graph (G.E.create cond 2 n1) in
  let graph = G.add_edge graph n1 n2 in
  let graph = G.add_edge graph n2 n3 in
  let graph = G.add_edge graph n3 n4 in
  let graph = G.add_edge graph n4 n5 in
 
  (* 5. Fabriquer la pipelined loop et la linker, sans la condition d entree *)
  
  let (graph,next_pc,l) = List.fold_right (fun e (g,npc,l) -> 
					   let n = G.V.create (e,npc) in
					   (G.add_vertex g n, npc+1, n :: l)
					) loop (graph,next_pc,[]) in

  let pipe_cond = List.hd l in
  let pipeline = List.tl l in
  
  let rec link l graph node =
    match l with
      | n1 :: n2 :: l -> link (n2 :: l) (G.add_edge graph n1 n2) node 
      | n1 :: [] -> G.add_edge graph n1 node
      | _ -> graph
  in
  
  let graph = link pipeline graph pipe_cond in
  
  (* link de l entree de la boucle *)
  
  let (graph,next_pc,prolog) = List.fold_right (fun e (g,npc,l) -> 
					   let n = G.V.create (e,npc) in
					   (G.add_vertex g n, npc+1, n :: l)
					) prolog (graph,next_pc,[]) in

  let (graph,next_pc,epilog) = List.fold_right (fun e (g,npc,l) -> 
					   let n = G.V.create (e,npc) in
					   (G.add_vertex g n, npc+1, n :: l)
					) epilog (graph,next_pc,[]) in

  (* 6. Creation du reste et branchement et la condition *)
  let n6 = G.V.create (Iop (Omove,to_coq_list [r4],bound),next_pc) in (* Iop (Omove,to_coq_list [r4],bound) *)
  let next_pc = next_pc + 1 in
  
  (* 7. Creation du ramp up *)
  let ramp_up = List.map (fun (a,b) -> Iop (Omove,CList.Coq_cons (b,CList.Coq_nil),a)) ramp_up in
  let (graph,next_pc,ramp_up) = List.fold_right (fun e (g,npc,l) -> 
					   let n = G.V.create (e,npc) in
					   (G.add_vertex g n, npc+1, n :: l)
					) ramp_up (graph,next_pc,[]) in

  let next_pc = next_pc + 1 in

  let ramp_down = List.map (fun (a,b) -> Iop (Omove,CList.Coq_cons (b,CList.Coq_nil),a)) ramp_down in
  let (graph,next_pc,ramp_down) = List.fold_right (fun e (g,npc,l) -> 
					   let n = G.V.create (e,npc) in
					   (G.add_vertex g n, npc+1, n :: l)
					) ramp_down (graph,next_pc,[]) in

  (* let next_pc = next_pc + 1 in *)

  (* Creation des proloque et epilogue *)

  let graph = link prolog graph pipe_cond in
  let graph = link ramp_up graph (List.hd prolog) in
  let graph = link epilog graph (List.hd ramp_down) in
  let graph = link ramp_down graph n6 in


  let graph = G.add_edge graph n5 (List.hd ramp_up) in
  let graph = G.add_edge_e graph (G.E.create pipe_cond 1 (List.hd epilog)) in
  let graph = G.add_edge_e graph (G.E.create pipe_cond 2 (List.hd pipeline)) in

  (* 8. Retour sur la boucle classique *)
  let graph = G.add_edge graph n6 entry in

  graph
       
let regs_of_node node = 
  match G.V.label node with
  | (Inop,n) -> []
  | (Iop (op, args, dst),n) -> dst :: (to_caml_list args)
  | (Iload (chunk, mode, args, dst),n) -> dst :: (to_caml_list args)
  | (Istore (chunk, mode, args, src),n) -> src :: (to_caml_list args)
  | (Icall (sign, id, args, dst),n) -> dst :: (to_caml_list args)
  | (Itailcall (sign, id, args),n) -> (to_caml_list args)
  | (Ialloc (dst, size),n) -> [dst]
  | (Icond (cond, args),n) -> (to_caml_list args)
  | (Ireturn (res),n) -> match res with Datatypes.Some res -> [res] | _ -> [] 

let max_reg_of_graph graph params =
  Printf.fprintf Debug.dc "Calcul du registre de depart.\n";
  let regs =  G.fold_vertex (fun node regs ->
			       (regs_of_node node) @ regs
			    ) graph [] in
  let regs = regs @ params in
  let max_reg = List.fold_right (fun reg max ->
				   Printf.fprintf Debug.dc "%i " (Int32.to_int (Camlcoq.camlint_of_positive reg));
				   if Int32.compare (Camlcoq.camlint_of_positive reg) max > 0 
				   then (Camlcoq.camlint_of_positive reg)
				   else max
				) regs Int32.zero in
  
  Printf.fprintf Debug.dc "MAX REG = %i\n" (Int32.to_int max_reg);
  BinPos.coq_Psucc (Camlcoq.positive_of_camlint max_reg)
 
let get_bound node loop =
  match G.V.label node with
    | (Icond (cond, args),n) -> 
	let args = to_caml_list args in
	begin
	  match args with 
	    | [] -> failwith "get_bound: condition sans variables"
	    | r :: [] -> if is_variant r loop then failwith "Pas de borene dans la boucle" else r
	    | r1 :: r2 :: [] ->
		begin
		  match is_variant r1 loop, is_variant r2 loop with
		    | true, true -> failwith "Pas de borne dans la boucle "
		    | false, true -> r1
		    | true, false -> r2
		    | false, false -> failwith "deux bornes possibles dans la boucle"
		end
	    | _ -> failwith "get_bound: condition avec nombre de variables superieur a 2"
	end
    | _ -> failwith "get_bound: the node I was given is not a condition\n" 

let get_nextpc graph =
  (G.fold_vertex (fun node max ->
		   if (snd (G.V.label node)) > max 
		   then (snd (G.V.label node))
		   else max
		) graph 0) + 1

let substitute_pipeline graph loop steady_state prolog epilog min unrolling ru rd params =
  let n1 = max_reg_of_graph graph params in
  let n2 = (BinPos.coq_Psucc n1) in
  let n3 = (BinPos.coq_Psucc n2) in
  let n4 = (BinPos.coq_Psucc n3) in  
  let way_in = (List.hd loop) in
  let way_out = (List.hd (List.rev loop)) in
  let bound = (get_bound (List.hd (List.tl loop)) loop) in
  let min = (Camlcoq.z_of_camlint (Int32.of_int min)) in
  let unrolling = (Camlcoq.z_of_camlint (Int32.of_int unrolling)) in
  let next_pc = get_nextpc graph in
  patch_graph graph way_in way_out steady_state bound min unrolling n1 n2 n3 n4 next_pc prolog epilog ru rd 
 
let get_loops cfg = 
  let domi = dominator_tree cfg in
  let loops = detect_loops cfg.graph domi in
  let loops = List.filter (fun loop -> is_pipelinable (snd (loop))) loops in 
  loops

type pipeline = {steady_state : G.V.t list; prolog : G.V.t list; epilog : G.V.t list; 
		 min : int; unrolling : int; ramp_up : (reg * reg) list; ramp_down : (reg * reg) list}

let delete_indexes l = List.map (fun e -> fst (G.V.label e) ) l

type reg = Registers.reg 

let fresh = ref BinPos.Coq_xH

let distance e = 
  match G.E.label e with
    | 1 | 2 | 3 -> 0
    | _ -> 1

type et = IntraRAW | IntraWAW | IntraWAR | InterRAW | InterWAW | InterWAR

let edge_type e = 
  match G.E.label e with
    | 1 -> IntraRAW
    | 2 -> IntraWAR
    | 3 -> IntraWAW
    | 4 -> InterRAW
    | 5 -> InterWAR
    | 6 -> InterWAW
    | _ -> failwith "Unknown edge type"

let latency n = (* A raffiner *) 
  match fst (G.V.label n) with
    | Iop (op,args, dst) -> 
	begin
	  match op with
	    | Omove -> 1
	    | Oaddimm _ -> 1
	    | Oadd -> 2
	    | Omul -> 3 
	    | Odiv -> 30
	    | Omulimm _ -> 5
	    | _ -> 2
	end
    | Iload _ -> 10
    | Ialloc _ -> 20
    | _ -> 1
  
let reforge_writes inst r = 
  G.V.create ((match fst (G.V.label inst) with
    | Inop -> Inop
    | Iop (op, args, dst) -> Iop (op, args, r)
    | Iload (chunk, mode, args, dst) -> Iload (chunk, mode, args, r)
    | Istore (chunk, mode, args, src) -> Istore (chunk, mode, args, src)
    | Icall (sign, id, args, dst) -> failwith "reforge_writes: call"
    | Itailcall (sign, id, args) -> failwith "reforge_writes: tailcall"
    | Ialloc (dst, size) -> Ialloc (r, size)
    | Icond (cond, args) -> Icond (cond, args)
    | Ireturn (res) -> failwith "reforge_writes: return")
	, snd (G.V.label inst))

let rec reforge_args args oldr newr =
  match args with
    | CList.Coq_nil -> CList.Coq_nil
    | CList.Coq_cons (e,l) -> CList.Coq_cons ((if e = oldr then newr else e), (reforge_args l oldr newr))

let rec mem_args args r =
  match args with
    | CList.Coq_nil -> false
    | CList.Coq_cons (e,l) -> if e = r then true else mem_args l r

let check_read_exists inst r =
  match fst (G.V.label inst) with
    | Inop -> false
    | Iop (op, args, dst) -> mem_args args r
    | Iload (chunk, mode, args, dst) -> mem_args args r
    | Istore (chunk, mode, args, src) -> src = r || mem_args args r
    | Icall (sign, id, args, dst) -> mem_args args r
    | Itailcall (sign, id, args) -> false
    | Ialloc (dst, size) -> false
    | Icond (cond, args) -> mem_args args r
    | Ireturn (res) -> false

let reforge_reads inst oldr newr  = 
  assert (check_read_exists inst oldr);
  G.V.create ((match fst (G.V.label inst) with
    | Inop -> Inop
    | Iop (op, args, dst) -> Iop (op, reforge_args args oldr newr, dst)
    | Iload (chunk, mode, args, dst) -> Iload (chunk, mode, reforge_args args oldr newr, dst)
    | Istore (chunk, mode, args, src) -> Istore (chunk, mode, reforge_args args oldr newr , if src = oldr then newr else src)
    | Icall (sign, id, args, dst) -> failwith "reforge_reads: call"
    | Itailcall (sign, id, args) -> failwith "reforge_reads: tailcall"
    | Ialloc (dst, size) -> Ialloc (dst, size)
    | Icond (cond, args) -> Icond (cond, reforge_args args oldr newr)
    | Ireturn (res) -> failwith "reforge_reads: return")
	, snd (G.V.label inst))

let get_succs_raw ddg node = 
  let succs = G.succ_e ddg node in
  let succs = List.filter (fun succ ->
			     match G.E.label succ with
			       | 1 | 4 -> true
			       | _ -> false
			  ) succs in
  List.map (fun e -> G.E.dst e) succs

let written inst = 
  match fst (G.V.label inst) with
    | Inop -> None
    | Iop (op, args, dst) -> Some dst
    | Iload (chunk, mode, args, dst) -> Some dst
    | Istore (chunk, mode, args, src) -> None
    | Icall (sign, id, args, dst) -> failwith "written: call"
    | Itailcall (sign, id, args) -> failwith "written: tailcall"
    | Ialloc (dst, size) -> Some dst
    | Icond (cond, args) -> None
    | Ireturn (res) -> failwith "written: return"

let fresh_regs n =
  let t = Array.make n (BinPos.Coq_xH) in
  for i = 0 to (n - 1) do
    Array.set t i (!fresh);
    fresh := BinPos.coq_Psucc !fresh 
  done;
  t
  
let print_reg r = Printf.fprintf Debug.dc "%i " (Int32.to_int (Camlcoq.camlint_of_positive r))

let is_cond node =
  match fst (G.V.label node) with
    | Icond _ -> true 
    | _ -> false
    
  
(*******************************************)
 
let watch_regs l = List.fold_right (fun (a,b) l ->
				      if List.mem a l then l else a :: l
				   ) l []

let make_moves = List.map (fun (a,b) -> Iop (Omove,CList.Coq_cons (b,CList.Coq_nil),a))

let rec repeat l n =
  match n with
    | 0 -> []
    | n -> l @ repeat l (n-1)

let fv = ref 0

let apply_pipeliner f p ?(debug=false) = 
  Printf.fprintf Debug.dc "******************** NEW FUNCTION ***********************\n";
  let cfg = convert f in
  incr fv;
  if debug then display cfg.graph ("input" ^ (string_of_int !fv));
  let loops = get_loops cfg in
  let ddgs = List.map (fun (qqch,loop) -> (loop,build_inter_dependency_graph loop)) loops in
  
  let lv = ref 0 in

  let graph = List.fold_right (fun (loop,ddg) graph ->
				 Printf.fprintf Debug.dc "__________________ NEW LOOP ____________________\n";
				 Printf.printf "Pipelinable loop: ";
				 incr lv;
				 fresh := (BinPos.coq_Psucc 
					     (BinPos.coq_Psucc 
						(BinPos.coq_Psucc 
						   (BinPos.coq_Psucc 
						      (BinPos.coq_Psucc 
							 (max_reg_of_graph graph (to_caml_list f.fn_params) 
							 ))))));
				 Printf.fprintf Debug.dc "FRESH = %i \n" 
				   (Int32.to_int (Camlcoq.camlint_of_positive !fresh));
				 match p ddg with
				   | Some pipe ->
				       Printf.printf "Rock On ! Min = %i - Unroll = %i\n" pipe.min pipe.unrolling;
				       let p = (make_moves pipe.ramp_up) @ (delete_indexes pipe.prolog) in
				       let e = (delete_indexes pipe.epilog) @ (make_moves pipe.ramp_down) in
				       let b = delete_indexes (List.tl (List.tl loop)) in
				       let bt = (List.tl (delete_indexes pipe.steady_state)) in					   
				       let cond1 = fst (G.V.label (List.hd (List.tl loop))) in
				       let cond2 = (List.hd (delete_indexes pipe.steady_state)) in
				   
				       
				       let bu = symbolic_evaluation (repeat b (pipe.min + 1)) in
				       let pe = symbolic_evaluation (p @ e) in
				       let bte = symbolic_evaluation (bt @ e) in 
				       let ebu = symbolic_evaluation (e @ repeat b pipe.unrolling) in 
				       let regs = watch_regs pipe.ramp_down in
				       let c1 = symbolic_condition cond1 (repeat b pipe.unrolling) in
				       let d1 = symbolic_condition cond1 (repeat b (pipe.min + 1)) in
				       let c2 = symbolic_condition cond2 p in
				       let d2 = symbolic_condition cond2 ((make_moves pipe.ramp_up) @ bt) in
    
				       

				       let sbt = symbolic_evaluation (bt) in
				       let sep = symbolic_evaluation (e @ repeat b (pipe.unrolling - (pipe.min + 1)) @ p) in (* er @ pr *)

				       Printf.printf "Initialisation : %s \n" 
					 (if symbolic_equivalence bu pe regs then "OK" else "FAIL");
				       Printf.printf "Etat stable : %s \n" 
					 (if symbolic_equivalence bte ebu regs then "OK" else "FAIL");
				       Printf.printf "Egalite fondamentale : %s \n"
					 (if symbolic_equivalence sbt sep (watch_regs pipe.ramp_up) then "OK" else "FAIL");
				       Printf.printf "Condition initiale : %s \n"
					 (if c1 = c2 then "OK" else "FAIL");
				       Printf.printf "Condition stable : %s \n"
					 (if d1 = d2 then "OK" else "FAIL");


				       Printf.fprintf Debug.dc "pbte\n";
				       List.iter (fun e -> 
						    Printf.fprintf Debug.dc "%s\n" 
						      (string_of_node (G.V.create (e,0)))
						 ) (p @ bt @ e);
				       Printf.fprintf Debug.dc "bu\n";
				       List.iter (fun e -> Printf.fprintf Debug.dc "%s\n" 
						    (string_of_node (G.V.create (e,0)))
						 ) (repeat b (pipe.unrolling + pipe.min));


				    
				       if debug then 
					 display_st ("pbte"^ (string_of_int !fv) ^ (string_of_int !lv)) (p @ bt @ e) (watch_regs pipe.ramp_down);
				       if debug then 
					 display_st ("bu"^ (string_of_int !fv) ^ (string_of_int !lv)) (repeat b (pipe.min + pipe.unrolling)) (watch_regs pipe.ramp_down);
				       
				       if debug then display_st ("bt"^ (string_of_int !fv) ^ (string_of_int !lv)) (bt) (watch_regs pipe.ramp_up);
				       if debug then display_st ("ep"^ (string_of_int !fv) ^ (string_of_int !lv)) (e @ repeat b (pipe.unrolling - (pipe.min + 1)) @ p) (watch_regs pipe.ramp_up);

				       substitute_pipeline graph loop 
					 (delete_indexes pipe.steady_state) (delete_indexes pipe.prolog) 
					 (delete_indexes pipe.epilog) (pipe.min + pipe.unrolling) 
					 pipe.unrolling pipe.ramp_up
					 pipe.ramp_down 
					 (to_caml_list f.fn_params) 
				   | None -> Printf.printf "Damn It ! \n"; graph
			      ) ddgs cfg.graph in

  if debug then display graph ("output"^ (string_of_int !fv));
  let tg = convert_back graph in

  let tg_to_type = {fn_sig = f.fn_sig; 
		    fn_params = f.fn_params; 
		    fn_stacksize = f.fn_stacksize;
		    fn_code = tg; 
		    fn_entrypoint = f.fn_entrypoint; 
		    fn_nextpc = Camlcoq.positive_of_camlint (Int32.of_int (get_nextpc (graph)))
		   } in
  Typing.type_function tg_to_type;

  tg
