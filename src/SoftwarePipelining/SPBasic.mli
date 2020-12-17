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

(* DATA DEPENDENCY GRAPHS *)
module G : Graph.Sig.P 

(* We abstract the register type to make sure that the user won't mess up *)
type reg

(* The scheduling should return a value of type pipeline *)
type pipeline = {
  steady_state : G.V.t list; 
  prolog : G.V.t list; 
  epilog : G.V.t list; 
  min : int; 
  unrolling : int;
  ramp_up : (reg * reg) list;
  ramp_down : (reg * reg) list
}

(* Operations on ddg *)

val display : G.t -> string -> unit
val apply_pipeliner : RTL.coq_function -> (G.t -> pipeline option) -> ?debug:bool -> RTL.code
val get_succs_raw : G.t -> G.V.t -> G.V.t list

(* Operations on instructions, the nodes of the data dependency graph *)

val string_of_node : G.V.t -> string
val latency : G.V.t -> int
val reforge_reads : G.V.t -> reg -> reg -> G.V.t
val reforge_writes : G.V.t -> reg -> G.V.t
val written : G.V.t -> reg option
val is_cond : G.V.t -> bool

(* Operations on dependencies, the edges of the data dependency graph *)
 
type et = IntraRAW | IntraWAW | IntraWAR | InterRAW | InterWAW | InterWAR

val edge_type : G.E.t -> et
val distance : G.E.t -> int

(* Getting fresh registers, int is the number of required registers *)

val fresh_regs : int -> reg array 
val print_reg : reg -> unit










