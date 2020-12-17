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

module NI : Map.S with type key = Basic.G.V.t 

(* piepeliner takes a data dependency graph and returns a schedule with an initiation interval
   fails if cannot find any schedule *)
val pipeliner : G.t -> (G.t -> int option NI.t -> G.V.t) -> int NI.t * int

val print_schedule : int NI.t -> unit
