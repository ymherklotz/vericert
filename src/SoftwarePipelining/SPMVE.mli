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

val mve : G.t -> int NI.t -> int -> 
  (G.V.t option) array * G.V.t list * G.V.t list * int * int * (reg * reg) list * (reg * reg) list
