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


open Unix

let tm = localtime (time ());;
let name = "../tmp/" ^ (string_of_int tm.tm_year) ^ "-" ^(string_of_int tm.tm_mon) ^ "-" ^(string_of_int tm.tm_mday) ^ 
  "-" ^(string_of_int tm.tm_hour) ^"-" ^(string_of_int tm.tm_min) ^ "-" ^(string_of_int tm.tm_sec) ^ "/";;
mkdir name 0o777;;
Printf.printf "Debug informations: %s \n" name  ;;
let dc = open_out (name ^ "debug.log");;   
let () = at_exit(fun () -> close_out dc);;



  
