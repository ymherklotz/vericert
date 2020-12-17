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


open Camlcoq
open Op
open Registers
open Mem
open AST

type ('a,'b) sum = ('a,'b) Datatypes.sum

type instruction =
  | Inop 
  | Iop of operation * reg CList.list * reg 
  | Iload of memory_chunk * addressing * reg CList.list * reg 
  | Istore of memory_chunk * addressing * reg CList.list * reg 
  | Icall of signature * (reg, ident) sum * reg CList.list * reg 
  | Itailcall of signature * (reg, ident) sum * reg CList.list
  | Ialloc of reg * reg 
  | Icond of condition * reg CList.list 
  | Ireturn of reg Datatypes.option

type resource = Reg of reg | Mem

let inst_coq_to_caml = function 
  | RTL.Inop succ -> Inop
  | RTL.Iop (op, args, dst, succ) -> Iop (op, args, dst)
  | RTL.Iload (chunk, mode, args, dst, succ) -> Iload (chunk, mode, args, dst)
  | RTL.Istore (chunk, mode, args, src, succ) -> Istore (chunk, mode, args, src)
  | RTL.Icall (sign, id, args, dst, succ) -> Icall (sign, id, args, dst)
  | RTL.Itailcall (sign, id, args) -> Itailcall (sign, id, args)
  | RTL.Ialloc (dst, size, succ) -> Ialloc (dst, size)
  | RTL.Icond (cond, args, succ1, succ2) -> Icond (cond, args)  
  | RTL.Ireturn (res) -> Ireturn (res)
 
let inst_caml_to_coq i (links : RTL.node list) =
  match i,links with 
  | Inop,[p] -> RTL.Inop p
  | Iop (op, args, dst),[p] -> RTL.Iop (op, args, dst,p)  
  | Iload (chunk, mode, args, dst),[p] -> RTL.Iload (chunk, mode, args,dst,p) 
  | Istore (chunk, mode, args, src),[p] -> RTL.Istore (chunk, mode, args, src,p)  
  | Icall (sign, id, args, dst),[p] -> RTL.Icall (sign, id, args, dst,p) 
  | Itailcall (sign, id, args),[] -> RTL.Itailcall (sign, id, args) 
  | Ialloc (dst, size),[p] -> RTL.Ialloc (dst, size,p) 
  | Icond (cond, args),[p1;p2] -> RTL.Icond (cond,args,p1,p2)  
  | Ireturn (res),[] -> RTL.Ireturn res 
  | _,_ -> failwith "Echec lors de la conversion des instrucitons internes vers compcert"


let print_inst node = string_of_int (snd node)

let to_int = fun n -> Int32.to_int (camlint_of_positive n)
let to_binpos = fun n -> positive_of_camlint (Int32.of_int n)

let rec string_of_args args =
  match args with
    | CList.Coq_nil -> ""
    | CList.Coq_cons (arg,args) -> "r" ^ (string_of_int (to_int arg)) ^ " " ^ string_of_args args  

let string_of_z z = string_of_int (Int32.to_int (Camlcoq.camlint_of_z z))

let string_of_comparison = function
  | Integers.Ceq -> "eq"
  | Integers.Cne -> "ne"
  | Integers.Clt -> "lt"
  | Integers.Cle -> "le"
  | Integers.Cgt -> "gt"
  | Integers.Cge -> "ge"
 
let string_of_cond = function
  | Ccomp c -> Printf.sprintf "comp %s" (string_of_comparison c)
  | Ccompu c -> Printf.sprintf "compu %s" (string_of_comparison c)
  | Ccompimm (c,i) -> Printf.sprintf "compimm %s %s" (string_of_comparison c) (string_of_z i)
  | Ccompuimm (c,i) -> Printf.sprintf "compuimm %s %s" (string_of_comparison c) (string_of_z i)
  | Ccompf c -> Printf.sprintf "compf %s" (string_of_comparison c)
  | Cnotcompf c -> Printf.sprintf "notcompf %s" (string_of_comparison c)
  | Cmaskzero i -> Printf.sprintf "maskzero %s" (string_of_z i)
  | Cmasknotzero i -> Printf.sprintf "masknotzero %s" (string_of_z i)

let string_of_op = function
  | Omove -> "move"
  | Ointconst i -> Printf.sprintf "intconst %s" (string_of_z i)
  | Ofloatconst f -> Printf.sprintf "floatconst %s" (string_of_float f)  
  | Oaddrsymbol (id,i) -> Printf.sprintf "addrsymbol %s %s" (string_of_int (to_int id)) (string_of_z i)
  | Oaddrstack i -> Printf.sprintf "addrstack %s" (string_of_z i)
  | Ocast8signed -> "cast8signed"
  | Ocast8unsigned -> "cast8unsigned"
  | Ocast16signed -> "cast16signed"
  | Ocast16unsigned -> "cast16unsigned"
  | Oadd -> "add"
  | Oaddimm i -> Printf.sprintf "addimm %s" (string_of_z i)
  | Osub -> "sub"
  | Osubimm i -> Printf.sprintf "subimm %s" (string_of_z i)
  | Omul -> "mul"
  | Omulimm i -> Printf.sprintf "mulimm %s" (string_of_z i)
  | Odiv -> "div"
  | Odivu -> "divu"
  | Oand -> "and"
  | Oandimm i -> Printf.sprintf "andimm %s" (string_of_z i)
  | Oor -> "or"
  | Oorimm i -> Printf.sprintf "orimm %s" (string_of_z i)
  | Oxor -> "xor"
  | Oxorimm i -> Printf.sprintf "xorimm %s" (string_of_z i)
  | Onand -> "nand"
  | Onor -> "nor"
  | Onxor -> "nxor" 
  | Oshl -> "shl"
  | Oshr -> "shr"
  | Oshrimm i -> Printf.sprintf "shrimm %s" (string_of_z i)
  | Oshrximm i -> Printf.sprintf "shrximm %s" (string_of_z i)
  | Oshru -> "shru"
  | Orolm (i,j) -> Printf.sprintf "rolm %s %s" (string_of_z i) (string_of_z j)
  | Onegf -> "negf"
  | Oabsf -> "absf"
  | Oaddf -> "addf"
  | Osubf -> "subf"
  | Omulf -> "mulf"
  | Odivf -> "divf"
  | Omuladdf -> "muladdf"
  | Omulsubf -> "mulsubf"
  | Osingleoffloat -> "singleoffloat"
  | Ointoffloat -> "intoffloat"
  | Ointuoffloat -> "intuoffloat"
  | Ofloatofint -> "floatofint"
  | Ofloatofintu -> "floatofintu"
  | Ocmp c -> Printf.sprintf "cmpcmpcmp" 
  
let rec to_coq_list = function
  | [] -> CList.Coq_nil
  | e :: l -> CList.Coq_cons (e,(to_coq_list l))

let rec to_caml_list = function
  | CList.Coq_nil -> []
  | CList.Coq_cons (e,l) -> e :: to_caml_list l 
