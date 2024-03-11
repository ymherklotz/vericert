open Vericert

open AST
open Abstr
open BinNums
open Coqlib
open Datatypes
open Errors
open GiblePargenproofEquiv
open List0
open Maps
open Optionmonad
open Predicate
open GiblePargen
open Integers
open Op
open Printf

let z = Camlcoq.Z.of_sint
let int n = Int.repr (z n)
let reg = Camlcoq.P.of_int
let pred = Camlcoq.P.of_int
let node = Camlcoq.P.of_int
let plit b p = Plit (b, pred p)

let const p d c: Gible.instr = RBop (p, Ointconst (z c), [], reg d)
let add p d1 r1 r2: Gible.instr = RBop (p, Olea (Aindexed2 (z 0)), [reg r1; reg r2], reg d1)
let mul p d1 r1 r2: Gible.instr = RBop (p, Omul, [reg r1; reg r2], reg d1)
let div p d1 r1 r2: Gible.instr = RBop (p, Odiv, [reg r1; reg r2], reg d1)
let seteq p d1 r1 r2: Gible.instr = RBsetpred (p, Ccomp Ceq, [reg r1; reg r2], pred d1)
let sett p d1 r1: Gible.instr = RBsetpred (p, Ccompimm (Ceq, int 0), [reg r1], pred d1)
let goto p n: Gible.instr = RBexit (p, (RBgoto (node n)))

let () =
    (if schedule_oracle
       [
         seteq None 1 10 11;
       ]
       [ [ [ seteq None 1 10 11;
       ] ] ]
  then Printf.printf "Passed\n"
     else Printf.printf "Failed\n")
