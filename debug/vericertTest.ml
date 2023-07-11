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

let schedule_oracle l bb bbt =
  match abstract_sequence_top bb with
  | Some p ->
    let (p0, m_expr) = p in
    let (bb', reg_expr) = p0 in
    (match abstract_sequence_top (concat (concat bbt)) with
     | Some p1 ->
       let (p2, m_expr_t) = p1 in
       let (bbt', reg_expr_t) = p2 in
       printf "F1:\n%a\n" PrintAbstr.print_forest bb';
       printf "F2:\n%a\n" PrintAbstr.print_forest bbt'; flush stdout;
       (&&)
         ((&&) ((&&) (if check l bb' bbt' then true else (Printf.printf "Failed 1\n"; false)) (empty_trees bb bbt))
           (if (check_evaluability1 reg_expr reg_expr_t) then true else (Printf.printf "Failed 12\n"; false)))
         (if check_evaluability2 m_expr m_expr_t then true else (Printf.printf "Failed 13\n"; false))
     | None -> (printf "FAILED1\n"; false))
  | None -> (printf "FAILED2\n"; false)

(** val check_scheduled_trees :
    GibleSeq.SeqBB.t PTree.t -> GiblePar.ParBB.t PTree.t -> bool **)

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
  (* (if schedule_oracle [] *)
  (*      [ add None 2 1 4; *)
  (*        seteq (Some (plit true 1)) 3 4 2; *)
  (*        add (Some (plit true 1)) 1 2 4; *)
  (*        mul (Some (Pand (plit false 1, plit false 2))) 3 1 1; *)
  (*        mul (Some (plit true 2)) 3 1 4; *)
  (*        goto (Some (plit true 2)) 10; *)
  (*        mul (Some (plit false 2)) 3 3 3; *)
  (*        goto None 10; *)
  (*      ] *)
  (*      [ [ [ mul (Some (Pand (plit false 1, plit false 2))) 3 1 1; ]; *)
  (*          [ add None 2 1 4; *)
  (*            add (Some (plit true 1)) 1 2 4; *)
  (*            seteq (Some (plit true 1)) 3 4 2; ] ]; *)
  (*        [ [ mul (Some (plit true 2)) 3 1 4; ]; *)
  (*          [ mul (Some (plit false 2)) 3 3 3; ]; *)
  (*          [ goto None 10; ] *)
  (*        ] *)
  (*      ] *)
  (* then Printf.printf "Passed 1\n" *)
  (*  else Printf.printf "Failed 1\n"); *)
  (* (if schedule_oracle [] *)
  (*       [ seteq (Some (plit true 1)) 2 1 2; *)
  (*         goto None 10; *)
  (*      ] *)
  (*       [ [ [ goto (Some (plit false 1)) 10; *)
  (*             seteq None 2 1 2; *)
  (*             goto None 10; *)
  (*       ] ] ] *)
  (* then Printf.printf "Passed 1\n" *)
  (*  else Printf.printf "Failed 1\n");   *)
  (* (if schedule_oracle [] *)
  (*       [ seteq None 2 1 2; *)
  (*         seteq None 3 1 2; *)
  (*         seteq (Some (Por (plit true 2, plit false 3))) 4 1 3; *)
  (*      ] *)
  (*       [ [ [ seteq None 2 1 2; *)
  (*             seteq None 3 1 2; *)
  (*             seteq None 4 1 3; *)
  (*       ] ] ] *)
  (* then Printf.printf "Passed 1\n" *)
  (*  else Printf.printf "Failed 1\n");   *)
  (* (if schedule_oracle [] *)
  (*       [ sett (Some (plit false 1)) 2 1; *)
  (*         div (Some (plit true 1)) 1 2 3; *)
  (*       ] *)
  (*       [ [ [ div (Some (plit true 1)) 1 2 3; *)
  (*             sett (Some (plit false 1)) 2 1; *)
  (*       ] ] ] *)
  (* then Printf.printf "Passed 1\n" *)
  (*  else Printf.printf "Failed 1\n"); *)
  (if schedule_oracle []
        [ const (Some (plit true 1)) 1 0;
          const (Some (Por (plit true 1, plit false 1))) 1 1;
        ]
        [ [ [ const None 1 1;
        ] ] ]
   then Printf.printf "Passed 1\n"
   else Printf.printf "Failed 1\n");
  (* (if schedule_oracle [(pred 3, pred 2)] *)
  (*      [ add None 2 1 4; *)
  (*        seteq None 1 10 11; *)
  (*        add (Some (plit true 1)) 1 2 4; *)
  (*        seteq (Some (plit true 1)) 2 12 13; *)
  (*        mul (Some (Pand (plit true 1, plit true 2))) 3 1 4; *)
  (*        goto (Some (Pand (plit true 1, plit true 2))) 10; *)
  (*        mul (Some (Pand (plit true 1, plit false 2))) 3 3 3; *)
  (*        goto (Some (Pand (plit true 1, plit false 2))) 10; *)
  (*        seteq (Some (plit false 1)) 3 12 13; *)
  (*        mul (Some (Pand (plit false 1, plit true 3))) 3 1 4; *)
  (*        goto (Some (Pand (plit false 1, plit true 3))) 10; *)
  (*        mul (Some (Pand (plit false 1, plit false 3))) 3 1 1; *)
  (*        mul (Some (Pand (plit false 1, plit false 3))) 3 3 3; *)
  (*        goto (Some (Pand (plit false 1, plit false 3))) 10; *)
  (*      ] *)
  (*      [ [ [ seteq None 1 10 11; *)
  (*            add None 2 1 4; *)
  (*            seteq (Some (plit false 1)) 3 12 13; *)
  (*            seteq (Some (plit true 1)) 2 12 13; *)
  (*            add (Some (plit true 1)) 1 2 4; *)
  (*            mul (Some (Pand (plit true 1, plit true 2))) 3 1 4; *)
  (*            mul (Some (Pand (plit true 1, plit false 2))) 3 3 3; *)
  (*            mul (Some (Pand (plit false 1, plit true 2))) 3 1 4; *)
  (*            mul (Some (Pand (plit false 1, plit false 2))) 3 1 1; *)
  (*            mul (Some (Pand (plit false 1, plit false 2))) 3 3 3; *)
  (*            goto None 10; *)
  (*      ] ] ] *)
  (* then Printf.printf "Passed 110\n" *)
  (*  else Printf.printf "Failed 102\n"); *)
  (*   (if schedule_oracle [(pred 3, pred 2)] *)
  (*      [ add None 2 1 4; *)
  (*        seteq None 1 10 11; *)
  (*        add (Some (plit true 1)) 1 2 4; *)
  (*        seteq (Some (plit true 1)) 2 12 13; *)
  (*        mul (Some (Pand (plit true 1, plit true 2))) 3 1 4; *)
  (*        goto (Some (Pand (plit true 1, plit true 2))) 10; *)
  (*        mul (Some (Pand (plit true 1, plit false 2))) 5 3 3; *)
  (*        goto (Some (Pand (plit true 1, plit false 2))) 10; *)
  (*        seteq (Some (plit false 1)) 3 12 13; *)
  (*        mul (Some (Pand (plit false 1, plit true 3))) 3 1 4; *)
  (*        goto (Some (Pand (plit false 1, plit true 3))) 10; *)
  (*        mul (Some (Pand (plit false 1, plit false 3))) 3 1 1; *)
  (*        mul (Some (Pand (plit false 1, plit false 3))) 5 3 3; *)
  (*        goto (Some (Pand (plit false 1, plit false 3))) 10; *)
  (*      ] *)
  (*      [ [ [ seteq None 1 10 11; *)
  (*            add None 2 1 4; *)
  (*            seteq (Some (plit false 1)) 3 12 13; *)
  (*            seteq (Some (plit true 1)) 2 12 13; *)
  (*            add (Some (plit true 1)) 1 2 4; *)
  (*            mul (Some (Pand (plit true 1, plit true 2))) 3 1 4; *)
  (*            mul (Some (Pand (plit false 1, plit true 2))) 3 1 4; *)
  (*            mul (Some (Pand (plit false 1, plit false 2))) 3 1 1; *)
  (*            mul (Some (Pand (plit true 1, plit false 2))) 5 3 3; *)
  (*            mul (Some (Pand (plit false 1, plit false 2))) 5 3 3; *)
  (*            goto None 10; *)
  (*      ] ] ] *)
  (* then Printf.printf "Passed 110\n" *)
  (*    else Printf.printf "Failed 102\n"); *)
  (*   (if schedule_oracle [(pred 3, pred 2)] *)
  (*      [  *)
  (*        seteq None 1 10 11; *)
  (*        seteq None 3 12 13; *)
  (*        seteq None 2 12 13; *)
  (*        add None 2 1 4; *)
  (*        mul (Some (Pand (plit false 1, plit false 3))) 3 1 1; *)
  (*        mul (Some (Pand (plit false 1, plit false 3))) 5 3 3; *)
  (*        goto (Some (Pand (plit false 1, plit false 3))) 10; *)
  (*        mul (Some (Pand (plit false 1, plit true 3))) 3 1 4; *)
  (*        goto (Some (Pand (plit false 1, plit true 3))) 10; *)
  (*        add (Some (plit true 1)) 1 2 4; *)
  (*        mul (Some (Pand (plit true 1, plit false 2))) 5 3 3; *)
  (*        goto (Some (Pand (plit true 1, plit false 2))) 10; *)
  (*        mul (Some (Pand (plit true 1, plit true 2))) 3 1 4; *)
  (*        goto (Some (Pand (plit true 1, plit true 2))) 10; *)
  (*      ] *)
  (*      [ [ [ seteq None 1 10 11; *)
  (*            seteq None 3 12 13; *)
  (*            seteq None 2 12 13; *)
  (*            mul (Some (Pand (plit false 1, plit false 2))) 3 1 1; *)
  (*            add None 2 1 4; *)
  (*            add (Some (plit true 1)) 1 2 4; *)
  (*            mul (Some (Pand (plit false 1, plit true 2))) 3 1 4; *)
  (*            mul (Some (Pand (plit true 1, plit true 2))) 3 1 4; *)
  (*            mul (Some (Pand (plit false 1, plit false 2))) 5 3 3; *)
  (*            mul (Some (Pand (plit true 1, plit false 2))) 5 3 3; *)
  (*            goto None 10; *)
  (*      ] ] ] *)
  (* then Printf.printf "Passed 110\n" *)
  (*    else Printf.printf "Failed 102\n") *)

