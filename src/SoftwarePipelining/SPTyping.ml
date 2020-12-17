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


open Datatypes
open CList
open Camlcoq
open Maps
open AST
open Op
open Registers
open RTL

open Conventions
open Coqlib
open Errors
open Specif



exception Type_error of string

let env = ref (PTree.empty : typ PTree.t)

let set_type r ty =
  match PTree.get r !env with
  | None -> env := PTree.set r ty !env
  | Some ty' -> if ty <> ty' then 
      begin 
	Printf.fprintf Debug.dc "Failed to type register : %i " (Int32.to_int (Camlcoq.camlint_of_positive r));
	raise (Type_error "type mismatch")
      end

let rec set_types rl tyl =
  match rl, tyl with
  | Coq_nil, Coq_nil -> ()
  | Coq_cons(r1, rs), Coq_cons(ty1, tys) -> set_type r1 ty1; set_types rs tys
  | _, _ -> raise (Type_error "arity mismatch")

(* First pass: process constraints of the form typeof(r) = ty *)

let type_instr retty (Coq_pair(pc, i)) =
  Printf.fprintf Debug.dc "typage de l'instruction : %i \n" (Int32.to_int (Camlcoq.camlint_of_positive pc)); 
  match i with
  | Inop(_) ->
      ()
  | Iop(Omove, _, _, _) -> 
      ()
  | Iop(op, args, res, _) ->
      let (Coq_pair(targs, tres)) = type_of_operation op in
      set_types args targs; set_type res tres
  | Iload(chunk, addr, args, dst, _) ->
      set_types args (type_of_addressing addr);
      set_type dst (type_of_chunk chunk)
  | Istore(chunk, addr, args, src, _) ->
      set_types args (type_of_addressing addr);
      set_type src (type_of_chunk chunk)
  | Icall(sg, ros, args, res, _) ->
      begin try
        begin match ros with
        | Coq_inl r -> set_type r Tint
        | Coq_inr _ -> ()
        end;
        set_types args sg.sig_args;
        set_type res (match sg.sig_res with None -> Tint | Some ty -> ty)
      with Type_error msg ->
        let name =
          match ros with
          | Coq_inl _ -> "<reg>"
          | Coq_inr id -> extern_atom id in
        raise(Type_error (Printf.sprintf "type mismatch in Icall(%s): %s"
                                         name msg))
      end
  | Itailcall(sg, ros, args) ->
      begin try
        begin match ros with
        | Coq_inl r -> set_type r Tint
        | Coq_inr _ -> ()
        end;
        set_types args sg.sig_args;
        if sg.sig_res <> retty then
          raise (Type_error "mismatch on return type")
      with Type_error msg ->
        let name =
          match ros with
          | Coq_inl _ -> "<reg>"
          | Coq_inr id -> extern_atom id in
        raise(Type_error (Printf.sprintf "type mismatch in Itailcall(%s): %s"
                                         name msg))
      end
  | Ialloc(arg, res, _) ->
      set_type arg Tint; set_type res Tint
  | Icond(cond, args, _, _) ->
      set_types args (type_of_condition cond)
  | Ireturn(optres) ->
      begin match optres, retty with
      | None, None -> ()
      | Some r, Some ty -> set_type r ty
      | _, _ -> raise (Type_error "type mismatch in Ireturn")
      end

let type_pass1 retty instrs = 
  coqlist_iter (type_instr retty) instrs

(* Second pass: extract move constraints typeof(r1) = typeof(r2)
   and solve them iteratively *)

let rec extract_moves = function
  | Coq_nil -> []
  | Coq_cons(Coq_pair(pc, i), rem) ->
      match i with
      | Iop(Omove, Coq_cons(r1, Coq_nil), r2, _) ->
          (r1, r2) :: extract_moves rem
      | Iop(Omove, _, _, _) ->
          raise (Type_error "wrong Omove")
      | _ ->
          extract_moves rem

let changed = ref false

let rec solve_moves = function
  | [] -> []
  | (r1, r2) :: rem ->
      match (PTree.get r1 !env, PTree.get r2 !env) with
      | Some ty1, Some ty2 ->
          if ty1 = ty2 
          then (changed := true; solve_moves rem)
          else raise (Type_error "type mismatch in Omove")
      | Some ty1, None ->
          env := PTree.set r2 ty1 !env; changed := true; solve_moves rem
      | None, Some ty2 ->
          env := PTree.set r1 ty2 !env; changed := true; solve_moves rem
      | None, None ->
          (r1, r2) :: solve_moves rem

let rec iter_solve_moves mvs =
  changed := false;
  let mvs' = solve_moves mvs in
  if !changed then iter_solve_moves mvs'

let type_pass2 instrs =
  iter_solve_moves (extract_moves instrs)

let typeof e r =
  match PTree.get r e with Some ty -> ty | None -> Tint

let infer_type_environment f instrs =
  try
    env := PTree.empty;
    set_types f.fn_params f.fn_sig.sig_args;
    type_pass1 f.fn_sig.sig_res instrs;
    type_pass2 instrs;
    let e = !env in
    env := PTree.empty;
    Some(typeof e)
  with Type_error msg ->
    Printf.eprintf "Error during RTL type inference: %s\n" msg;
    None

(** val typ_eq : typ -> typ -> bool **)

let typ_eq t1 t2 =
  match t1 with
    | Tint -> (match t2 with
                 | Tint -> true
                 | Tfloat -> false)
    | Tfloat -> (match t2 with
                   | Tint -> false
                   | Tfloat -> true)

(** val opt_typ_eq : typ option -> typ option -> bool **)

let opt_typ_eq t1 t2 =
  match t1 with
    | Some x -> (match t2 with
                   | Some t -> typ_eq x t
                   | None -> false)
    | None -> (match t2 with
                 | Some t -> false
                 | None -> true)

(** val check_reg : regenv -> reg -> typ -> bool **)

let check_reg env r ty =
  match typ_eq (env r) ty with
    | true -> true
    | false -> false

(** val check_regs : regenv -> reg list -> typ list -> bool **)

let rec check_regs env rl tyl =
  match rl with
    | Coq_nil ->
        (match tyl with
           | Coq_nil -> true
           | Coq_cons (t, l) -> false)
    | Coq_cons (r1, rs) ->
        (match tyl with
           | Coq_nil -> false
           | Coq_cons (ty, tys) ->
               (match typ_eq (env r1) ty with
                  | true -> check_regs env rs tys
                  | false -> false))

(** val check_op : regenv -> operation -> reg list -> reg -> bool **)

let check_op env op args res0 =
  let Coq_pair (targs, tres) = type_of_operation op in
  (match check_regs env args targs with
     | true ->
         (match typ_eq (env res0) tres with
            | true -> true
            | false -> false)
     | false -> false)

(** val check_successor : coq_function -> node -> bool **)

let check_successor funct s =
  match Maps.PTree.get s funct.fn_code with
    | Some i -> true
    | None -> false

(** val check_instr : coq_function -> regenv -> instruction -> bool **)

let check_instr funct env = function
  | Inop s -> check_successor funct s
  | Iop (op, args, res0, s) ->
      (match op with
         | Omove ->
             (match args with
                | Coq_nil -> false
                | Coq_cons (arg, l) ->
                    (match l with
                       | Coq_nil ->
                           (match typ_eq (env arg) (env res0) with
                              | true -> check_successor funct s
                              | false -> false)
                       | Coq_cons (r, l0) -> false))
         | Ointconst i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ofloatconst f ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oaddrsymbol (i0, i1) ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oaddrstack i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ocast8signed ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ocast8unsigned ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ocast16signed ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ocast16unsigned ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oadd ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oaddimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Osub ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Osubimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Omul ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Omulimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Odiv ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Odivu ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oand ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oandimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oor ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oorimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oxor ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oxorimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Onand ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Onor ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Onxor ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oshl ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oshr ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oshrimm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oshrximm i0 ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oshru ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Orolm (i0, i1) ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Onegf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oabsf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Oaddf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Osubf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Omulf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Odivf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Omuladdf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Omulsubf ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Osingleoffloat ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ointoffloat ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ointuoffloat ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ofloatofint ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ofloatofintu ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false)
         | Ocmp c ->
             (match check_op env op args res0 with
                | true -> check_successor funct s
                | false -> false))
  | Iload (chunk, addr, args, dst, s) ->
      (match check_regs env args (type_of_addressing addr) with
         | true ->
             (match typ_eq (env dst) (type_of_chunk chunk) with
                | true -> check_successor funct s
                | false -> false)
         | false -> false)
  | Istore (chunk, addr, args, src, s) ->
      (match check_regs env args (type_of_addressing addr) with
         | true ->
             (match typ_eq (env src) (type_of_chunk chunk) with
                | true -> check_successor funct s
                | false -> false)
         | false -> false)
  | Icall (sig0, ros, args, res0, s) ->
      (match match ros with
               | Coq_inl r ->
                   (match typ_eq (env r) Tint with
                      | true -> check_regs env args sig0.sig_args
                      | false -> false)
               | Coq_inr s0 -> check_regs env args sig0.sig_args with
         | true ->
             (match typ_eq (env res0) (proj_sig_res sig0) with
                | true -> check_successor funct s
                | false -> false)
         | false -> false)
  | Itailcall (sig0, ros, args) ->
      (match match match ros with
                     | Coq_inl r ->
                         (match typ_eq (env r) Tint with
                            | true -> check_regs env args sig0.sig_args
                            | false -> false)
                     | Coq_inr s -> check_regs env args sig0.sig_args with
               | true ->
                   proj_sumbool
                     (opt_typ_eq sig0.sig_res funct.fn_sig.sig_res)
               | false -> false with
         | true -> tailcall_is_possible sig0
         | false -> false)
  | Ialloc (arg, res0, s) ->
      (match typ_eq (env arg) Tint with
         | true ->
             (match typ_eq (env res0) Tint with
                | true -> check_successor funct s
                | false -> false)
         | false -> false)
  | Icond (cond, args, s1, s2) ->
      (match match check_regs env args (type_of_condition cond) with
               | true -> check_successor funct s1
               | false -> false with
         | true -> check_successor funct s2
         | false -> false)
  | Ireturn optres ->
      (match optres with
         | Some r ->
             (match funct.fn_sig.sig_res with
                | Some t ->
                    (match typ_eq (env r) t with
                       | true -> true
                       | false -> false)
                | None -> false)
         | None ->
             (match funct.fn_sig.sig_res with
                | Some t -> false
                | None -> true))

(** val check_params_norepet : reg list -> bool **)

let check_params_norepet params =
  match list_norepet_dec Registers.Reg.eq params with
    | true -> true
    | false -> false

(** val check_instrs : coq_function -> regenv -> (node, instruction) prod
                       list -> bool **)

let rec check_instrs funct env = function
  | Coq_nil -> true
  | Coq_cons (p, rem) ->
      let Coq_pair (pc, i) = p in
      (match check_instr funct env i with
         | true -> check_instrs funct env rem
         | false -> false)

(** val type_function : coq_function -> unit **)

let type_function f =
  let instrs = Maps.PTree.elements f.fn_code in
  match infer_type_environment f instrs with
    | Some env ->
        (match match match match check_regs env f.fn_params
           f.fn_sig.sig_args with
             | true -> check_params_norepet f.fn_params
             | false -> false with
                 | true -> check_instrs f env instrs
                 | false -> false with
                     | true -> check_successor f f.fn_entrypoint
                     | false -> false with
			 | true -> Printf.fprintf Debug.dc "The code is well typed\n"
			 | false -> failwith "Type checking failure\n")
    | None -> failwith "Type inference failure\n"
			     
