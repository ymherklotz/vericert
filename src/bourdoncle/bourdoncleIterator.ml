type ('ab, 'instr) adom = {
  order: 'ab -> 'ab -> bool;
  join: 'ab -> 'ab -> 'ab;
  widen: 'ab -> 'ab -> 'ab;
  top: unit -> 'ab;
  bot: unit -> 'ab;
  transfer: 'instr -> 'ab -> 'ab;
  to_string: 'ab -> string
}

type 'instr cfg = {
  entry: int;
  succ: (int * 'instr) list array;
}

(* Utilities *)
let rec print_list_sep_rec sep pp = function
  | [] -> ""
  | x::q -> sep^(pp x)^(print_list_sep_rec sep pp q)

let rec print_list_sep_list_rec sep pp = function
  | [] -> []
  | x::q -> (sep^(pp x))::(print_list_sep_list_rec sep pp q)

let print_list_sep sep pp = function
  | [] -> ""
  | x::q -> (pp x)^(print_list_sep_rec sep pp q)

let dot_cfg cfg filename =
  let f = open_out filename in
    Printf.fprintf f "digraph {\n";
    Array.iteri
      (fun i l ->
	 List.iter (fun (j,_) -> Printf.fprintf f "  n%d -> n%d\n" i j) l)
      cfg.succ;
    Printf.fprintf f "}\n";
    close_out f


(* Bourdoncle *)
type bourdoncle = L of (bourdoncle list) * Ptset.t | I of int

let rec string_of_bourdoncle_list l =
    print_list_sep  " " string_of_bourdoncle l
and string_of_bourdoncle = function
  | L (l,_) -> "("^(string_of_bourdoncle_list l)^")"
  | I i -> string_of_int i

(* For efficiency we pre-compute the set of nodes in a cfc *)
let add_component =
  List.fold_left
    (fun s b ->
       match b with
	 | I i -> Ptset.add i s
	 | L (_,s') -> Ptset.union s s')
    Ptset.empty

(* Bourdoncle strategy computation  *)
let get_bourdoncle cfg =
  let date = ref 0 in
  let debut = Array.map (fun _ -> 0) cfg.succ in
  let stack = Stack.create () in
  let rec component i =
    let partition = ref [] in
      List.iter
	(fun (j,_) ->
	   if debut.(j)=0 then ignore (visite j partition))
	cfg.succ.(i);
      (I i) :: !partition
  and visite i partition =
    incr date;
    debut.(i) <- !date;
    let min = ref !date in
    let loop = ref false in
      Stack.push i stack;
      List.iter
	(fun (j,_) ->
	   let m = if debut.(j)=0 then visite j partition else debut.(j) in
	     if m <= !min then
	       begin
		 min := m;
		 loop := true
	       end)
	cfg.succ.(i);
      if !min=debut.(i) then
	begin
	  debut.(i) <- max_int;
	  let k = ref (Stack.pop stack) in
	    if !loop then begin
	      while (!k<>i) do
		debut.(!k) <- 0;
		k := Stack.pop stack;
	      done;
	      let c = component i in
		partition := (L (c,add_component c)) :: !partition
	    end
	    else partition := (I i) :: !partition
	end;
      !min
  in
  let partition = ref [] in
    (* only one entry in the cfg *)
    ignore (visite cfg.entry partition);
    Array.iteri (fun i d -> if d=0 then cfg.succ.(i) <- []) debut;
    !partition

(* predecessors *)
let get_pred cfg =
  let pred = Array.make (Array.length cfg.succ) [] in
    Array.iteri
      (fun i succs ->
	 List.iter
	   (fun (j,ins) ->
	      pred.(j) <- (i,ins) :: pred.(j))
	   succs
      )
      cfg.succ;
    pred

let check_fixpoint adom cfg res =
  if not (adom.order (adom.top ()) res.(cfg.entry)) then
    failwith "res.(ENTRY) should be top !\n";
  Array.iteri
      (fun i succs ->
	 List.iter
	 (fun (j,op) ->
	    if not (adom.order (adom.transfer op res.(i)) res.(j)) then
	      begin
		dot_cfg cfg "debug_bourdoncle.dot";
		failwith (Printf.sprintf "res.(%d) should be lower than res.(%d) !\n" i j)
	      end)
	   succs)
    cfg.succ

let option_down_iterations = ref 1

let rec f_list f acc = function
    [] -> acc
  | x::q -> f_list f (f acc x) q

let run_with_bourdoncle adom b cfg =
  let preds = get_pred cfg in
  let res = Array.init (Array.length preds) (fun _ -> adom.bot ()) in
  let join_list = f_list adom.join in
  let _ = res.(cfg.entry) <- adom.top () in
    let upd j =
      if j <> cfg.entry then
	res.(j) <-
	  join_list (adom.bot ())
	  (List.map (fun (i,op) -> adom.transfer op res.(i)) preds.(j)) in
    let upd_except_cfc j cfc =
      if j <> cfg.entry then
	res.(j) <- join_list res.(j)
	  (List.map (fun (i,op) -> adom.transfer op res.(i))
	     (List.filter (fun (i,op) -> not (Ptset.mem i cfc)) preds.(j)))
    in
    let nb_down = !option_down_iterations in
    let rec iter_component down = function
      | L (I head::rest,cfc) ->
	  let rec aux down = function
	      [] ->
		let old_ab = res.(head) in
		let _ = upd head in
		let new_ab = res.(head) in
		  if down >= nb_down || (new_ab = old_ab) then ()
		  else if not (adom.order new_ab old_ab) then
		    begin
		      res.(head) <- adom.widen old_ab new_ab;
		      aux (-1) rest
		    end
		  else (upd head; aux (down+1) rest)
	    | b::q -> iter_component down b; aux down q in
	    upd_except_cfc head cfc;
	    aux down rest
      | I i -> upd i
      | _ -> assert false in
      List.iter (iter_component (-1)) b;
      check_fixpoint adom cfg res;
      res

let run adom cfg =
  let b = get_bourdoncle cfg in
    run_with_bourdoncle adom b cfg
