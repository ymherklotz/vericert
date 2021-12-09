open Camlcoq

let indent i = String.make (2 * i) ' '

let rec print_bourdoncle i pp =
  function
  | Bourdoncle.I n ->
     Printf.fprintf pp "%sI %d\n" (indent i) (P.to_int n)
  | Bourdoncle.L (h, b) ->
    Printf.fprintf pp "%sL %d\n" (indent i) (P.to_int h);
    List.iter (fun a -> Printf.fprintf pp "%a" (print_bourdoncle (i+1)) a) b

let print_if optdest loop =
  match !optdest with
  | None -> ()
  | Some f ->
    let oc = open_out f in
    print_bourdoncle 0 oc loop;
    close_out oc

let destination_loops : string option ref = ref None
let print_loops = print_if destination_loops
