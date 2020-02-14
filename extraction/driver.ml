open Compcert

let parse_c_file sourcename ifile =
  (* Simplification options *)
  let simplifs =
    "b" (* blocks: mandatory *)
    ^ (if false then "s" else "")
    ^ (if false then "f" else "")
    ^ (if false then "p" else "")
  in
  (* Parsing and production of a simplified C AST *)
  let ast = Parse.preprocessed_file simplifs sourcename ifile in
  (* Conversion to Csyntax *)
  let csyntax = Timing.time "CompCert C generation" C2C.convertProgram ast in
  (* Save CompCert C AST if requested *)
  PrintCsyntax.print_if csyntax;
  csyntax

let compile_c_file sourcename ifile ofile =
  (* Parse the ast *)
  let csyntax = parse_c_file sourcename ifile in
  (* Convert to Asm *)
  let rtl =
    match Compiler.apply_partial
            (CoqUp.transf_frontend csyntax) with
    | Errors.OK rtl ->
       rtl
    | Errors.Error msg ->
       let loc = file_loc sourcename in
       fatal_error loc "%a"  print_error msg in
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc

let compile_i_file sourcename preproname =
  if !option_interp then begin
      Machine.config := Machine.compcert_interpreter !Machine.config;
      let csyntax = parse_c_file sourcename preproname in
      Interp.execute csyntax;
      ""
    end else if !option_S then begin
      compile_c_file sourcename preproname
        (output_filename ~final:true sourcename ".c" ".s");
      ""
    end else begin
      let asmname =
        if !option_dasm
        then output_filename sourcename ".c" ".s"
        else tmp_file ".s" in
      compile_c_file sourcename preproname asmname;
      let objname = object_filename sourcename ".c" in
      assemble asmname objname;
      objname
    end

(* Processing of a .c file *)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
      preprocess sourcename (output_filename_default "-");
      ""
    end else begin
      let preproname = if !option_dprepro then
                         output_filename sourcename ".c" ".i"
                       else
                         tmp_file ".i" in
      preprocess sourcename preproname;
      compile_i_file sourcename preproname
    end

let _ = print_endline "Hello world"
