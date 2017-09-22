let print_commands cmds =
  let print_command =
    if !Config.pure_print then PurePrint.print_command else SimplePrint.print_command
  in
  Print.sequence "\n\n;;\n\n" print_command cmds


let compile_file st filename =
  let pervasives_cmds =
    match !Config.pervasives_file with
    | Config.PervasivesNone -> []
    | Config.PervasivesFile f -> Lexer.read_file (parse Parser.file) f
    | Config.PervasivesDefault ->
      (* look for pervasives next to the executable and in the installation
         directory if they are not there *)
      let pervasives_development = Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff" in
      let f = (if Sys.file_exists pervasives_development
               then pervasives_development
               else Filename.concat Version.effdir "pervasives.eff") in
      Lexer.read_file (parse Parser.file) f
  in
  let cmds = Lexer.read_file (parse Parser.file) filename in
  (* Here, we insert a simple command to be later on able to separate the source from pervasives *)
  let separator = (Sugared.Term (Sugared.Const (Const.of_string "End of pervasives"), Location.unknown), Location.unknown) in
  let cmds = List.map Desugar.toplevel (pervasives_cmds @ separator :: cmds) in
  let cmds, _ = Infer.type_cmds st.Shell.typing cmds in
  let cmds_no_opt = cmds in
  let cmds = if !Config.disable_optimization then cmds else Optimize.optimize_commands cmds in

  (* read the source file *)
  let source_channel = open_in filename in
  let n = in_channel_length source_channel in
  let source = String.create n in
  really_input source_channel source 0 n;
  close_in source_channel;

  (* look for header.ml next to the executable  *)
  let header_file = Filename.concat (Filename.dirname Sys.argv.(0)) "header.ml" in
  let header_channel = open_in header_file in
  let n = in_channel_length header_channel in
  let header = String.create n in
  really_input header_channel header 0 n;
  close_in header_channel;

  ignore (Sys.command ("mkdir -p _tmp"));
  let temporary_file = "_tmp/" ^ CommonPrint.compiled_filename filename in
  let out_channel = open_out temporary_file in
  Format.fprintf (Format.formatter_of_out_channel out_channel)
    "%s\n;;\n%t@."
    header (print_commands cmds);
  flush out_channel;
  close_out out_channel;

  let compiled_file = CommonPrint.compiled_filename filename in
  ignore (Sys.command ("echo '(*\n=== GENERATED FROM " ^ filename ^ " ===' > " ^ compiled_file));
  ignore (Sys.command ("echo \"commit SHA: $(git rev-parse HEAD)\" >> " ^ compiled_file));
  ignore (Sys.command ("echo '=== BEGIN SOURCE ==='" ^ " >> " ^ compiled_file));
  ignore (Sys.command ("echo ''" ^ " >> " ^ compiled_file));
  ignore (Sys.command ("cat " ^ filename ^ " >> " ^ compiled_file));
  ignore (Sys.command ("echo ''" ^ " >> " ^ compiled_file));
  ignore (Sys.command ("echo '=== END SOURCE ===\n*)'" ^ " >> " ^ compiled_file));
  ignore (Sys.command ("echo ''" ^ " >> " ^ compiled_file));
  ignore (Sys.command ("ocamlc " ^ temporary_file));
  ignore (Sys.command ("ocamlc -dsource -w -A " ^ temporary_file ^ " >>" ^ compiled_file ^ " 2>&1"))
