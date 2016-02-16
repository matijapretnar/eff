let usage = "Usage: eff [option] ... [file] ..."
let wrapper = ref (Some ["rlwrap"; "ledit"])

let help_text = "Toplevel commands:
#type <expr>;;     print the type of <expr> without evaluating it
#reset;;           forget all definitions (including pervasives)
#help;;            print this help
#quit;;            exit eff
#use \"<file>\";;  load commands from file";;

(* A list of files to be loaded and run. *)
let files = ref []
let to_be_compiled = ref []
let add_file interactive filename = (files := (filename, interactive) :: !files)
let load_pervasives = ref true
let compile_file filename = (load_pervasives := false; to_be_compiled := filename :: !to_be_compiled; Config.interactive_shell := false)

(* Command-line options *)
let options = Arg.align [
  ("--pervasives",
   Arg.String (fun str -> Config.pervasives_file := Config.PervasivesFile str),
   " Specify the pervasives.eff file");
  ("--no-effects",
   Arg.Clear Config.effect_annotations,
   " Hide the output of effect inference");
  ("--no-beautify",
    Arg.Set Config.disable_beautify,
    " Do not beautify types");
  ("--no-pervasives",
    Arg.Unit (fun () -> Config.pervasives_file := Config.PervasivesNone),
    " Do not load pervasives.eff");
  ("--no-types",
    Arg.Set Config.disable_typing,
    " Disable typechecking");
  ("--wrapper",
    Arg.String (fun str -> wrapper := Some [str]),
    "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
  ("--no-wrapper",
    Arg.Unit (fun () -> wrapper := None),
    " Do not use a command-line wrapper");
  ("--ascii",
    Arg.Set Config.ascii,
    " Use ASCII output");
  ("-v",
    Arg.Unit (fun () ->
      print_endline ("eff " ^ Version.version ^ "(" ^ Sys.os_type ^ ")");
      exit 0),
    " Print version information and exit");
  ("-n",
    Arg.Clear Config.interactive_shell,
    " Do not run the interactive toplevel");
  ("-l",
    Arg.String (fun str -> add_file false str),
    "<file> Load <file> into the initial environment");
  ("--compile",
    Arg.String (fun str -> compile_file str),
    "<file> Compile <file>");
  ("-V",
    Arg.Set_int Config.verbosity,
    "<n> Set printing verbosity to <n>");
]

(* Treat anonymous arguments as files to be run. *)
let anonymous str =
  add_file true str;
  Config.interactive_shell := false


(* Parser wrapper *)
let parse parser lex =
  try
    parser Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~loc:(Location.of_lexeme lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~loc:(Location.of_lexeme lex) "unrecognised symbol."


type state = {
  environment : RuntimeEnv.t;
  change : Scheme.dirty_scheme -> Scheme.dirty_scheme;
  typing : Infer.state;
}

let initial_ctxenv = {
  environment = RuntimeEnv.empty;
  change = Common.id;
  typing = Infer.initial;
}

let type_cmd st (cmd, loc) =
  let ty_st = {Infer.change = st.change; Infer.typing = st.typing} in
  let cmd, ty_st = Infer.infer_toplevel ~loc ty_st cmd in
  let st = {st with change = ty_st.Infer.change; typing = ty_st.Infer.typing} in
  (cmd, loc), st

let type_cmds st cmds =
  let cmds, st =
    List.fold_left (fun (cmds, st) cmd ->
      let cmd, st = type_cmd st cmd in
      (cmd :: cmds, st)
    ) ([], st) cmds
  in
  List.rev cmds, st

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd interactive st (cmd, loc) =
  let (cmd, loc), st = type_cmd st (cmd, loc) in
  match cmd with
  | Typed.Computation c ->
      let v = Eval.run st.environment c in
      if interactive then Format.printf "@[- : %t = %t@]@."
        (Scheme.print_dirty_scheme c.Typed.scheme)
        (Value.print_value v);
      st
  | Typed.TypeOf c ->
      Format.printf "@[- : %t@]@." (Scheme.print_dirty_scheme c.Typed.scheme);
      st
  | Typed.Reset ->
      Tctx.reset ();
      print_endline ("Environment reset."); initial_ctxenv
  | Typed.Help ->
      print_endline help_text;
      st
  | Typed.DefEffect (eff, (ty1, ty2)) ->
      st
  | Typed.Quit ->
      exit 0
  | Typed.Use fn ->
      use_file st (fn, interactive)
  | Typed.TopLet (defs, vars) ->
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs st.environment
      in
        if interactive then begin
          List.iter (fun (x, tysch) ->
                       match RuntimeEnv.lookup x env with
                         | None -> assert false
                         | Some v ->
                         Format.printf "@[val %t : %t = %t@]@." (Typed.Variable.print x) (Scheme.print_ty_scheme tysch) (Value.print_value v))
            vars
        end;
        {
          st with
          environment = env;
        }
    | Typed.TopLetRec (defs, vars) ->

        let env = Eval.extend_let_rec st.environment defs in
          if interactive then begin
            List.iter (fun (x, tysch) -> Format.printf "@[val %t : %t = <fun>@]@." (Typed.Variable.print x) (Scheme.print_ty_scheme tysch)) vars
          end;
        {
          st with
          environment = env;
        }
    | Typed.External (x, ty, f) ->
        begin match Common.lookup f External.values with
          | Some v -> {
              st with
              environment = RuntimeEnv.update x v st.environment;
            }
          | None -> Error.runtime "unknown external symbol %s." f
        end
    | Typed.Tydef tydefs ->
        st


and use_file env (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
  let cmds = List.map Desugar.toplevel cmds in
    List.fold_left (exec_cmd interactive) env cmds

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
  let cmds = List.map Desugar.toplevel (pervasives_cmds @ cmds) in
  let cmds, _ = type_cmds st cmds in
  Print.debug "UNOPTIMIZED CODE:@.%t@." (CamlPrint.print_commands cmds);
  let cmds = Optimize.optimize_commands cmds in
  Print.debug "OPTIMIZED CODE:@.%t@." (CamlPrint.print_commands cmds);

  (* look for header.ml next to the executable  *)
  let header_file = Filename.concat (Filename.dirname Sys.argv.(0)) "header.ml" in
  let header_channel = open_in header_file in
  let n = in_channel_length header_channel in
  let header = String.create n in
  really_input header_channel header 0 n;
  close_in header_channel;

  let compiled_file = CamlPrint.compiled_filename filename in
  let out_channel = open_out compiled_file in
  Format.fprintf (Format.formatter_of_out_channel out_channel) "%s\n;;\n%t@." header (CamlPrint.print_commands cmds);
  flush out_channel;
  close_out out_channel

(* Interactive toplevel *)
let toplevel ctxenv =
  let eof = match Sys.os_type with
    | "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "EOF"
  in
  print_endline ("eff " ^ Version.version);
  print_endline ("[Type " ^ eof ^ " to exit or #help;; for help.]");
  try
    let ctxenv = ref ctxenv in
    while true do
      try
        let cmd = Lexer.read_toplevel (parse Parser.commandline) () in
        let cmd = Desugar.toplevel cmd in
        ctxenv := exec_cmd true !ctxenv cmd
        with
        | Error.Error err -> Error.print err
        | Sys.Break -> prerr_endline "Interrupted."
    done
  with End_of_file -> ()

(* Main program *)
let main =
  Sys.catch_break true;
  (* Parse the arguments. *)
  Arg.parse options anonymous usage;
  (* Attemp to wrap yourself with a line-editing wrapper. *)
  if !Config.interactive_shell then
    begin match !Config.wrapper with
      | None -> ()
      | Some lst ->
          let n = Array.length Sys.argv + 2 in
          let args = Array.make n "" in
            Array.blit Sys.argv 0 args 1 (n - 2);
            args.(n - 1) <- "--no-wrapper";
            List.iter
              (fun wrapper ->
                 try
                   args.(0) <- wrapper;
                   Unix.execvp wrapper args
                 with Unix.Unix_error _ -> ())
              lst
    end;
  (* Files were listed in the wrong order, so we reverse them *)
  files := List.rev !files;
  (* Load the pervasives. *)
  begin
    match !Config.pervasives_file with
    | Config.PervasivesNone -> ()
    | Config.PervasivesFile f -> if !load_pervasives then add_file false f
    | Config.PervasivesDefault ->
      (* look for pervasives next to the executable and in the installation
      directory if they are not there *)
      let pervasives_development = Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff" in
      let f = (if Sys.file_exists pervasives_development
        then pervasives_development
        else Filename.concat Version.effdir "pervasives.eff") in
      if !load_pervasives then add_file false f
  end;
  try
    (* Run and load all the specified files. *)
    let ctxenv = List.fold_left use_file initial_ctxenv !files in
    List.iter (compile_file ctxenv) !to_be_compiled;
    if !Config.interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Error.print err; exit 1
