let usage = "Usage: eff [option] ... [file] ..."
let wrapper = Config.wrapper


(* A list of files to be loaded and run. *)
let files = ref []
let add_file interactive filename = (files := (filename, interactive) :: !files)

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
  ("--no-smart-print",
    Arg.Clear Config.smart_print,
    " Disable smart printing of type schemes");
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
        let cmd = Lexer.read_toplevel (Shell.parse Parser.commandline) () in
        let cmd = Desugar.toplevel cmd in
        ctxenv := Shell.exec_cmd Format.std_formatter true !ctxenv cmd
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
    | Config.PervasivesFile f -> add_file false f
    | Config.PervasivesDefault ->
      (* look for pervasives next to the executable and in the installation
      directory if they are not there *)
      let pervasives_development = Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff" in
      let f = (if Sys.file_exists pervasives_development
        then pervasives_development
        else Filename.concat Version.effdir "pervasives.eff") in
      add_file false f
  end;
  try
    (* Run and load all the specified files. *)
    let ctxenv = List.fold_left (Shell.use_file Format.std_formatter) Shell.initial_state !files in
    if !Config.interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Error.print err; exit 1
