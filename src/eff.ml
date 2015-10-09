let usage = "Usage: eff [option] ... [file] ..."

let interactive_shell = ref true
let pervasives = ref true
let wrapper = ref (Some ["rlwrap"; "ledit"])


(* We look for pervasives.eff _first_ next to the executable and _then_ in the relevant
   install directory. This makes it easier to experiment with pervasives.eff because
   eff will work straight from the build directory. We are probably creating a security
   hole, but we'll deal with that when eff actually gets used by more than a dozen
   people. *)

let pervasives_file =
  let pervasives_development = Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff" in
  ref (if Sys.file_exists pervasives_development
    then pervasives_development
    else Filename.concat Version.effdir "pervasives.eff")

(* A list of files to be loaded and run. *)
let files = ref []
let add_file interactive filename = (files := (filename, interactive) :: !files)

(* Command-line options *)
let options = Arg.align [
  ("--pervasives",
   Arg.String (fun str -> pervasives_file := str),
   " Specify the pervasives.eff file");
  ("--effects",
   Arg.Set Type.effects,
   " Show the output of effect inference");
  ("--no-beautify",
    Arg.Set Type.disable_beautify,
    " Do not beautify types");
  ("--no-pervasives",
    Arg.Clear pervasives,
    " Do not load pervasives.eff");
  ("--no-types",
    Arg.Set Infer.disable_typing,
    " Disable typechecking");
  ("--wrapper",
    Arg.String (fun str -> wrapper := Some [str]),
    "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
  ("--no-wrapper",
    Arg.Unit (fun () -> wrapper := None),
    " Do not use a command-line wrapper");
  ("--ascii",
    Arg.Set Symbols.ascii,
    " Use ASCII output");
  ("-v",
    Arg.Unit (fun () ->
      print_endline ("eff " ^ Version.version ^ "(" ^ Sys.os_type ^ ")");
      exit 0),
    " Print version information and exit");
  ("--warn-sequencing", Arg.Set Infer.warn_implicit_sequencing,
   " Print warning about implicit sequencing");
  ("-n",
    Arg.Clear interactive_shell,
    " Do not run the interactive toplevel");
  ("-l",
    Arg.String (fun str -> add_file false str),
    "<file> Load <file> into the initial environment");
  ("-V",
    Arg.Set_int Print.verbosity,
    "<n> Set printing verbosity to <n>");
]

(* Treat anonymous arguments as files to be run. *)
let anonymous str =
  add_file true str;
  interactive_shell := false

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
        ctxenv := Shell.exec_cmd true !ctxenv cmd
      with
        | Error.Error err -> Print.error err
        | Sys.Break -> prerr_endline "Interrupted."
    done
  with End_of_file -> ()

(* Main program *)
let main =
  Sys.catch_break true;
  (* Parse the arguments. *)
  Arg.parse options anonymous usage;
  (* Attemp to wrap yourself with a line-editing wrapper. *)
  if !interactive_shell then
    begin match !wrapper with
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
  if !pervasives then add_file false !pervasives_file;
  try
    (* Run and load all the specified files. *)
    let ctxenv = List.fold_left Shell.use_file Shell.initial_state !files in
    if !interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Print.error err; exit 1
