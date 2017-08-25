let usage = "Usage: eff [option] ... [file] ..."

(* A list of files to be loaded and run. *)
let file_queue = ref []
let enqueue_file ~print_output filename =
    file_queue := (filename, print_output) :: !file_queue

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
    Arg.String (fun str -> Config.wrapper := Some [str]),
    "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
  ("--no-wrapper",
    Arg.Unit (fun () -> Config.wrapper := None),
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
    Arg.String (fun str -> enqueue_file ~print_output:false str),
    "<file> Load <file> into the initial environment");
  ("-V",
    Arg.Set_int Config.verbosity,
    "<n> Set printing verbosity to <n>");
]

(* Treat anonymous arguments as files to be run. *)
let anonymous str =
  enqueue_file ~print_output:true str;
  Config.interactive_shell := false


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
        ctxenv := Shell.use_toplevel Format.std_formatter !ctxenv
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
  file_queue := List.rev !file_queue;
  (* Load the pervasives. *)
  begin
    match !Config.pervasives_file with
    | Config.PervasivesNone -> ()
    | Config.PervasivesFile f -> enqueue_file ~print_output:false f
    | Config.PervasivesDefault ->
      (* look for pervasives next to the executable and in the installation
      directory if they are not there *)
      let pervasives_development = Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff" in
      let f = (if Sys.file_exists pervasives_development
        then pervasives_development
        else Filename.concat Version.effdir "pervasives.eff") in
      enqueue_file ~print_output:false f
  end;
  try
    (* Run and load all the specified files. *)
    let ignore_all_formatter =
      Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())
    in
    let ctxenv = List.fold_left (fun env (filename, print_output) ->
      if print_output then
        Shell.use_file Format.std_formatter filename env
      else
        Shell.use_file ignore_all_formatter filename env
    ) Shell.initial_state !file_queue in
    if !Config.interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Error.print err; exit 1
