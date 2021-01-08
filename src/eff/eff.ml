open Utils
module B = Backend

let usage = "Usage: eff [option] ... [file] ..."

(* A list of files to be loaded and run. *)
type use_file = Run of string | Load of string

let file_queue = ref []

let enqueue_file filename = file_queue := filename :: !file_queue

(* Command-line options *)
let options =
  Arg.align
    [
      ( "--no-stdlib",
        Arg.Clear Config.use_stdlib,
        " Do not load the standard library" );
      ( "--wrapper",
        Arg.String (fun str -> Config.wrapper := Some [ str ]),
        "<program> Specify a command-line wrapper to be used (such as rlwrap \
         or ledit)" );
      ( "--no-wrapper",
        Arg.Unit (fun () -> Config.wrapper := None),
        " Do not use a command-line wrapper" );
      ( "--compile-multicore-ocaml",
        Arg.String (fun filename -> Config.backend := Multicore filename),
        "<file> Compile the Eff code into a Multicore OCaml file <file>" );
      ("--ascii", Arg.Set Config.ascii, " Use ASCII output");
      ( "-v",
        Arg.Unit
          (fun () ->
            print_endline ("eff " ^ Config.version ^ "(" ^ Sys.os_type ^ ")");
            exit 0),
        " Print version information and exit" );
      ( "-l",
        Arg.String (fun str -> enqueue_file (Load str)),
        "<file> Load <file> into the initial environment" );
      ("-V", Arg.Set_int Config.verbosity, "<n> Set printing verbosity to <n>");
    ]

(* Treat anonymous arguments as files to be run. *)
let anonymous filename =
  enqueue_file (Run filename);
  Config.interactive_shell := false

let run_under_wrapper wrapper args =
  let n = Array.length args + 2 in
  let args_with_wrapper = Array.make n "" in
  args_with_wrapper.(0) <- wrapper;
  Array.blit args 0 args_with_wrapper 1 (n - 2);
  args_with_wrapper.(n - 1) <- "--no-wrapper";
  Unix.execvp wrapper args_with_wrapper

let read_toplevel () =
  let has_semisemi str =
    let in_quote = ref false in
    let last_backslash = ref false in
    let last_semi = ref false in
    let semisemi = ref false in
    let i = ref 0 in
    while !i < String.length str && not !semisemi do
      (match (str.[!i], !last_backslash, !in_quote, !last_semi) with
      | '\\', b, _, _ ->
          last_backslash := not b;
          last_semi := false
      | '"', false, b, _ ->
          in_quote := not b;
          last_backslash := false;
          last_semi := false
      | ';', false, false, b ->
          semisemi := b;
          last_semi := true
      | _, _, _, _ ->
          last_backslash := false;
          last_semi := false);
      incr i
    done;
    if !semisemi then Some (String.sub str 0 !i) else None
  in
  let rec read_more prompt acc =
    match has_semisemi acc with
    | Some acc -> acc
    | None ->
        print_string prompt;
        let str = read_line () in
        read_more "  " (acc ^ "\n" ^ str)
  in
  let str = read_more "# " "" in
  str ^ "\n"

(* Interactive toplevel *)
let toplevel execute_source state =
  let eof =
    match Sys.os_type with
    | "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "EOF"
  in
  Format.fprintf !Config.output_formatter "eff %s@." Config.version;
  Format.fprintf !Config.output_formatter
    "[Type %s to exit or #help;; for help.]@." eof;
  let state = ref state in
  Sys.catch_break true;
  try
    while true do
      let source = read_toplevel () in
      try state := execute_source source !state with
      | Error.Error err -> Error.print err
      | Sys.Break -> prerr_endline "Interrupted."
    done;
    !state
  with End_of_file -> !state

(* Main program *)
let main =
  (* Parse the arguments. *)
  Arg.parse options anonymous usage;
  (* Attemp to wrap yourself with a line-editing wrapper. *)
  (if !Config.interactive_shell then
   match !Config.wrapper with
   | None -> ()
   | Some lst ->
       List.iter
         (fun wrapper ->
           try run_under_wrapper wrapper Sys.argv with Unix.Unix_error _ -> ())
         lst);
  (* Files were listed in the wrong order, so we reverse them *)
  file_queue := List.rev !file_queue;
  try
    let (module Backend : Backend.BackendSignature.T) =
      match !Config.backend with
      | Config.Runtime -> (module Runtime.Backend)
      | Config.Multicore output_file ->
          (module BackendMulticore.MulticoreCompile.Backend (struct
            let output_file = output_file
          end))
    in
    let (module Shell) = (module Shell.Make (Backend) : Shell.Shell) in
    (* Run and load all the specified files. *)
    let execute_file env = function
      | Run filename -> Shell.execute_file filename env
      | Load filename -> Shell.load_file filename env
    in
    let state = Shell.initialize () in
    let state =
      (* Load the standard library. *)
      if !Config.use_stdlib then
        let stdlib =
          match !Config.backend with
          | Config.Runtime -> B.Stdlib_eff.stdlib
          | Config.Multicore _ -> B.Stdlib_eff.multicoreStdlib
        in
        Shell.load_source stdlib state
      else state
    in
    let state = List.fold_left execute_file state !file_queue in
    let state =
      if !Config.interactive_shell then toplevel Shell.execute_source state
      else state
    in
    Shell.finalize state
  with Error.Error err ->
    Error.print err;
    exit 1
