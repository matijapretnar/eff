let usage = "Usage: eff [option] ... [file] ..."

module Backend = Eval.Backend(struct let output = Format.std_formatter end)

(* DELETE THIS, it is only here to typecheck backends in progress. *)
module Backend_test = 
McocCompile.Backend(
  struct 
    let warnings = Format.std_formatter
    let response = Format.std_formatter 
    let output = Format.formatter_of_out_channel (open_out "test.ml")
    let printing = true
  end)
    
module Shell = Shell.Make(Backend_test)
(* A list of files to be loaded and run. *)
type use_file = Run of string | Load of string

let file_queue = ref []

let enqueue_file filename = file_queue := filename :: !file_queue

(* Command-line options *)
let options =
  Arg.align
    [ ( "--pervasives"
      , Arg.String
          (fun str -> Config.pervasives_file := Config.PervasivesFile str)
      , " Specify the pervasives.eff file" )
    ; ( "--no-pervasives"
      , Arg.Unit (fun () -> Config.pervasives_file := Config.PervasivesNone)
      , " Do not load pervasives.eff" )
    ; ( "--wrapper"
      , Arg.String (fun str -> Config.wrapper := Some [str])
      , "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)"
      )
    ; ( "--no-wrapper"
      , Arg.Unit (fun () -> Config.wrapper := None)
      , " Do not use a command-line wrapper" )
    ; ("--no-types", Arg.Set Config.disable_typing, " Disable typechecking")
    ; ("--ascii", Arg.Set Config.ascii, " Use ASCII output")
    ; ( "-v"
      , Arg.Unit
          (fun () ->
            print_endline ("eff " ^ Config.version ^ "(" ^ Sys.os_type ^ ")") ;
            exit 0 )
      , " Print version information and exit" )
    ; ( "-n"
      , Arg.Clear Config.interactive_shell
      , " Do not run the interactive toplevel" )
    ; ( "-l"
      , Arg.String (fun str -> enqueue_file (Load str))
      , "<file> Load <file> into the initial environment" )
    ; ("-V", Arg.Set_int Config.verbosity, "<n> Set printing verbosity to <n>")
    ]


(* Treat anonymous arguments as files to be run. *)
let anonymous filename =
  enqueue_file (Run filename) ;
  Config.interactive_shell := false


let run_under_wrapper wrapper args =
  let n = Array.length args + 2 in
  let args_with_wrapper = Array.make n "" in
  args_with_wrapper.(0) <- wrapper ;
  Array.blit args 0 args_with_wrapper 1 (n - 2) ;
  args_with_wrapper.(n - 1) <- "--no-wrapper" ;
  Unix.execvp wrapper args_with_wrapper


let read_toplevel () =
  let has_semisemi str =
    let in_quote = ref false in
    let last_backslash = ref false in
    let last_semi = ref false in
    let semisemi = ref false in
    let i = ref 0 in
    while !i < String.length str && not !semisemi do
      ( match (str.[!i], !last_backslash, !in_quote, !last_semi) with
      | '\\', b, _, _ ->
          last_backslash := not b ;
          last_semi := false
      | '"', false, b, _ ->
          in_quote := not b ;
          last_backslash := false ;
          last_semi := false
      | ';', false, false, b ->
          semisemi := b ;
          last_semi := true
      | _, _, _, _ ->
          last_backslash := false ;
          last_semi := false ) ;
      incr i
    done ;
    if !semisemi then Some (String.sub str 0 !i) else None
  in
  let rec read_more prompt acc =
    match has_semisemi acc with
    | Some acc -> acc
    | None ->
        print_string prompt ;
        let str = read_line () in
        read_more "  " (acc ^ "\n" ^ str)
  in
  let str = read_more "# " "" in
  str ^ "\n"


(* Interactive toplevel *)
let toplevel st =
  let eof =
    match Sys.os_type with
    | "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "EOF"
  in
  print_endline ("eff " ^ Config.version) ;
  print_endline ("[Type " ^ eof ^ " to exit or #help;; for help.]") ;
  try
    let st = ref st in
    Sys.catch_break true ;
    while true do
      let source = read_toplevel () in
      try st := Shell.execute_source source !st with
      | Error.Error err -> Error.print err
      | Sys.Break -> prerr_endline "Interrupted."
    done
  with End_of_file -> ()


(* Main program *)
let main =
  (* Parse the arguments. *)
  Arg.parse options anonymous usage ;
  (* Attemp to wrap yourself with a line-editing wrapper. *)
  ( if !Config.interactive_shell then
      match !Config.wrapper with
      | None -> ()
      | Some lst ->
          List.iter
            (fun wrapper ->
              try run_under_wrapper wrapper Sys.argv
              with Unix.Unix_error _ -> () )
            lst ) ;
  (* Files were listed in the wrong order, so we reverse them *)
  file_queue := List.rev !file_queue ;
  (* Load the pervasives. *)
  ( match !Config.pervasives_file with
  | Config.PervasivesNone -> ()
  | Config.PervasivesFile f -> enqueue_file (Load f)
  | Config.PervasivesDefault ->
      (* look for pervasives next to the executable and in the installation
      directory if they are not there *)
      let pervasives_development =
        Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff"
      in
      let f =
        if Sys.file_exists pervasives_development then pervasives_development
        else Filename.concat Local.effdir "pervasives.eff"
      in
      enqueue_file (Load f) ) ;
  try
    (* Run and load all the specified files. *)
    let execute_file env = function
      | Run filename -> Shell.execute_file filename env
      | Load filename -> Shell.load_file filename env
    in
    let st = List.fold_left execute_file Shell.initial_state !file_queue in
    if !Config.interactive_shell then toplevel st
  with Error.Error err -> Error.print err ; exit 1
