module S = Syntax
module C = Common

let version = "3.0"

let usage = "Usage: eff [option] ... [file] ..."
let interactive = ref true
let pervasives = ref true

(* We set up a list of files to be loaded and run. *)
let files = ref []
let add_file f = (files := f :: !files)

(* Command-line options *)
let options = Arg.align [
  ("--no-pervasives",
    Arg.Clear pervasives,
    " Do not load pervasives.eff");
  ("--no-types",
    Arg.Set Infer.disable_typing,
    " Disable typechecking");
  ("-version",
    Arg.Unit (fun () ->
                print_endline ("eff " ^ version ^ ":\n" ^
                                "  changeset: " ^ Version.changeset ^ "\n" ^
                                "  system:    " ^ Version.os ^ "\n" ^
                                "  date:      " ^ Version.date) ;
                exit 0),
    " Print full version information");
  ("--warn-sequencing", Arg.Set Infer.warn_implicit_sequencing,
   " Print warning about implicit sequencing");
  ("-n",
    Arg.Clear interactive,
    " Do not run the interactive toplevel");
  ("-l",
    Arg.String (fun str -> add_file str),
    "<file> Load <file> into the initial environment");
  ("-V",
    Arg.Set_int Print.verbosity,
    "<n> Set printing verbosity to <n>");
]

(* Treat anonymous arguments as files to be run. *)
let anonymous str =
  add_file str;
  interactive := false


(* Parser wrapper *)
let parse parser lex =
  try
    parser Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~pos:(Lexer.position_of_lex lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~pos:(Lexer.position_of_lex lex) "unrecognised symbol."

let initial_environment =
  (Ctx.initial, Eval.initial)

let exec_topdef (ctx, env) (d,pos) =
  match d with
  | S.TopLet defs ->
      let defs = C.assoc_map Desugar.computation defs in
      let vars, ctx = Infer.infer_top_let ctx pos defs in
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs env
      in
        if !interactive then begin
          List.iter (fun (x, (ps,t)) ->
                       match Eval.lookup x env with
                         | None -> assert false
                         | Some v -> Format.printf "@[val %s : %t = %t@]@." x (Print.ty ps t) (Print.value v))
            vars
        end ;
        (ctx, env)
  | S.TopLetRec defs ->
      let defs = C.assoc_map Desugar.let_rec defs in
      let vars, ctx = Infer.infer_top_let_rec ctx pos defs in
      let env = Eval.extend_let_rec env defs in
        if !interactive then begin
          List.iter (fun (x,(ps,t)) -> Format.printf "@[val %s : %t = <fun>@]@." x (Print.ty ps t)) vars
        end ;
        (ctx, env)
  | S.External (x, t, f) ->
    let lst = List.fold_right (fun p lst -> (p, Type.next_param ()) :: lst) (S.ty_fv t) [] in
    let s = C.assoc_map (fun p -> Type.Param p) lst in
    let ctx = Ctx.extend_var x (List.map snd lst, Desugar.ty s t) ctx in
      begin match C.lookup f External.symbols with
        | Some v -> (ctx, Eval.update x v env)
        | None -> Error.runtime ~pos:pos "unknown external symbol %s." f
      end
  | S.Tydef defs ->
      let defs = List.map (fun (t, (ps, d)) -> (t, Desugar.tydef ps d)) defs in
      let ctx = Infer.check_tydef ctx pos defs in
      (ctx, env)

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd (ctx, env) e =
  match e with
  | S.Expr c ->
      let c = Desugar.computation c in
      let ctx, (ps, t) = Infer.infer_top_comp ctx c in
      let v = Eval.run env c in
      if !interactive then Format.printf "@[- : %t = %t@]@." (Print.ty ps t) (Print.value v) ;
      (ctx, env)
  | S.TypeOf c ->
      let c = Desugar.computation c in
      let ctx, (ps, t) = Infer.infer_top_comp ctx c in
      Format.printf "@[- : %t@]@." (Print.ty ps t) ;
      (ctx, env)

  | S.Reset ->
      print_endline ("Environment reset."); initial_environment
  | S.Help ->
      print_endline ("Read the source.") ; (ctx, env)
  | S.Quit -> exit 0
  | S.Use fn -> use_file (ctx, env) fn
  | S.Topdef def -> exec_topdef (ctx, env) def

and use_file env fn =
  let cmds = Lexer.read_file (parse Parser.file) fn in
  List.fold_left exec_cmd env cmds

let rec loop env =
  try
    let cmd = Lexer.read_toplevel (parse Parser.commandline) () in
    let env = exec_cmd env cmd in
    loop env
  with
    | Error.Error err -> Print.error err; loop env
    | Sys.Break -> prerr_endline "Interrupted."; loop env

(* Interactive toplevel *)
let toplevel env =
  let eof = match Sys.os_type with
    | "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "EOF"
  in
  print_endline ("eff " ^ version);
  print_endline ("Press " ^ eof ^ " to exit.");
  try loop env
  with End_of_file -> ()

(* Main program *)
let main =
  Sys.catch_break true;
  (* Parse the arguments. *)
  Arg.parse options anonymous usage;
  (* Files were listed in the wrong order, so we reverse them *)
  files := List.rev !files;
  (* Load the pervasives. *)
  if !pervasives then
    begin
      let eff_dir = Filename.dirname Sys.argv.(0) in
      add_file (Filename.concat eff_dir "pervasives.eff")
    end ;
  try
    (* Run and load all the specified files. *)
    let i = !interactive in
      interactive := false ;
      let env = List.fold_left use_file initial_environment !files in
        interactive := i ;
        if !interactive then toplevel env
  with
    Error.Error err -> Print.error err; exit 1
