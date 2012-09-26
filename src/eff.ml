module C = Common

let usage = "Usage: eff [option] ... [file] ..."
let interactive_shell = ref true
let pervasives = ref true
let wrapper = ref (Some ["rlwrap"; "ledit"])

let help_text = "Toplevel commands:
#type <expr>;;     print the type of <expr> without evaluating it
#reset;;           forget all definitions (including pervasives)
#help;;            print this help
#quit;;            exit eff
#use \"<file>\";;  load commands from file";;

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


(* Parser wrapper *)
let parse parser lex =
  try
    parser Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~pos:(Lexer.position_of_lex lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~pos:(Lexer.position_of_lex lex) "unrecognised symbol."

let initial_ctxenv =
  (Ctx.empty, Eval.initial)

let exec_topdef interactive (ctx, env) (d,pos) =
  match d with
  | Syntax.TopLet defs ->
      let defs = Desugar.top_let defs in
      (* XXX What to do about the dirts? *)
      (* XXX What to do about the fresh instances? *)
      let ctx, vars, _, _, _, _ = Infer.infer_let ctx pos defs in
      List.iter (fun (p, c) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs env
      in
(*         if interactive then begin
          List.iter (fun (x, tysch) ->
                       match Eval.lookup x env with
                         | None -> assert false
                         | Some v ->
                         Format.printf "@[val %d : %t = %t@]@." x (Print.beautified_ty_scheme tysch) (Print.value v))
            vars
        end;
 *)        (ctx, env)
  | Syntax.TopLetRec defs ->
      let defs = Desugar.top_let_rec defs in
      let ctx, _, cstr = Infer.infer_let_rec ctx pos defs in
      List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
      let env = Eval.extend_let_rec env defs in
(*         if interactive then begin
          List.iter (fun (x, tysch) -> Format.printf "@[val %d : %t = <fun>@]@." x (Print.beautified_ty_scheme tysch)) vars
        end;
 *)        (ctx, env)
  | Syntax.External (x, t, f) ->
    let (x, t) = Desugar.external_ty (Tctx.is_effect ~pos:pos) x t in
    let ctx = Ctx.extend ctx x t in
      begin match C.lookup f External.values with
        | Some v -> (ctx, Eval.update x v env)
        | None -> Error.runtime "unknown external symbol %s." f
      end
  | Syntax.Tydef tydefs ->
      let tydefs = Desugar.tydefs ~pos tydefs in
      Tctx.extend_tydefs ~pos tydefs ;
      (ctx, env)

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)

let infer_top_comp ctx c =
  let ctx, (frshs, ty, drt), cstr = Infer.infer_comp ctx c in
  let tysch = Unify.normalize (ctx, ty, cstr) in
  Exhaust.check_comp c ;
  (* let cnstr = Unify.constraints_of_graph remaining in *)
  (* XXX What to do about the fresh instances? *)
  (* XXX Here, we need to show what type parameters are polymorphic or not. *)
  (*     I am disabling it because we are going to try a new approach. *)
  tysch, drt, frshs

let rec exec_cmd interactive (ctx, env) e =
  match e with
  | Syntax.Term c ->
      let c = Desugar.top_computation c in
      let tysch, drt, frsh = infer_top_comp ctx c in
      let v = Eval.run env c in
      if interactive then Format.printf "@[- : %t %t = %t@]@."
        (Print.fresh_instances frsh)
        (Print.beautified_ty_scheme tysch)
        (Print.value v);
      (ctx, env)
  | Syntax.TypeOf c ->
      let c = Desugar.top_computation c in
      let tysch, drt, frsh = infer_top_comp ctx c in
      Format.printf "@[- : %t@]@." (Print.beautified_dirty_scheme tysch drt);
      (ctx, env)
  | Syntax.Reset ->
      Tctx.reset ();
      print_endline ("Environment reset."); initial_ctxenv
  | Syntax.Help ->
      print_endline help_text; (ctx, env)
  | Syntax.Quit -> exit 0
  | Syntax.Use fn -> use_file (ctx, env) (fn, interactive)
  | Syntax.Topdef def -> exec_topdef interactive (ctx, env) def

and use_file env (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
    List.fold_left (exec_cmd interactive) env cmds

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
        ctxenv := exec_cmd true !ctxenv cmd
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
    let ctxenv = List.fold_left use_file initial_ctxenv !files in
    if !interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Print.error err; exit 1
