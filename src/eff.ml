module S = Syntax
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
  ref (if Sys.file_exists "pervasives.eff"
       then Filename.concat (Filename.dirname Sys.argv.(0)) "pervasives.eff"
       else Filename.concat Version.effdir "pervasives.eff")

(* A list of files to be loaded and run. *)
let files = ref []
let add_file interactive filename = (files := (filename, interactive) :: !files)

(* Command-line options *)
let options = Arg.align [
  ("--pervasives",
   Arg.String (fun str -> pervasives_file := str),
   " Specify the pervasives.eff file");
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
  (Ctx.initial, Eval.initial)

let exec_topdef interactive (ctx, env) (d,pos) =
  match d with
  | S.TopLet defs ->
      let defs = C.assoc_map Desugar.computation defs in
      let vars, ctx = Infer.infer_let ctx (ref Type.identity_subst) pos defs in
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs env
      in
        if interactive then begin
          List.iter (fun (x, (ps,t)) ->
                       match Eval.lookup x env with
                         | None -> assert false
                         | Some v -> Format.printf "@[val %s : %t = %t@]@." x (Print.ty ps t) (Print.value v))
            vars
        end;
        (ctx, env)
  | S.TopLetRec defs ->
      let defs = C.assoc_map Desugar.let_rec defs in
      let vars, ctx = Infer.infer_let_rec ctx (ref Type.identity_subst) pos defs in
      let env = Eval.extend_let_rec env defs in
        if interactive then begin
          List.iter (fun (x,(ps,t)) -> Format.printf "@[val %s : %t = <fun>@]@." x (Print.ty ps t)) vars
        end;
        (ctx, env)
  | S.External (x, t, f) ->
    let ctx = Ctx.extend_var x (Desugar.external_ty t) ctx in
      begin match C.lookup f External.symbols with
        | Some v -> (ctx, Eval.update x v env)
        | None -> Error.runtime ~pos:pos "unknown external symbol %s." f
      end
  | S.Tydef tydefs ->
      let tydefs = List.map (fun (t, (ps, d)) -> (t, Desugar.tydef ps d)) tydefs in
      Tctx.global := Tctx.extend_tydefs ~pos:pos !Tctx.global tydefs;
      (ctx, env)

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)

let infer_top_comp ctx c =
  let cstr = ref [] in
  let ty = Infer.infer_comp ctx cstr c in
  let sbst = Unify.solve !cstr in
  let ctx = Ctx.subst_ctx sbst ctx in
  let ty = Type.subst_ty sbst ty in
  let ps = (if Infer.nonexpansive (fst c) then Ctx.generalize ctx ty else []) in
  ctx, (ps, ty)

let rec exec_cmd interactive (ctx, env) e =
  match e with
  | S.Term c ->
      let c = Desugar.computation c in
      let ctx, (ps, t) = infer_top_comp ctx c in
      let v = Eval.run env c in
      if interactive then Format.printf "@[- : %t = %t@]@." (Print.ty ps t) (Print.value v);
      (ctx, env)
  | S.TypeOf c ->
      let c = Desugar.computation c in
      let ctx, (ps, t) = infer_top_comp ctx c in
      Format.printf "@[- : %t@]@." (Print.ty ps t);
      (ctx, env)
  | S.Reset ->
      Tctx.reset ();
      print_endline ("Environment reset."); initial_ctxenv
  | S.Help ->
      print_endline help_text; (ctx, env)
  | S.Quit -> exit 0
  | S.Use fn -> use_file (ctx, env) (fn, interactive)
  | S.Topdef def -> exec_topdef interactive (ctx, env) def

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
