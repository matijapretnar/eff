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
let to_be_optimized = ref []
let add_file interactive filename = (files := (filename, interactive) :: !files)
let optimize_file filename = (to_be_optimized := filename :: !to_be_optimized)

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
  ("--opt",
    Arg.String (fun str -> optimize_file str),
    "<file> Optimize <file>");
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

let infer_top_comp st c =
  let c' = Infer.type_comp st.typing c in
  let ctx', (ty', drt'), cnstrs' = c'.Typed.scheme in
  let change = Scheme.add_to_top ~loc:c'.Typed.location ctx' cnstrs' in
  let top_change = Common.compose st.change change in
  let ctx = match c'.Typed.term with
  | Typed.Value _ -> ctx'
  | _ -> (Desugar.fresh_variable (Some "$top_comp"), ty') :: ctx'
  in
  let drty_sch = top_change (ctx, (ty', drt'), cnstrs') in
  Exhaust.check_comp c;

  drty_sch, c', top_change

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd interactive st (d,loc) =
  match d with
  | Sugared.Term c ->
      let c = Desugar.top_computation c in
      let drty_sch, c', new_change = infer_top_comp st c in
      let v = Eval.run st.environment c' in
      if interactive then Format.printf "@[- : %t = %t@]@."
        (Scheme.print_dirty_scheme drty_sch)
        (Value.print_value v);
      {st with change = new_change}
  | Sugared.TypeOf c ->
      let c = Desugar.top_computation c in
      let drty_sch, c', new_change = infer_top_comp st c in
      Format.printf "@[- : %t@]@." (Scheme.print_dirty_scheme drty_sch);
      {st with change = new_change}
  | Sugared.Reset ->
      Tctx.reset ();
      print_endline ("Environment reset."); initial_ctxenv
  | Sugared.Help ->
      print_endline help_text;
      st
  | Sugared.DefEffect (eff, (ty1, ty2)) ->
      let ty1 = Desugar.ty Trio.empty ty1
      and ty2 = Desugar.ty Trio.empty ty2 in
      {st with typing = Infer.add_effect st.typing eff (ty1, ty2)}
  | Sugared.Quit -> exit 0
  | Sugared.Use fn -> use_file st (fn, interactive)
  | Sugared.TopLet defs ->
      let defs = Desugar.top_let defs in
      (* XXX What to do about the dirts? *)
      let vars, nonpoly, change = Infer.infer_let ~loc st.typing defs in
      let typing_env = List.fold_right (fun (x, ty_sch) env -> Infer.add_def env x ty_sch) vars st.typing in
      let extend_nonpoly (x, ty) env =
        (x, ([(x, ty)], ty, Constraints.empty)) :: env
      in
      let vars = List.fold_right extend_nonpoly nonpoly vars in
      let top_change = Common.compose st.change change in
      let sch_change (ctx, ty, cnstrs) =
        let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
        (ctx, ty, cnstrs)
      in
      let defs', poly_tyschs = Infer.type_let_defs ~loc st.typing defs in
      List.iter (fun (p, c) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs' st.environment
      in
        if interactive then begin
          List.iter (fun (x, tysch) ->
                       match RuntimeEnv.lookup x env with
                         | None -> assert false
                         | Some v ->
                         Format.printf "@[val %t : %t = %t@]@." (Untyped.Variable.print x) (Scheme.print_ty_scheme (sch_change tysch)) (Value.print_value v))
            vars
        end;
        {
          typing = typing_env;
          change = top_change;
          environment = env;
        }
    | Sugared.TopLetRec defs ->
        let defs = Desugar.top_let_rec defs in
        let vars, _, change = Infer.infer_let_rec ~loc st.typing defs in
        let defs', poly_tyschs = Infer.type_let_rec_defs ~loc st.typing defs in
        let typing_env = List.fold_right (fun (x, ty_sch) env -> Infer.add_def env x ty_sch) vars st.typing in
        let top_change = Common.compose st.change change in
        let sch_change (ctx, ty, cnstrs) =
          let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
          (ctx, ty, cnstrs)
        in
        List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
        let env = Eval.extend_let_rec st.environment defs' in
          if interactive then begin
            List.iter (fun (x, tysch) -> Format.printf "@[val %t : %t = <fun>@]@." (Untyped.Variable.print x) (Scheme.print_ty_scheme (sch_change tysch))) vars
          end;
        {
          typing = typing_env;
          change = top_change;
          environment = env;
        }
    | Sugared.External (x, t, f) ->
      let x, ty_sch = Desugar.external_ty x t in
      let typing_env = Infer.add_def st.typing x ty_sch in
        begin match Common.lookup f External.values with
          | Some v -> {
              typing = typing_env;
              change = st.change;
              environment = RuntimeEnv.update x v st.environment;
            }
          | None -> Error.runtime "unknown external symbol %s." f
        end
    | Sugared.Tydef tydefs ->
        let tydefs = Desugar.tydefs ~loc tydefs in
        Tctx.extend_tydefs ~loc tydefs ;
        st


and use_file env (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
    List.fold_left (exec_cmd interactive) env cmds

and optimize_file st filename =
  let t = Lexer.read_file (parse Parser.computation_file) filename in
  let c = Desugar.top_computation t in
  let drty_sch, c', new_change = infer_top_comp st c in
  Typed.printC c' stdout;
  print_endline "UNOPTIMIZED CODE:";
  Typed.printC c' stdout;
  print_endline "OPTIMIZED CODE:";
  Typed.printC (Optimize.optimize_comp c') stdout;
  (* Format.printf "OPTIMIZED CODE:@.@[val %t : %t = <fun>@]@." (Typed.print_computation c'); *)
(*   let r = Eval.run st.environment c' in
  begin match r with
  | Runtime.Value v -> print_endline (Runtime.string_of_value v)
  | Runtime.Call (eff, v, _) -> print_endline ("Uncaught effect " ^ (Syntax.Effect.string_of eff) ^ " " ^ Runtime.string_of_value v)
  end
 *)
  ()

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
    let ctxenv = List.fold_left use_file initial_ctxenv !files in
    List.iter (optimize_file ctxenv) !to_be_optimized;
    if !Config.interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Error.print err; exit 1
