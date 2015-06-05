module C = Common

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
let add_file interactive filename = (files := (filename, interactive) :: !files)

(* Command-line options *)
let options = Arg.align [
  ("--pervasives",
   Arg.String (fun str -> Config.pervasives_file := Config.PervasivesFile str),
   " Specify the pervasives.eff file");
  ("--effects",
   Arg.Set Config.effect_annotations,
   " Show the output of effect inference");
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
  environment : Eval.env;
  context : Ctx.t;
  change : Scheme.dirty_scheme -> Scheme.dirty_scheme;
  effects : (Type.ty * Type.ty) Syntax.EffectMap.t
}

let initial_ctxenv = {
  environment = Eval.initial;
  context = Ctx.empty;
  change = Common.id;
  effects = Syntax.EffectMap.empty;
}

let create_infer_state st = {
  Infer.context = st.context;
  Infer.effects = st.effects;
}

let infer_top_comp st c =
  let ctx', (ty', drt'), cnstrs' = Infer.infer_comp (create_infer_state st) c in
  let change = Scheme.add_to_top ~loc:c.Syntax.location ctx' cnstrs' in
  let top_change = Common.compose st.change change in
  let ctx = match c.Syntax.term with
  | Syntax.Value _ -> ctx'
  | _ -> (Desugar.fresh_variable (), ty') :: ctx'
  in
  let drty_sch = top_change (ctx, (ty', drt'), cnstrs') in

  Exhaust.check_comp c;
  drty_sch, top_change

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd interactive st (d,loc) =
  match d with
  | SugaredSyntax.Term c ->
      let c = Desugar.top_computation c in
      let drty_sch, new_change = infer_top_comp st c in
      let v = Eval.run st.environment c in
      if interactive then Format.printf "@[- : %t = %t@]@."
        (Scheme.print_dirty_scheme drty_sch)
        (Value.print_value v);
      {st with change = new_change}
  | SugaredSyntax.TypeOf c ->
      let c = Desugar.top_computation c in
      let drty_sch, new_change = infer_top_comp st c in
      Format.printf "@[- : %t@]@." (Scheme.print_dirty_scheme drty_sch);
      {st with change = new_change}
  | SugaredSyntax.Reset ->
      Tctx.reset ();
      print_endline ("Environment reset."); initial_ctxenv
  | SugaredSyntax.Help ->
      print_endline help_text;
      st
  | SugaredSyntax.DefEffect (eff, (ty1, ty2)) ->
      let ty1 = Desugar.ty Trio.empty ty1
      and ty2 = Desugar.ty Trio.empty ty2 in
      {st with effects = Syntax.EffectMap.add eff (ty1, ty2) st.effects}
  | SugaredSyntax.Quit -> exit 0
  | SugaredSyntax.Use fn -> use_file st (fn, interactive)
  | SugaredSyntax.TopLet defs ->
      let defs = Desugar.top_let defs in
      (* XXX What to do about the dirts? *)
      let vars, nonpoly, change = Infer.infer_let ~loc (create_infer_state st) defs in
      let ctx = List.fold_right (fun (x, ty_sch) env -> Ctx.extend env x ty_sch) vars st.context in
      let extend_nonpoly (x, ty) env =
        (x, ([(x, ty)], ty, Constraints.empty)) :: env
      in
      let vars = List.fold_right extend_nonpoly nonpoly vars in
      let top_change = Common.compose st.change change in
      let sch_change (ctx, ty, cnstrs) =
        let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
        (ctx, ty, cnstrs)
      in
      List.iter (fun (p, c) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs st.environment
      in
        if interactive then begin
          List.iter (fun (x, tysch) ->
                       match Eval.lookup x env with
                         | None -> assert false
                         | Some v ->
                         Format.printf "@[val %t : %t = %t@]@." (Syntax.print_variable x) (Scheme.print_ty_scheme (sch_change tysch)) (Value.print_value v))
            vars
        end;
        {
          st with
          context = ctx;
          change = top_change;
          environment = env;
        }
    | SugaredSyntax.TopLetRec defs ->
        let defs = Desugar.top_let_rec defs in
        let vars, change = Infer.infer_let_rec ~loc (create_infer_state st) defs in
        let ctx = List.fold_right (fun (x, ty_sch) ctx -> Ctx.extend ctx x ty_sch) vars st.context in
        let top_change = Common.compose st.change change in
        let sch_change (ctx, ty, cnstrs) =
          let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
          (ctx, ty, cnstrs)
        in
        List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
        let env = Eval.extend_let_rec st.environment defs in
          if interactive then begin
            List.iter (fun (x, tysch) -> Format.printf "@[val %t : %t = <fun>@]@." (Syntax.print_variable x) (Scheme.print_ty_scheme (sch_change tysch))) vars
          end;
        {
          st with
          context = ctx;
          change = top_change;
          environment = env;
        }
    | SugaredSyntax.External (x, t, f) ->
      let (x, t) = Desugar.external_ty x t in
      let ctx = Ctx.extend st.context x t in
        begin match C.lookup f External.values with
          | Some v -> {
              st with
              context = ctx;
              change = st.change;
              environment = Eval.update x v st.environment;
            }
          | None -> Error.runtime "unknown external symbol %s." f
        end
    | SugaredSyntax.Tydef tydefs ->
        let tydefs = Desugar.tydefs ~loc tydefs in
        Tctx.extend_tydefs ~loc tydefs ;
        st


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
    if !Config.interactive_shell then toplevel ctxenv
  with
    Error.Error err -> Error.print err; exit 1
