type eff_state = (TypingEnv.t * (Scheme.dirty_scheme -> Scheme.dirty_scheme)) * RuntimeEnv.t

let help_text = "Toplevel commands:
#type <expr>;;     print the type of <expr> without evaluating it
#reset;;           forget all definitions (including pervasives)
#help;;            print this help
#quit;;            exit eff
#use \"<file>\";;  load commands from file";;

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
  typing : Infer.state;
}

let initial_state = {
  environment = RuntimeEnv.empty;
  typing = {
    Infer.context = TypingEnv.empty
  }
}

let print_ty_scheme sch =
  if !Config.smart_print then
    SmartPrint.print_ty_scheme sch
  else
    Scheme.print_ty_scheme sch

let print_dirty_scheme sch =
  if !Config.smart_print then
    SmartPrint.print_dirty_scheme sch
  else
    Scheme.print_dirty_scheme sch

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd ppf interactive st cmd =
  let loc = cmd.Untyped.location in
  let cmd_typed, typing = Infer.type_toplevel ~loc st.typing cmd.Untyped.term in
  let st = {st with typing} in
  match cmd_typed with
  | Typed.Computation c ->
    let v = Eval.run st.environment c in
    if interactive then Format.fprintf ppf "@[- : ? = %t@]@."
        (* (print_dirty_scheme c.Typed.scheme) *)
        (Value.print_value v);
    st
  | Typed.Reset ->
    Tctx.reset ();
    print_endline ("Environment reset."); initial_state
  | Typed.Help ->
    print_endline help_text;
    st
(*   | Typed.DefEffect (eff, (ty1, ty2)) ->
    st
 *)  | Typed.Quit -> exit 0
  | Typed.Use fn -> use_file ppf st (fn, interactive)
(*   | Typed.TopLet (defs, vars) ->
    let env =
      List.fold_right
        (fun (p, c) env -> let v = Eval.run env c in Eval.extend p v env)
        defs st.environment
    in
    if interactive then begin
      List.iter (fun (x, tysch) ->
          match RuntimeEnv.lookup x env with
          | None -> assert false
          | Some v ->
            Format.fprintf ppf "@[val %t : %t = %t@]@." (Typed.Variable.print x) (print_ty_scheme tysch) (Value.print_value v))
        vars
    end;
    {st with environment = env}
  | Typed.TopLetRec (defs, vars) ->
    let env = Eval.extend_let_rec st.environment defs in
    if interactive then begin
      List.iter (fun (x, tysch) -> Format.fprintf ppf "@[val %t : %t = <fun>@]@." (Typed.Variable.print x) (print_ty_scheme tysch)) vars
    end;
    {
      st with environment = env;
    }
  | Typed.External (x, ty, f) ->
    begin match Common.lookup f External.values with
      | Some v -> {
          st with environment = RuntimeEnv.update x v st.environment;
        }
      | None -> Error.runtime "unknown external symbol %s." f
    end
  | Typed.Tydef tydefs ->
    st
 *)
and use_file ppf env (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
  let cmds = List.map Desugar.toplevel cmds in
  List.fold_left (exec_cmd ppf interactive) env cmds
