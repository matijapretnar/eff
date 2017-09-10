let help_text = "Toplevel commands:
#type <expr>;;     print the type of <expr> without evaluating it
#reset;;           forget all definitions (including pervasives)
#help;;            print this help
#quit;;            exit eff
#use \"<file>\";;  load commands from file";;

type state = {
  environment : RuntimeEnv.t;
  typing : Infer.t;
}

let initial_state = {
  environment = RuntimeEnv.empty;
  typing = Infer.empty;
}

let print_ty_scheme =
  if !Config.smart_print then
    SmartPrint.print_ty_scheme
  else
    Scheme.print_ty_scheme

let print_dirty_scheme =
  if !Config.smart_print then
    SmartPrint.print_dirty_scheme
  else
    Scheme.print_dirty_scheme

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd ppf st d =
  let loc = d.Untyped.location in
  match d.Untyped.term with
  | Untyped.Computation c ->
      let drty_sch, c', typing = Infer.infer_top_comp st.typing c in
      let v = Eval.run st.environment c' in
      Format.fprintf ppf "@[- : %t = %t@]@."
        (print_dirty_scheme drty_sch)
        (Value.print_value v);
      {st with typing}
  | Untyped.TypeOf c ->
      let drty_sch, c', typing = Infer.infer_top_comp st.typing c in
      Format.fprintf ppf "@[- : %t@]@." (print_dirty_scheme drty_sch);
      {st with typing}
  | Untyped.Reset ->
      Tctx.reset ();
      Format.fprintf ppf "Environment reset.";
      initial_state
  | Untyped.Help ->
      Format.fprintf ppf "%s" help_text;
      st
  | Untyped.DefEffect (eff, (ty1, ty2)) ->
      {st with typing = Infer.add_top_effect st.typing eff (ty1, ty2)}
  | Untyped.Quit -> exit 0
  | Untyped.Use fn -> use_file ppf fn st
  | Untyped.TopLet defs ->
      let defs', vars, typing = Infer.infer_top_let ~loc st.typing defs in
      let environment =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs' st.environment
      in
          List.iter (fun (x, tysch) ->
                       match RuntimeEnv.lookup x environment with
                         | None -> assert false
                         | Some v ->
                         Format.fprintf ppf "@[val %t : %t = %t@]@." (Untyped.Variable.print x) (print_ty_scheme tysch) (Value.print_value v))
            vars;
        { typing; environment }
    | Untyped.TopLetRec defs ->
        let defs', vars, typing = Infer.infer_top_let_rec ~loc st.typing defs in
        let environment = Eval.extend_let_rec st.environment defs' in
        List.iter (fun (x, tysch) -> Format.fprintf ppf "@[val %t : %t = <fun>@]@." (Untyped.Variable.print x) (print_ty_scheme tysch)) vars;
        { typing; environment }
    | Untyped.External (x, ty, f) ->
        begin match Common.lookup f External.values with
          | Some v ->
              {
                typing = Infer.add_top_def st.typing x ty;
                environment = RuntimeEnv.update x v st.environment;
              }
          | None -> Error.runtime "unknown external symbol %s." f
        end
    | Untyped.Tydef tydefs ->
        Tctx.extend_tydefs ~loc tydefs ;
        st

and desugar_and_exec_cmds ppf env cmds =
  let cmds = List.map Desugar.toplevel cmds in
    List.fold_left (exec_cmd ppf) env cmds

(* Parser wrapper *)
and parse lex =
  try
    Parser.commands Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~loc:(Location.of_lexeme lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~loc:(Location.of_lexeme lex) "unrecognised symbol."

and use_file ppf filename env =
  Lexer.read_file parse filename
  |> desugar_and_exec_cmds ppf env

and use_textfile ppf str env =
  Lexer.read_string parse str
  |> desugar_and_exec_cmds ppf env

and use_toplevel ppf env =
  Lexer.read_toplevel parse ()
  |> desugar_and_exec_cmds ppf env
