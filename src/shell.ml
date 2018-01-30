let help_text =
  "Toplevel commands:\n"
  ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
  ^ "#reset;;           forget all definitions (including pervasives)\n"
  ^ "#help;;            print this help\n" ^ "#quit;;            exit eff\n"
  ^ "#use \"<file>\";;  load commands from file\n"


type state = {runtime: Eval.state; typing: Infer.t}

let initial_state = {runtime= Eval.empty; typing= Infer.empty}

(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf st cmd =
  let loc = cmd.CoreSyntax.location in
  match cmd.CoreSyntax.term with
  | CoreSyntax.Computation c ->
      let typing, ty = Infer.infer_top_comp st.typing c in
      let v = Eval.run st.runtime c in
      Format.fprintf ppf "@[- : %t = %t@]@." (Type.print_beautiful ty)
        (Value.print_value v) ;
      {st with typing}
  | CoreSyntax.TypeOf c ->
      let typing, ty = Infer.infer_top_comp st.typing c in
      Format.fprintf ppf "@[- : %t@]@." (Type.print_beautiful ty) ;
      {st with typing}
  | CoreSyntax.Reset ->
      Format.fprintf ppf "Environment reset." ;
      Tctx.reset () ;
      initial_state
  | CoreSyntax.Help ->
      Format.fprintf ppf "%s" help_text ;
      st
  | CoreSyntax.DefEffect (eff, (ty1, ty2)) ->
      let typing = Ctx.add_effect st.typing eff (ty1, ty2) in
      {st with typing}
  | CoreSyntax.Quit -> exit 0
  | CoreSyntax.Use fn -> use_file ppf fn st
  | CoreSyntax.TopLet defs ->
      let vars, typing = Infer.infer_top_let ~loc st.typing defs in
      let runtime =
        List.fold_right
          (fun (p, c) env ->
            let v = Eval.run env c in
            Eval.extend p v env )
          defs st.runtime
      in
      List.iter
        (fun (x, tysch) ->
          match Eval.lookup x runtime with
          | None -> assert false
          | Some v ->
              Format.fprintf ppf "@[val %t : %t = %t@]@."
                (CoreSyntax.Variable.print x)
                (Type.print_beautiful tysch)
                (Value.print_value v) )
        vars ;
      {typing; runtime}
  | CoreSyntax.TopLetRec defs ->
      let vars, typing = Infer.infer_top_let_rec ~loc st.typing defs in
      let runtime = Eval.extend_let_rec st.runtime defs in
      List.iter
        (fun (x, tysch) ->
          Format.fprintf ppf "@[val %t : %t = <fun>@]@."
            (CoreSyntax.Variable.print x)
            (Type.print_beautiful tysch) )
        vars ;
      {typing; runtime}
  | CoreSyntax.External (x, ty, f) -> (
    match OldUtils.lookup f External.values with
    | Some v ->
        { typing= Ctx.extend st.typing x (Type.free_params ty, ty)
        ; runtime= Eval.update x v st.runtime }
    | None -> Error.runtime "unknown external symbol %s." f )
  | CoreSyntax.Tydef tydefs ->
      Tctx.extend_tydefs ~loc tydefs ;
      st

and desugar_and_exec_cmds ppf env cmds =
  cmds |> List.map Desugar.toplevel |> List.fold_left (exec_cmd ppf) env

(* Parser wrapper *)
and parse lex =
  try Parser.commands Lexer.token lex with
  | Parser.Error -> Error.syntax ~loc:(Location.of_lexeme lex) "parser error"
  | Failure failmsg when failmsg = "lexing: empty token" ->
      Error.syntax ~loc:(Location.of_lexeme lex) "unrecognised symbol."

and use_file ppf filename env =
  Lexer.read_file parse filename |> desugar_and_exec_cmds ppf env

and use_textfile ppf str env =
  Lexer.read_string parse str |> desugar_and_exec_cmds ppf env

and use_toplevel ppf env =
  Lexer.read_toplevel parse () |> desugar_and_exec_cmds ppf env
