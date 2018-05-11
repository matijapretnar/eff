let help_text =
  "Toplevel commands:\n"
  ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
  ^ "#reset;;           forget all definitions (including pervasives)\n"
  ^ "#help;;            print this help\n" ^ "#quit;;            exit eff\n"
  ^ "#use \"<file>\";;  load commands from file\n"


type state =
  {runtime: Eval.state; typing: SimpleInfer.t; desugaring: Desugar.state}

let _ = Random.self_init ()

let initial =
  {runtime= Eval.empty; typing= SimpleInfer.empty; desugaring= Desugar.initial}


(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf st cmd =
  let loc = cmd.CoreSyntax.location in
  match cmd.CoreSyntax.term with
  | CoreSyntax.Computation c ->
      let typing, ty = SimpleInfer.infer_top_comp st.typing c in
      let v = Eval.run st.runtime c in
      Format.fprintf ppf "@[- : %t = %t@]@." (Type.print_beautiful ty)
        (Value.print_value v) ;
      {st with typing}
  | CoreSyntax.TypeOf c ->
      let typing, ty = SimpleInfer.infer_top_comp st.typing c in
      Format.fprintf ppf "@[- : %t@]@." (Type.print_beautiful ty) ;
      {st with typing}
  | CoreSyntax.Reset ->
      Format.fprintf ppf "Environment reset." ;
      Tctx.reset () ;
      initial
  | CoreSyntax.Help ->
      Format.fprintf ppf "%s" help_text ;
      st
  | CoreSyntax.DefEffect (eff, (ty1, ty2)) ->
      let typing = SimpleCtx.add_effect st.typing eff (ty1, ty2) in
      {st with typing}
  | CoreSyntax.Quit -> exit 0
  | CoreSyntax.Use filename -> execute_file ppf filename st
  | CoreSyntax.TopLet defs ->
      let vars, typing = SimpleInfer.infer_top_let ~loc st.typing defs in
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
      {st with typing; runtime}
  | CoreSyntax.TopLetRec defs ->
      let vars, typing = SimpleInfer.infer_top_let_rec ~loc st.typing defs in
      let runtime = Eval.extend_let_rec st.runtime defs in
      List.iter
        (fun (x, tysch) ->
          Format.fprintf ppf "@[val %t : %t = <fun>@]@."
            (CoreSyntax.Variable.print x)
            (Type.print_beautiful tysch) )
        vars ;
      {st with typing; runtime}
  | CoreSyntax.External (x, ty, f) -> (
    match OldUtils.lookup f External.values with
    | Some v ->
        { st with
          typing= SimpleCtx.extend st.typing x (Type.free_params ty, ty)
        ; runtime= Eval.update x v st.runtime }
    | None -> Error.runtime "unknown external symbol %s." f )
  | CoreSyntax.Tydef tydefs ->
      Tctx.extend_tydefs ~loc tydefs ;
      st

and desugar_and_exec_cmds ppf state cmds =
  let desugar_state', untyped_cmds =
    Desugar.desugar_commands state.desugaring cmds
  in
  let state' = {state with desugaring= desugar_state'} in
  CoreUtils.fold (exec_cmd ppf) state' untyped_cmds

(* Parser wrapper *)
and parse lexbuf =
  try Parser.commands Lexer.token lexbuf with
  | Parser.Error ->
      Error.syntax ~loc:(Location.of_lexeme lexbuf) "parser error"
  | Failure failmsg when failmsg = "lexing: empty token" ->
      Error.syntax ~loc:(Location.of_lexeme lexbuf) "unrecognised symbol."

and execute_file ppf filename env =
  Lexer.read_file parse filename |> desugar_and_exec_cmds ppf env

and execute_source ppf str env =
  Lexer.read_string parse str |> desugar_and_exec_cmds ppf env
