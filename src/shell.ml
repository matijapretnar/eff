let help_text =
  "Toplevel commands:\n"
  ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
  ^ "#reset;;           forget all definitions (including pervasives)\n"
  ^ "#help;;            print this help\n" ^ "#quit;;            exit eff\n"
  ^ "#use \"<file>\";;  load commands from file\n"


module TypeChecker = SimpleInfer
module Runtime = Eval

type state =
  { desugarer_state: Desugarer.state
  ; typechecker_state: TypeChecker.state
  ; runtime_state: Runtime.state }

let initial_state =
  { desugarer_state= Desugarer.initial_state
  ; typechecker_state= TypeChecker.initial_state
  ; runtime_state= Runtime.initial_state }


let _ = Random.self_init ()

(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf st cmd =
  let loc = cmd.CoreSyntax.location in
  match cmd.CoreSyntax.term with
  | CoreSyntax.Computation c ->
      let typechecker_state, ty =
        TypeChecker.infer_top_comp st.typechecker_state c
      in
      let v = Runtime.run st.runtime_state c in
      Format.fprintf ppf "@[- : %t = %t@]@." (Type.print_beautiful ty)
        (Value.print_value v) ;
      {st with typechecker_state}
  | CoreSyntax.TypeOf c ->
      let typechecker_state, ty =
        TypeChecker.infer_top_comp st.typechecker_state c
      in
      Format.fprintf ppf "@[- : %t@]@." (Type.print_beautiful ty) ;
      {st with typechecker_state}
  | CoreSyntax.Reset ->
      Format.fprintf ppf "Environment reset." ;
      Tctx.reset () ;
      initial_state
  | CoreSyntax.Help ->
      Format.fprintf ppf "%s" help_text ;
      st
  | CoreSyntax.DefEffect (eff, (ty1, ty2)) ->
      let typechecker_state =
        SimpleCtx.add_effect st.typechecker_state eff (ty1, ty2)
      in
      {st with typechecker_state}
  | CoreSyntax.Quit -> exit 0
  | CoreSyntax.Use filename -> execute_file ppf filename st
  | CoreSyntax.TopLet defs ->
      let vars, typechecker_state =
        TypeChecker.infer_top_let ~loc st.typechecker_state defs
      in
      let runtime_state =
        List.fold_right
          (fun (p, c) env ->
            let v = Runtime.run env c in
            Runtime.extend p v env )
          defs st.runtime_state
      in
      List.iter
        (fun (x, tysch) ->
          match Runtime.lookup x runtime_state with
          | None -> assert false
          | Some v ->
              Format.fprintf ppf "@[val %t : %t = %t@]@."
                (CoreSyntax.Variable.print x)
                (Type.print_beautiful tysch)
                (Value.print_value v) )
        vars ;
      {st with typechecker_state; runtime_state}
  | CoreSyntax.TopLetRec defs ->
      let vars, typechecker_state =
        TypeChecker.infer_top_let_rec ~loc st.typechecker_state defs
      in
      let runtime_state = Runtime.extend_let_rec st.runtime_state defs in
      List.iter
        (fun (x, tysch) ->
          Format.fprintf ppf "@[val %t : %t = <fun>@]@."
            (CoreSyntax.Variable.print x)
            (Type.print_beautiful tysch) )
        vars ;
      {st with typechecker_state; runtime_state}
  | CoreSyntax.External (x, ty, f) -> (
    match OldUtils.lookup f External.values with
    | Some v ->
        { st with
          typechecker_state=
            SimpleCtx.extend st.typechecker_state x (Type.free_params ty, ty)
        ; runtime_state= Runtime.update x v st.runtime_state }
    | None -> Error.runtime "unknown external symbol %s." f )
  | CoreSyntax.Tydef tydefs ->
      Tctx.extend_tydefs ~loc tydefs ;
      st

and desugar_and_exec_cmds ppf state cmds =
  let desugarer_state', untyped_cmds =
    Desugarer.desugar_commands state.desugarer_state cmds
  in
  let state' = {state with desugarer_state= desugarer_state'} in
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
