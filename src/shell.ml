let help_text = "Toplevel commands:
#type <expr>;;     print the type of <expr> without evaluating it
#reset;;           forget all definitions (including pervasives)
#help;;            print this help
#quit;;            exit eff
#use \"<file>\";;  load commands from file
";;

type state = {
  runtime : Eval.state;
  typing : Infer.state;
}

let initial_state = {
  runtime = Eval.empty;
  typing = {
    Infer.context = TypingEnv.empty;
    Infer.effects = CoreSyntax.EffectMap.empty
  }
}


(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf st cmd =
  let loc = cmd.CoreSyntax.location
  and print_ty_scheme _ ppf =
    Format.fprintf ppf "ty_scheme"
  and print_dirty_scheme _ ppf =
    Format.fprintf ppf "dirty_scheme"
  in
  match cmd.CoreSyntax.term with
  | CoreSyntax.Computation c ->
      let drty_sch = () in
      let v = Eval.run st.runtime c in
      Format.fprintf ppf "@[- : %t = %t@]@."
        (print_dirty_scheme drty_sch)
        (Value.print_value v);
      st
  | CoreSyntax.TypeOf c ->
      let drty_sch = () in
      Format.fprintf ppf "@[- : %t@]@."
        (print_dirty_scheme drty_sch);
      st
  | CoreSyntax.Reset ->
      Format.fprintf ppf "Environment reset.";
      Tctx.reset ();
      initial_state
  | CoreSyntax.Help ->
      Format.fprintf ppf "%s" help_text;
      st
  | CoreSyntax.DefEffect (eff, (ty1, ty2)) ->
     (* Add typing *)
      let typing = st.typing in
      { st with typing }
  | CoreSyntax.Quit ->
      exit 0
  | CoreSyntax.Use fn ->
      use_file ppf fn st
(*   | CoreSyntax.TopLet defs ->
      let defs', vars, typing = Infer.infer_top_let ~loc st.typing defs in
      let runtime =
        List.fold_right
          (fun (p, c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs st.runtime
      in
      List.iter (fun (x, tysch) ->
        match Eval.lookup x runtime with
          | None -> assert false
          | Some v ->
            Format.fprintf ppf "@[val %t : %t = %t@]@."
              (CoreSyntax.Variable.print x)
              (print_ty_scheme tysch)
              (Value.print_value v)
      ) vars;
      { typing; runtime }
    | CoreSyntax.TopLetRec defs ->
        let defs', vars, typing = Infer.infer_top_let_rec ~loc st.typing defs in
        let runtime = Eval.extend_let_rec st.runtime defs in
        List.iter (fun (x, tysch) ->
          Format.fprintf ppf "@[val %t : %t = <fun>@]@."
            (CoreSyntax.Variable.print x)
            (print_ty_scheme tysch)
        ) vars;
        { typing; runtime }
    | CoreSyntax.External (x, ty, f) ->
        begin match OldUtils.lookup f External.values with
        | Some v -> {
            typing = Infer.add_top_def st.typing x ty;
            runtime = Eval.update x v st.runtime;
          }
        | None -> Error.runtime "unknown external symbol %s." f
        end
    | CoreSyntax.Tydef tydefs ->
        Tctx.extend_tydefs ~loc tydefs;
        st *)

and desugar_and_exec_cmds ppf env cmds =
  cmds
  |> List.map Desugar.toplevel
  |> List.fold_left (exec_cmd ppf) env

(* Parser wrapper *)
and parse lex =
  try
    Parser.commands Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~loc:(Location.of_lexeme lex) "parser error"
  | Failure failmsg when failmsg = "lexing: empty token" ->
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

let compile_file ppf filename st =
  let out_channel = open_out (filename ^ ".ml") in
  let out_ppf = Format.formatter_of_out_channel out_channel in

  let compile_cmd st cmd =
    let loc = cmd.CoreSyntax.location in
    let cmd_typed, typing = Infer.type_toplevel ~loc st.typing cmd.CoreSyntax.term in
    let st = {st with typing} in
    match cmd_typed with
    | Typed.Computation c ->
        print_endline "found something!";
        SimplePrint.print_computation c out_ppf;
        Format.fprintf out_ppf "\n;;\n ";
        print_endline "ended found something!";
        st
    | _ -> st
  in

  let cmds = Lexer.read_file parse filename |> List.map Desugar.toplevel in
  let st = List.fold_left compile_cmd st cmds in
    Format.fprintf out_ppf "@? ";
  flush out_channel;
  close_out out_channel;
  st


