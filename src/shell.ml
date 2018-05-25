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
    Infer.effects = Untyped.EffectMap.empty
  }
}

(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf st cmd =
  let loc = cmd.Untyped.location in
  
  match cmd.Untyped.term with
  | Untyped.Computation c ->
      (* PrintUntyped.print_computation c ppf; *)
      let ct, typing = Infer.type_comp st.typing c in
      (* let ct = Optimize.optimize_command ct in *)
      Format.fprintf ppf "@[- : %t@]@." (Scheme.print_dirty_scheme ct.Typed.scheme);
      (* let v = Eval.run st.runtime c in
      Format.fprintf ppf "@[- : %t = %t@]@."
        (Scheme.print_dirty_scheme ct.Typed.scheme)
        (Value.print_value v); *)
      st
  | Untyped.TypeOf c ->
      let c, _ = Infer.type_comp st.typing c in
      Format.fprintf ppf "@[- : %t@]@."
        (Scheme.print_dirty_scheme c.Typed.scheme);
      st
  | Untyped.Reset ->
      Format.fprintf ppf "Environment reset.";
      Tctx.reset ();
      initial_state
  | Untyped.Help ->
      Format.fprintf ppf "%s" help_text;
      st
  | Untyped.DefEffect (eff, (ty1, ty2)) ->
      let typing = Infer.add_effect st.typing eff (ty1, ty2) in
      { st with typing }
  | Untyped.Quit ->
      exit 0
  | Untyped.Use fn ->
      use_file ppf fn st
  | Untyped.External (x, ty, f) ->
    begin match OldUtils.lookup f External.values with
      | Some v -> {
          typing = Infer.add_def st.typing x (Scheme.simple ty);
          runtime = Eval.update x v st.runtime;
        }
      | None -> Error.runtime "unknown external symbol %s." f
    end
  | Untyped.Tydef tydefs ->
    Tctx.extend_tydefs ~loc tydefs;
    st 
  | Untyped.TopLet defs ->
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
            (Untyped.Variable.print x)
            (Scheme.print_ty_scheme tysch)
            (Value.print_value v)
    ) vars;
    { typing; runtime }
  | Untyped.TopLetRec defs ->
    let _, vars, typing = Infer.infer_top_let_rec ~loc st.typing defs in
    let runtime = Eval.extend_let_rec st.runtime defs in
    List.iter (fun (x, tysch) ->
      Format.fprintf ppf "@[val %t : %t = <fun>@]@."
        (Untyped.Variable.print x)
        (Scheme.print_ty_scheme tysch)
    ) vars;
    { typing; runtime }

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
    let loc = cmd.Untyped.location in
    match cmd.Untyped.term with
    | Untyped.Computation c ->
        let ct, typing = Infer.type_comp st.typing c in
        print_endline "found something!";
        SimplePrint.print_computation ct out_ppf;
        Format.fprintf out_ppf "\n;;\n ";
        print_endline "ended found something!";
        {st with typing}
    | Untyped.DefEffect (eff, (ty1, ty2)) ->
        let typing = Infer.add_effect st.typing eff (ty1, ty2) in
        { st with typing }
    | _ -> st
  in

  let cmds = Lexer.read_file parse filename |> List.map Desugar.toplevel in
  let st = List.fold_left compile_cmd st cmds in
    Format.fprintf out_ppf "@? ";
  flush out_channel;
  close_out out_channel;
  st
