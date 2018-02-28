let help_text =
  "Toplevel commands:\n"
  ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
  ^ "#reset;;           forget all definitions (including pervasives)\n"
  ^ "#help;;            print this help\n" ^ "#quit;;            exit eff\n"
  ^ "#use \"<file>\";;  load commands from file\n"


type state =
  { runtime: Eval.state
  ; explicit_typing: ExplicitInfer.state
  ; type_checker: TypeChecker.checker_state
  ; typing: SimpleInfer.t }

let initial_state =
  { runtime= Eval.empty
  ; explicit_typing= ExplicitInfer.empty
  ; type_checker= TypeChecker.new_checker_state
  ; typing= SimpleInfer.empty }


(* [exec_cmd ppf st cmd] executes toplevel command [cmd] in a state [st].
   It prints the result to [ppf] and returns the new state. *)
let rec exec_cmd ppf st cmd =
  let loc = cmd.CoreSyntax.location in
  match cmd.CoreSyntax.term with
  | CoreSyntax.Computation c ->
      if !Config.explicit_subtyping then
        let ct, explicit_typing =
          ExplicitInfer.type_toplevel ~loc:c.CoreSyntax.location
            st.explicit_typing c
        in
        let ty, drt =
          TypeChecker.type_check_comp st.type_checker ct.Typed.term
        in
        let v = Eval.run st.runtime c in
        Format.fprintf ppf "@[- : %t ! %t = %t@]@." (Types.print_target_ty ty)
          (Types.print_target_dirt drt)
          (Value.print_value v) ;
        {st with explicit_typing}
      else
        let typing, ty = SimpleInfer.infer_top_comp st.typing c in
        let v = Eval.run st.runtime c in
        Format.fprintf ppf "@[- : %t = %t@]@." (Type.print_beautiful ty)
          (Value.print_value v) ;
        {st with typing}
  | CoreSyntax.TypeOf c ->
      if !Config.explicit_subtyping then
        let ct, explicit_typing =
          ExplicitInfer.type_toplevel ~loc:c.CoreSyntax.location
            st.explicit_typing c
        in
        let ty, drt =
          TypeChecker.type_check_comp st.type_checker ct.Typed.term
        in
        Format.fprintf ppf "@[- : %t ! %t@]@." (Types.print_target_ty ty)
          (Types.print_target_dirt drt) ;
        {st with explicit_typing}
      else
        let typing, ty = SimpleInfer.infer_top_comp st.typing c in
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
      if !Config.explicit_subtyping then
        let explicit_typing =
          ExplicitInfer.add_effect eff (ty1, ty2) st.explicit_typing
        in
        {st with explicit_typing}
      else
        let typing = SimpleCtx.add_effect st.typing eff (ty1, ty2) in
        {st with typing}
  | CoreSyntax.Quit -> exit 0
  | CoreSyntax.Use fn -> use_file ppf fn st
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
        let new_ty = ExplicitInfer.source_to_target ty in
        { st with
          typing= SimpleCtx.extend st.typing x (Type.free_params ty, ty)
        ; explicit_typing=
            { st.explicit_typing with
              ExplicitInfer.context=
                TypingEnv.update st.explicit_typing.context x new_ty }
        ; type_checker=
            TypeChecker.extend_state_term_vars st.type_checker x new_ty
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


let compile_file ppf filename st =
  let out_channel = open_out (filename ^ ".ml") in
  let out_ppf = Format.formatter_of_out_channel out_channel in
  (* look for header.ml next to the executable  *)
  let header_file =
    Filename.concat (Filename.dirname Sys.argv.(0)) "header.ml"
  in
  let header_channel = open_in header_file in
  let n = in_channel_length header_channel in
  let header = really_input_string header_channel n in
  close_in header_channel ;
  Format.fprintf out_ppf "%s\n;;\n@." header ;
  let compile_cmd st cmd =
    let loc = cmd.CoreSyntax.location in
    match cmd.CoreSyntax.term with
    | CoreSyntax.Computation c ->
        Print.debug "Compiling: %t" (CoreSyntax.print_computation c);
        let ct, explicit_typing =
          ExplicitInfer.type_toplevel ~loc st.explicit_typing c
        in
        Print.debug "-- After Type Inference ----------------------------------------";
        Print.debug "%t" (Typed.print_computation ct);
        let ct =
          if !Config.disable_optimization then ct
          else Optimize.optimize_main_comp st.type_checker ct
        in
        Print.debug "-- After Optimization ------------------------------------------";
        Print.debug "%t" (Typed.print_computation ct);
        let ct_ty, ct_dirt = TypeChecker.type_check_comp st.type_checker ct.term in
        Print.debug "Type from Type Checker : %t ! %t" (Types.print_target_ty ct_ty) (Types.print_target_dirt ct_dirt) ;
 
        let erasure_ct = Erasure.typed_to_erasure_comp [] ct in
        NewPrint.print_computation erasure_ct out_ppf ;
        Format.fprintf out_ppf "\n;;\n " ;
        print_endline "ended found something!" ;
        {st with explicit_typing}
    | CoreSyntax.DefEffect (eff, (ty1, ty2)) ->
        let explicit_typing =
          ExplicitInfer.add_effect eff (ty1, ty2) st.explicit_typing
        in
        Print.print out_ppf
          "type (_, _) effect += Effect_%s : (int, int) effect" eff ;
        Format.fprintf out_ppf "\n;;\n " ;
        {st with explicit_typing}
    | CoreSyntax.External (x, ty, f) -> (
      match OldUtils.lookup f External.values with
      | Some v ->
          let new_ty = ExplicitInfer.source_to_target ty in
          Print.print out_ppf
            "let %t = ( %s )" (NewPrint.print_variable x) f ;
          Format.fprintf out_ppf "\n;;\n " ;
          { st with
            typing= SimpleCtx.extend st.typing x (Type.free_params ty, ty)
          ; explicit_typing=
              { st.explicit_typing with
                ExplicitInfer.context=
                  TypingEnv.update st.explicit_typing.context x new_ty }
          ; type_checker=
              TypeChecker.extend_state_term_vars st.type_checker x new_ty
          ; runtime= Eval.update x v st.runtime }
      | None -> Error.runtime "unknown external symbol %s." f )
    | _ -> st
  in
  let cmds = Lexer.read_file parse filename |> List.map Desugar.toplevel in
  let st = List.fold_left compile_cmd st cmds in
  Format.fprintf out_ppf "@? " ;
  flush out_channel ;
  close_out out_channel ;
  st
