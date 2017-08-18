type eff_state = (TypingEnv.t * (Scheme.dirty_scheme -> Scheme.dirty_scheme)) * RuntimeEnv.t

let help_text = "Toplevel commands:
#type <expr>;;     print the type of <expr> without evaluating it
#reset;;           forget all definitions (including pervasives)
#help;;            print this help
#quit;;            exit eff
#use \"<file>\";;  load commands from file";;

type state = {
  environment : RuntimeEnv.t;
  change : Scheme.dirty_scheme -> Scheme.dirty_scheme;
  typing : Infer.state;
}

let initial_state = {
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
let rec exec_cmd ppf interactive st d =
  let loc = d.Untyped.location in
  match d.Untyped.term with
  | Untyped.Computation c ->
      let drty_sch, c', new_change = infer_top_comp st c in
      let v = Eval.run st.environment c' in
      if interactive then Format.fprintf ppf "@[- : %t = %t@]@."
        (print_dirty_scheme drty_sch)
        (Value.print_value v);
      {st with change = new_change}
  | Untyped.TypeOf c ->
      let drty_sch, c', new_change = infer_top_comp st c in
      Format.fprintf ppf "@[- : %t@]@." (print_dirty_scheme drty_sch);
      {st with change = new_change}
  | Untyped.Reset ->
      Tctx.reset ();
      Format.fprintf ppf "Environment reset.";
      initial_state
  | Untyped.Help ->
      Format.fprintf ppf "%s" help_text;
      st
  | Untyped.DefEffect (eff, (ty1, ty2)) ->
      {st with typing = Infer.add_effect st.typing eff (ty1, ty2)}
  | Untyped.Quit -> exit 0
  | Untyped.Use fn -> use_file ppf st (fn, interactive)
  | Untyped.TopLet defs ->
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
                         Format.fprintf ppf "@[val %t : %t = %t@]@." (Untyped.Variable.print x) (print_ty_scheme (sch_change tysch)) (Value.print_value v))
            vars
        end;
        {
          typing = typing_env;
          change = top_change;
          environment = env;
        }
    | Untyped.TopLetRec defs ->
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
            List.iter (fun (x, tysch) -> Format.fprintf ppf "@[val %t : %t = <fun>@]@." (Untyped.Variable.print x) (print_ty_scheme (sch_change tysch))) vars
          end;
        {
          typing = typing_env;
          change = top_change;
          environment = env;
        }
    | Untyped.External (x, ty, f) ->
      let typing_env = Infer.add_def st.typing x ([], ty, Constraints.empty) in
        begin match Common.lookup f External.values with
          | Some v -> {
              typing = typing_env;
              change = st.change;
              environment = RuntimeEnv.update x v st.environment;
            }
          | None -> Error.runtime "unknown external symbol %s." f
        end
    | Untyped.Tydef tydefs ->
        Tctx.extend_tydefs ~loc tydefs ;
        st

and desugar_and_exec_cmds ppf interactive env cmds =
  let cmds = List.map Desugar.toplevel cmds in
    List.fold_left (exec_cmd ppf interactive) env cmds

(* Parser wrapper *)
and parse lex =
  try
    Parser.commands Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~loc:(Location.of_lexeme lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~loc:(Location.of_lexeme lex) "unrecognised symbol."

and use_file ppf env (filename, interactive) =
  Lexer.read_file parse filename
  |> desugar_and_exec_cmds ppf interactive env

and use_textfile ppf env str =
  Lexer.read_string parse str
  |> desugar_and_exec_cmds ppf true env

and use_toplevel ppf env =
  Lexer.read_toplevel parse ()
  |> desugar_and_exec_cmds ppf true env
