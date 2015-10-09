type eff_state = (Ctx.t * (Scheme.dirty_scheme -> Scheme.dirty_scheme)) * Eval.env

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

let initial_state =
  ((Ctx.empty, Common.id), Eval.initial)

let infer_top_comp (ctx, top_change) c =
  let ctx', (ty', drt'), cnstrs' = Infer.infer_comp ctx c in
  let change = Scheme.add_to_top ~loc:(snd c) ctx' cnstrs' in
  let top_change = Common.compose top_change change in
  let ctx = match fst c with
  | Syntax.Value _ -> ctx'
  | _ -> (Desugar.fresh_variable (), ty') :: ctx'
  in
  let drty_sch = top_change (ctx, (ty', drt'), cnstrs') in

  Exhaust.check_comp c;
  drty_sch, top_change

(* [exec_cmd env c] executes toplevel command [c] in global
    environment [(ctx, env)]. It prints the result on standard output
    and return the new environment. *)
let rec exec_cmd interactive ((ctx, top_change) as wholectx, env) (d,loc) =
  match d with
  | SugaredSyntax.Term c ->
      let c = Desugar.top_computation c in
      let drty_sch, top_change = infer_top_comp wholectx c in
      let v = Eval.run env c in
      if interactive then Format.printf "@[- : %t = %t@]@."
        (Scheme.print_dirty_scheme drty_sch)
        (Value.print_value v);
      ((ctx, top_change), env)
  | SugaredSyntax.TypeOf c ->
      let c = Desugar.top_computation c in
      let drty_sch, top_change = infer_top_comp wholectx c in
      Format.printf "@[- : %t@]@." (Scheme.print_dirty_scheme drty_sch);
      ((ctx, top_change), env)
  | SugaredSyntax.Reset ->
      Tctx.reset ();
      print_endline ("Environment reset."); initial_state
  | SugaredSyntax.Help ->
      print_endline help_text; (wholectx, env)
  | SugaredSyntax.Quit -> exit 0
  | SugaredSyntax.Use fn -> use_file (wholectx, env) (fn, interactive)
  | SugaredSyntax.TopLet defs ->
      let defs = Desugar.top_let defs in
      (* XXX What to do about the dirts? *)
      let vars, nonpoly, change = Infer.infer_let ~loc ctx defs in
      let ctx = List.fold_right (fun (x, ty_sch) env -> Ctx.extend env x ty_sch) vars ctx in
      let extend_nonpoly (x, ty) env =
        (x, ([(x, ty)], ty, Constraints.empty)) :: env
      in
      let vars = List.fold_right extend_nonpoly nonpoly vars in
      let top_change = Common.compose top_change change in
      let sch_change (ctx, ty, cnstrs) =
        let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
        (ctx, ty, cnstrs)
      in
      List.iter (fun (p, c) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
      let env =
        List.fold_right
          (fun (p,c) env -> let v = Eval.run env c in Eval.extend p v env)
          defs env
      in
        if interactive then begin
          List.iter (fun (x, tysch) ->
                       match Eval.lookup x env with
                         | None -> assert false
                         | Some v ->
                         Format.printf "@[val %t : %t = %t@]@." (Print.variable x) (Scheme.print_ty_scheme (sch_change tysch)) (Value.print_value v))
            vars
        end;
        ((ctx, top_change), env)
    | SugaredSyntax.TopLetRec defs ->
        let defs = Desugar.top_let_rec defs in
        let vars, change = Infer.infer_let_rec ~loc ctx defs in
        let ctx = List.fold_right (fun (x, ty_sch) env -> Ctx.extend ctx x ty_sch) vars ctx in
        let top_change = Common.compose top_change change in
        let sch_change (ctx, ty, cnstrs) =
          let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
          (ctx, ty, cnstrs)
        in
        List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
        let env = Eval.extend_let_rec env defs in
          if interactive then begin
            List.iter (fun (x, tysch) -> Format.printf "@[val %t : %t = <fun>@]@." (Print.variable x) (Scheme.print_ty_scheme (sch_change tysch))) vars
          end;
          ((ctx, top_change), env)
    | SugaredSyntax.External (x, t, f) ->
      let (x, t) = Desugar.external_ty (Tctx.is_effect ~loc) x t in
      let ctx = Ctx.extend ctx x t in
        begin match Common.lookup f External.values with
          | Some v -> ((ctx, top_change), Eval.update x v env)
          | None -> Error.runtime "unknown external symbol %s." f
        end
    | SugaredSyntax.Tydef tydefs ->
        let tydefs = Desugar.tydefs ~loc tydefs in
        Tctx.extend_tydefs ~loc tydefs ;
        ((ctx, top_change), env)


and use_file env (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
    List.fold_left (exec_cmd interactive) env cmds
