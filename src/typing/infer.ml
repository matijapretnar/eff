module T = Type

let ty_less = Scheme.ty_less
let dirt_less = Scheme.dirt_less
let dirty_less = Scheme.dirty_less
let just = Scheme.just
let trim_context = Scheme.trim_context

type state = {
  context : TypingEnv.t;
  effects : (Type.ty * Type.ty) Untyped.EffectMap.t
}

let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty

let add_effect env eff (ty1, ty2) =
  {env with effects = Untyped.EffectMap.add eff (ty1, ty2) env.effects}

let add_def env x ty_sch =
  {env with context = TypingEnv.update env.context x ty_sch}

let infer_effect ~loc env eff =
  try
    eff, (Untyped.EffectMap.find eff env.effects)
  with
  | Not_found -> Error.typing ~loc "Unbound effect %s" eff

let tag_polymorphic_dirt tysch =
  let tysch = Scheme.refresh tysch in
  let r = Params.fresh_region_param ()
  and d = Params.fresh_dirt_param ()
  and ds = Scheme.polymorphic_dirt tysch in
  let drt = {Type.ops = ["///", r]; Type.rest = d} in
  let (ctx, ty, cnstrs) = tysch in
  Print.debug "BEFORE: %t" (Scheme.print_ty_scheme tysch);
  let tysch =
  Scheme.finalize_ty_scheme ~loc:Location.unknown ctx ty (
    List.map (fun d -> Scheme.dirt_less drt (Type.simple_dirt d)) ds @ [
    Scheme.just cnstrs;
    Scheme.add_full_region r
  ]) in
  Print.debug "AFTER: %t" (Scheme.print_ty_scheme tysch);
  tysch

(* [infer_pattern p] infers the type scheme of a pattern [p].
   This consists of:
   - the context, which contains bound variables and their types,
   - the type of the whole pattern (what it matches against), and
   - constraints connecting all these types.
   Note that unlike in ordinary type schemes, context types are positive while
   pattern type is negative. *)
let rec type_pattern p =
  let loc = p.Untyped.location in
  let unify = Scheme.finalize_pattern_scheme ~loc in
  let ty_sch, pat = match p.Untyped.term with

    | Untyped.PVar x ->
      let ty = Type.fresh_ty () in
      ([(x, ty)], ty, Constraints.empty), Typed.PVar x

    | Untyped.PAs (p, x) ->
      let p = type_pattern p in
      let ctx, ty, cnstrs = p.Typed.scheme in
      ((x, ty) :: ctx, ty, cnstrs), Typed.PAs (p, x)

    | Untyped.PNonbinding ->
      Scheme.simple (Type.fresh_ty ()), Typed.PNonbinding

    | Untyped.PConst const ->
      Scheme.simple (ty_of_const const), Typed.PConst const

    | Untyped.PTuple ps ->
      let ps = List.map type_pattern ps in
      let infer p (ctx, tys, chngs) =
        let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
        ctx_p @ ctx, ty_p :: tys, [
          just cnstrs_p
        ] @ chngs
      in
      let ctx, tys, chngs = List.fold_right infer ps ([], [], []) in
      unify ctx (Type.Tuple tys) chngs, Typed.PTuple ps

    | Untyped.PRecord [] ->
      assert false

    | Untyped.PRecord (((fld, _) :: _) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~loc "Fields in a record must be distinct";
      let lst = Common.assoc_map type_pattern lst in
      begin match Tctx.infer_field fld with
        | None -> Error.typing ~loc "Unbound record field label %s" fld
        | Some (ty, (ty_name, fld_tys)) ->
          let infer (fld, p) (ctx, chngs) =
            begin match Common.lookup fld fld_tys with
              | None -> Error.typing ~loc "Unexpected field %s in a pattern of type %s" fld ty_name
              | Some fld_ty ->
                let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
                ctx_p @ ctx, [
                  ty_less ~loc fld_ty ty_p;
                  just cnstrs_p
                ] @ chngs
            end
          in
          let ctx, chngs = List.fold_right infer lst ([], []) in
          unify ctx ty chngs, Typed.PRecord lst
      end

    | Untyped.PVariant (lbl, p) ->
      begin match Tctx.infer_variant lbl with
        | None -> Error.typing ~loc "Unbound constructor %s" lbl
        | Some (ty, arg_ty) ->
          begin match p, arg_ty with
            | None, None -> Scheme.simple ty, Typed.PVariant (lbl, None)
            | Some p, Some arg_ty ->
              let p = type_pattern p in
              let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
              unify ctx_p ty [
                ty_less ~loc arg_ty ty_p;
                just cnstrs_p
              ], Typed.PVariant (lbl, Some p)
            | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
            | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
          end
      end

  in
  (* Print.debug "%t : %t" (Untyped.print_pattern (p, loc)) (Scheme.print_ty_scheme ty_sch); *)
  {
    Typed.term = pat;
    Typed.scheme = ty_sch;
    Typed.location = loc
  }

let extend_env vars env =
  List.fold_right (fun (x, ty_sch) env -> {env with context = TypingEnv.update env.context x ty_sch}) vars env

let rec type_expr env {Untyped.term=expr; Untyped.location=loc} =
  let typed_expr = match expr with
    | Untyped.Var x ->
      let ty_sch = begin match TypingEnv.lookup env.context x with
        | Some ty_sch -> ty_sch
        | None ->
          let ty = Type.fresh_ty () in
          ([(x, ty)], ty, Constraints.empty)
      end
      in
      Typed.var ~loc x ty_sch
    | Untyped.Const const -> Typed.const ~loc const
    | Untyped.Tuple es ->
      let es = List.map (type_expr env) es in
      Typed.tuple ~loc es
    | Untyped.Record lst ->
      let lst = Common.assoc_map (type_expr env) lst in
      Typed.record ~loc lst
    | Untyped.Variant (lbl, e) ->
      Typed.variant ~loc (lbl, Common.option_map (type_expr env) e)
    | Untyped.Lambda a ->
      Typed.lambda ~loc (type_abstraction env a)
    | Untyped.Effect eff ->
      let eff = infer_effect ~loc env eff in
      Typed.effect ~loc eff
    | Untyped.Handler h ->
      let h' = type_handler env h in
      begin match h.Untyped.finally_clause with
      | None -> Typed.handler ~loc h'
      | Some a -> Typed.finally_handler ~loc h' (type_abstraction env a)
      end
  in
  (* Print.debug ~loc:typed_expr.Typed.location "%t" (Scheme.print_ty_scheme typed_expr.Typed.scheme); *)
  typed_expr
and type_comp env {Untyped.term=comp; Untyped.location=loc} =
  let typed_comp = match comp with
    | Untyped.Value e ->
      Typed.value ~loc (type_expr env e)
    | Untyped.Match (e, cases) ->
      Typed.match' ~loc (type_expr env e) (List.map (type_abstraction env) cases)
    | Untyped.Apply (e1, e2) ->
      Typed.apply ~loc (type_expr env e1) (type_expr env e2)
    | Untyped.Handle (e, c) ->
      Typed.handle ~loc (type_expr env e) (type_comp env c)
    | Untyped.Check c ->
      Typed.check ~loc (type_comp env c)
    | Untyped.Let (defs, c) ->
      let env', defs' = type_let_defs ~loc env defs in
      Typed.let' ~loc defs' (type_comp env' c)
    | Untyped.LetRec (defs, c) ->
      let env', defs' = type_let_rec_defs ~loc env defs in
      let env', defs' = type_let_rec_defs ~loc env' defs in
      Typed.let_rec' ~loc defs' (type_comp env' c)
  in
  (* Print.debug ~loc:typed_comp.Typed.location "%t" (Scheme.print_dirty_scheme typed_comp.Typed.scheme); *)
  typed_comp
and type_abstraction env (p, c) =
  Typed.abstraction ~loc:(c.Untyped.location) (type_pattern p) (type_comp env c)
and type_abstraction2 env (p1, p2, c) =
  Typed.abstraction2 ~loc:(c.Untyped.location) (type_pattern p1) (type_pattern p2) (type_comp env c)
and type_handler env h =
  let type_handler_clause (eff, (p1, p2, c)) =
    let eff = infer_effect ~loc:(c.Untyped.location) env eff in
    (eff, type_abstraction2 env (p1, p2, c)) in
  let value_clause = match h.Untyped.value_clause with
  | Some a -> a
  | None -> Desugar.id_abstraction Location.unknown
  in
  {
    Typed.effect_clauses = Common.map type_handler_clause h.Untyped.effect_clauses;
    Typed.value_clause = type_abstraction env value_clause;
  }
and type_let_defs ~loc env defs =
  let defs' = List.map (fun (p, c) -> (type_pattern p, type_comp env c)) defs in
  let defs'', poly_tyschs, _, _ = Typed.let_defs ~loc defs' in
  let poly_tyschs = Common.assoc_map tag_polymorphic_dirt poly_tyschs in
  let env' = extend_env poly_tyschs env in
  env', defs''
and type_let_rec_defs ~loc env defs =
  let defs' = Common.assoc_map (type_abstraction env) defs in
  let defs'', poly_tyschs, _ = Typed.let_rec_defs ~loc defs' in
  let poly_tyschs = Common.assoc_map tag_polymorphic_dirt poly_tyschs in
  let env' = extend_env poly_tyschs env in
  env', defs''
and type_top_let_defs ~loc env defs =
  let defs' = List.map (fun (p, c) -> (type_pattern p, type_comp env c)) defs in
  let defs'', poly_tyschs, nonpoly_tys, change = Typed.let_defs ~loc defs' in
  let poly_tyschs = Common.assoc_map tag_polymorphic_dirt poly_tyschs in
  let env' = extend_env poly_tyschs env in
  let extend_nonpoly (x, ty) env =
    (x, ([(x, ty)], ty, Constraints.empty)) :: env
  in
  let vars = List.fold_right extend_nonpoly nonpoly_tys poly_tyschs in
  env', vars, defs'', change
and type_top_let_rec_defs ~loc env defs =
  let defs' = Common.assoc_map (type_abstraction env) defs in
  let defs'', poly_tyschs, change = Typed.let_rec_defs ~loc defs' in
  let poly_tyschs = Common.assoc_map tag_polymorphic_dirt poly_tyschs in
  let env' = extend_env poly_tyschs env in
  env', poly_tyschs, defs'', change

type toplevel_state = {
  change : Scheme.dirty_scheme -> Scheme.dirty_scheme;
  typing : state;
}

let empty = {
  change = Common.id;
  typing = {
    context = TypingEnv.empty;
    effects = Untyped.EffectMap.empty;
  }
}

let infer_top_comp st c =
  let c' = type_comp st.typing c in
  let ctx', (ty', drt'), cnstrs' = c'.Typed.scheme in
  let change = Scheme.add_to_top ~loc:c'.Typed.location ctx' cnstrs' in
  let top_change = Common.compose st.change change in
  let ctx = match c'.Typed.term with
    | Typed.Value _ -> ctx'
    | _ -> (Desugar.fresh_variable (Some "$top_comp"), ty') :: ctx'
  in
  let drty_sch = top_change (ctx, (ty', drt'), cnstrs') in
  Exhaust.check_comp c;

  {c' with Typed.scheme = drty_sch}, {st with change = top_change}

let infer_toplevel ~loc st = function
  | Untyped.Tydef defs ->
    Tctx.extend_tydefs ~loc defs;
    Typed.Tydef defs, st
  | Untyped.TopLet defs ->
    (* XXX What to do about the dirts? *)
    let env', vars, defs', change = type_top_let_defs ~loc st.typing defs in
    let defs' = Common.assoc_map (Typed.push_constraints_comp Constraints.empty) defs' in
    let top_change = Common.compose st.change change in
    let sch_change (ctx, ty, cnstrs) =
      let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
      (ctx, ty, cnstrs)
    in
    List.iter (fun (p, c) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
    let vars = Common.assoc_map sch_change vars in
    let st = {typing = env'; change = top_change} in

    Typed.TopLet (defs', vars), st
  | Untyped.TopLetRec defs'' ->
    let env', vars, defs', change = type_top_let_rec_defs ~loc st.typing defs'' in
    let env', vars, defs', change = type_top_let_rec_defs ~loc env' defs'' in
    let defs' = Common.assoc_map (Typed.push_constraints_abs Constraints.empty) defs' in
    let top_change = Common.compose st.change change in
    let sch_change (ctx, ty, cnstrs) =
      let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
      (ctx, ty, cnstrs)
    in
    List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs'' ;
    let vars = Common.assoc_map sch_change vars in
    let st = {typing = env'; change = top_change} in
    Typed.TopLetRec (defs', vars), st
  | Untyped.External (x, ty, f) ->
    let st = {st with typing = add_def st.typing x ([], ty, Constraints.empty)} in
    Typed.External (x, ty, f), st
  | Untyped.DefEffect (eff, (ty1, ty2)) ->
    let st = {st with typing = add_effect st.typing eff (ty1, ty2)} in
    Typed.DefEffect ((eff, (ty1, ty2)), (ty1, ty2)), st
  | Untyped.Computation c ->
    let c, st = infer_top_comp st c in
    let c = Typed.push_constraints_comp Constraints.empty c in
    Typed.Computation c, st
  | Untyped.Use fn ->
    Typed.Use fn, st
  | Untyped.Reset ->
    Typed.Reset, st
  | Untyped.Help ->
    Typed.Help, st
  | Untyped.Quit ->
    Typed.Quit, st
  | Untyped.TypeOf c ->
    let c, st = infer_top_comp st c in
    let c = Typed.push_constraints_comp Constraints.empty c in
    Typed.TypeOf c, st


let type_cmd st cmd =
  let loc = cmd.Untyped.location in
  let ty_st = {change = st.change; typing = st.typing} in
  let cmd, ty_st = infer_toplevel ~loc ty_st cmd.Untyped.term in
  let st = {change = ty_st.change; typing = ty_st.typing} in
  (cmd, loc), st

let type_cmds st cmds =
  let cmds, st =
    List.fold_left (fun (cmds, st) cmd ->
        let cmd, st = type_cmd st cmd in
        (cmd :: cmds, st)
      ) ([], st) cmds
  in
  List.rev cmds, st
