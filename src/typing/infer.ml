module T = Type
module Untyped = CoreSyntax
module Typed = TypedSyntax

let ty_less = Scheme.ty_less
let dirt_less = Scheme.dirt_less
let dirty_less = Scheme.dirty_less
let just = Scheme.just
let trim_context = Scheme.trim_context

module type TYPINGENV =
sig
  type t

  val empty : t
  val lookup : t -> TypedSyntax.variable -> Scheme.ty_scheme option
  val update : t -> TypedSyntax.variable -> Scheme.ty_scheme -> t
end

module TypingEnv : TYPINGENV =
struct
  type t = (Typed.variable, Scheme.ty_scheme) OldUtils.assoc

  let empty = []
  let lookup ctx x = OldUtils.option_map Scheme.refresh (OldUtils.lookup x ctx)
  let update ctx x sch = (x, sch) :: ctx
end

type state = {
  context : TypingEnv.t;
  effects : (Type.ty * Type.ty) Untyped.EffectMap.t
}

let initial = {
  context = TypingEnv.empty;
  effects = Untyped.EffectMap.empty;
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

let infer_effect env eff =
  try
    Some (Untyped.EffectMap.find eff env.effects)
  with
    | Not_found -> None

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
      if not (OldUtils.injective fst lst) then
        Error.typing ~loc "Fields in a record must be distinct";
      let lst = OldUtils.assoc_map type_pattern lst in
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~loc "Unbound record field label %s" fld
      | Some (ty, (ty_name, fld_tys)) ->
          let infer (fld, p) (ctx, chngs) =
            begin match OldUtils.lookup fld fld_tys with
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
  match expr with
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
      let lst = OldUtils.assoc_map (type_expr env) lst in
      Typed.record ~loc lst
  | Untyped.Variant (lbl, e) ->
      Typed.variant ~loc (lbl, OldUtils.option_map (type_expr env) e)
  | Untyped.Lambda a ->
      Typed.lambda ~loc (type_abstraction env a)
  | Untyped.Effect eff ->
      Typed.effect ~loc eff (infer_effect env)
  | Untyped.Handler h ->
      Typed.handler ~loc (type_handler env h) (infer_effect env)
and type_comp env {Untyped.term=comp; Untyped.location=loc} =
  match comp with
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
      let defs, poly_tyschs = type_let_defs ~loc env defs in
      let env' = extend_env poly_tyschs env in
      Typed.let' ~loc defs (type_comp env' c)
  | Untyped.LetRec (defs, c) ->
      let defs, poly_tyschs = type_let_rec_defs ~loc env defs in
      let env' = extend_env poly_tyschs env in
      Typed.let_rec' ~loc defs (type_comp env' c)
and type_abstraction env (p, c) =
  Typed.abstraction ~loc:(c.Untyped.location) (type_pattern p) (type_comp env c)
and type_abstraction2 env (p1, p2, c) =
  Typed.abstraction2 ~loc:(c.Untyped.location) (type_pattern p1) (type_pattern p2) (type_comp env c)
and type_handler env h =
  {
    Typed.effect_clauses = OldUtils.assoc_map (type_abstraction2 env) h.Untyped.effect_clauses;
    Typed.value_clause = type_abstraction env h.Untyped.value_clause;
    Typed.finally_clause = type_abstraction env h.Untyped.finally_clause;
  }
and type_let_defs ~loc env defs =
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (poly_tys, nonpoly_tys, ctx, chngs, defs) =
    let p = type_pattern p
    and c = type_comp env c in
    let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
    let ctx_c, drty_c, cnstrs_c = c.Typed.scheme in
    let poly_tys, nonpoly_tys =
      match c.Typed.term with
      | Typed.Value _ ->
          ctx_p @ poly_tys, nonpoly_tys
      | Typed.Apply _ | Typed.Match _ | Typed.Handle _
      | Typed.Let _ | Typed.LetRec _ | Typed.Check _ ->
          poly_tys, ctx_p @ nonpoly_tys
    in
    poly_tys, nonpoly_tys, ctx_c @ ctx, [
      Scheme.dirty_less ~loc:c.Typed.location drty_c (ty_p, drt);
      Scheme.just cnstrs_p;
      Scheme.just cnstrs_c
    ] @ chngs, (p, c) :: defs
  in
  let poly_tys, nonpoly_tys, ctx, chngs, defs = List.fold_right add_binding defs ([], [], [], [], []) in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.finalize_ty_scheme ~loc ctx ty chngs) poly_tys in
  defs, poly_tyschs
and type_let_rec_defs ~loc env defs =
  let add_binding (x, a) (poly_tys, nonpoly_tys, ctx, chngs, defs) =
    let a = type_abstraction env a in
    let ctx_a, (ty_p, drty_c), cnstrs_a = a.Typed.scheme in
    let poly_tys, nonpoly_tys = (x, Type.Arrow (ty_p, drty_c)) :: poly_tys, nonpoly_tys in
    poly_tys, nonpoly_tys, ctx_a @ ctx, [
      Scheme.just cnstrs_a
    ] @ chngs, (x, a) :: defs
  in
  let poly_tys, nonpoly_tys, ctx, chngs, defs = List.fold_right add_binding defs ([], [], [], [], []) in
  let chngs = Scheme.trim_context ~loc poly_tys :: chngs in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.finalize_ty_scheme ~loc ctx ty chngs) poly_tys in
  defs, poly_tyschs

(* [infer_comp env c] infers the dirty type scheme of a computation [c] in a
   typing environment [env] of generalised variables.
   The scheme consists of:
   - the context, which contains non-generalised variables and their types,
   - the type of the expression,
   - the dirt of the computation, and
   - constraints connecting all these types. *)
let infer_pattern p =
  if !Config.disable_typing then Scheme.simple Type.universal_ty else (type_pattern p).Typed.scheme

let infer_comp env c =
  if !Config.disable_typing then Scheme.simple Type.universal_dirty else (type_comp env c).Typed.scheme

let infer_abstraction env a =
  (type_abstraction env a).Typed.scheme

let infer_let ~loc env defs =
  (* XXX Check for implicit sequencing *)
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (poly_tys, nonpoly_tys, ctx, chngs) =
    let ctx_p, ty_p, cnstrs_p = infer_pattern p in
    let ctx_c, drty_c, cnstrs_c = infer_comp env c in
    let poly_tys, nonpoly_tys =
      match c.Untyped.term with
      | Untyped.Value _ ->
          ctx_p @ poly_tys, nonpoly_tys
      | Untyped.Apply _ | Untyped.Match _ | Untyped.Handle _
      | Untyped.Let _ | Untyped.LetRec _ | Untyped.Check _ ->
          poly_tys, ctx_p @ nonpoly_tys
    in
    poly_tys, nonpoly_tys, ctx_c @ ctx, [
      dirty_less ~loc:c.Untyped.location drty_c (ty_p, drt);
      just cnstrs_p;
      just cnstrs_c
    ] @ chngs
  in
  let poly_tys, nonpoly_tys, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.finalize_ty_scheme ~loc ctx ty chngs) poly_tys in
  let change (ctx_c, (ty_c, drt_c), cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx @ ctx_c) (ty_c, drt) ([
      Scheme.less_context ~loc nonpoly_tys;
      dirt_less drt_c drt;
      just cnstrs_c;
    ] @ chngs)
  in
  poly_tyschs, nonpoly_tys, change

let infer_let_rec ~loc env defs =
  let drt = Type.fresh_dirt () in
  let add_binding (x, a) (poly_tys, nonpoly_tys, ctx, chngs) =
    let ctx_a, (ty_p, drty_c), cnstrs_a = infer_abstraction env a in
    let poly_tys, nonpoly_tys = (x, Type.Arrow (ty_p, drty_c)) :: poly_tys, nonpoly_tys in
    poly_tys, nonpoly_tys, ctx_a @ ctx, [
      just cnstrs_a
    ] @ chngs
  in
  let poly_tys, nonpoly_tys, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
  let chngs = trim_context ~loc poly_tys :: chngs in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.finalize_ty_scheme ~loc ctx ty chngs) poly_tys in
  let change (ctx_c, (ty_c, drt_c), cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx @ ctx_c) (ty_c, drt) ([
      dirt_less drt_c drt;
      just cnstrs_c;
    ] @ chngs)
  in
  poly_tyschs, nonpoly_tys, change


type t = {
  typing : state;
  change : Scheme.dirty_scheme -> Scheme.dirty_scheme;
}

let empty = {
  typing = initial;
  change = OldUtils.id;
}

let infer_top_comp st c =
  let c' = type_comp st.typing c in
  let ctx', (ty', drt'), cnstrs' = c'.Typed.scheme in
  let change = Scheme.add_to_top ~loc:c'.Typed.location ctx' cnstrs' in
  let top_change = OldUtils.compose st.change change in
  let ctx = match c'.Typed.term with
  | Typed.Value _ -> ctx'
  | _ -> (Desugar.fresh_variable (Some "$top_comp"), ty') :: ctx'
  in
  let drty_sch = top_change (ctx, (ty', drt'), cnstrs') in
  Exhaust.check_comp c;

  drty_sch, c', {st with change = top_change}

let add_top_effect st eff (ty1, ty2) =
  {st with typing = add_effect st.typing eff (ty1, ty2)}

let infer_top_let ~loc st defs =
  (* XXX What to do about the dirts? *)
  let vars, nonpoly, change = infer_let ~loc st.typing defs in
  let typing_env = List.fold_right (fun (x, ty_sch) env -> add_def env x ty_sch) vars st.typing in
  let extend_nonpoly (x, ty) env =
    (x, ([(x, ty)], ty, Constraints.empty)) :: env
  in
  let vars = List.fold_right extend_nonpoly nonpoly vars in
  let top_change = OldUtils.compose st.change change in
  let sch_change (ctx, ty, cnstrs) =
    let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
    (ctx, ty, cnstrs)
  in
  let defs', poly_tyschs = type_let_defs ~loc st.typing defs in
  List.iter (fun (p, c) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs;
  let vars' = OldUtils.assoc_map sch_change vars in
  defs', vars', {
    typing = typing_env;
    change = top_change;
  }

let infer_top_let_rec ~loc st defs =
  let vars, _, change = infer_let_rec ~loc st.typing defs in
  let defs', poly_tyschs = type_let_rec_defs ~loc st.typing defs in
  let typing_env = List.fold_right (fun (x, ty_sch) env -> add_def env x ty_sch) vars st.typing in
  let top_change = OldUtils.compose st.change change in
  let sch_change (ctx, ty, cnstrs) =
    let (ctx, (ty, _), cnstrs) = top_change (ctx, (ty, Type.fresh_dirt ()), cnstrs) in
    (ctx, ty, cnstrs)
  in
  List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs ;
  let vars' = OldUtils.assoc_map sch_change vars in
  defs', vars', {
    typing = typing_env;
    change = top_change;
  }

let add_top_def st x ty =
  { st with typing = add_def st.typing x ([], ty, Constraints.empty) }
