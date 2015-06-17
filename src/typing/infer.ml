module C = Common
module T = Type

let ty_less = Scheme.ty_less
let dirt_less = Scheme.dirt_less
let dirty_less = Scheme.dirty_less
let just = Scheme.just
let trim_context = Scheme.trim_context

type state = {
  context : Ctx.t;
  effects : (Type.ty * Type.ty) Untyped.EffectMap.t
}

let initial = {
  context = Ctx.empty;
  effects = Untyped.EffectMap.empty;
}

let simple ty = ([], ty, Constraints.empty)
let empty_dirt () = { Type.ops = []; Type.rest = Type.fresh_dirt_param () }

let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty

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
let rec infer_pattern (p, loc) =
  if !Config.disable_typing then simple Type.universal_ty else
  let unify = Scheme.finalize_pattern_scheme in
  let ty_sch = match p with

  | Pattern.Var x ->
      let ty = Type.fresh_ty () in
      [(x, ty)], ty, Constraints.empty

  | Pattern.As (p, x) ->
      let ctx, ty, cnstrs = infer_pattern p in
      (x, ty) :: ctx, ty, cnstrs

  | Pattern.Nonbinding ->
      simple (Type.fresh_ty ())

  | Pattern.Const const ->
      simple (ty_of_const const)

  | Pattern.Tuple ps ->
      let infer p (ctx, tys, chngs) =
        let ctx_p, ty_p, cnstrs_p = infer_pattern p in
        ctx_p @ ctx, ty_p :: tys, [
          just cnstrs_p
        ] @ chngs
      in
      let ctx, tys, chngs = List.fold_right infer ps ([], [], []) in
      unify ctx (Type.Tuple tys) chngs

  | Pattern.Record [] ->
      assert false

  | Pattern.Record (((fld, _) :: _) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~loc "Fields in a record must be distinct";
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~loc "Unbound record field label %s" fld
      | Some (ty, (ty_name, fld_tys)) ->
          let infer (fld, p) (ctx, chngs) =
            begin match C.lookup fld fld_tys with
            | None -> Error.typing ~loc "Unexpected field %s in a pattern of type %s" fld ty_name
            | Some fld_ty ->
                let ctx_p, ty_p, cnstrs_p = infer_pattern p in
                ctx_p @ ctx, [
                  ty_less ~loc fld_ty ty_p;
                  just cnstrs_p
                ] @ chngs
            end
        in
        let ctx, chngs = List.fold_right infer lst ([], []) in
        unify ctx ty chngs
      end

  | Pattern.Variant (lbl, p) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some (ty, arg_ty) ->
          begin match p, arg_ty with
            | None, None -> simple ty
            | Some p, Some arg_ty ->
                let ctx_p, ty_p, cnstrs_p = infer_pattern p in
                unify ctx_p ty [
                  ty_less ~loc arg_ty ty_p;
                  just cnstrs_p
                ]
            | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
            | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
          end
      end

  in
  (* Print.debug "%t : %t" (Untyped.print_pattern (p, loc)) (Scheme.print_ty_scheme ty_sch); *)
  ty_sch

(* [infer_expr env e] infers the type scheme of an expression [e] in a
   typing environment [env] of generalised variables.
   The scheme consists of:
   - the context, which contains non-generalised variables and their types,
   - the type of the expression, and
   - constraints connecting all these types. *)
let rec infer_expr env e =
  if !Config.disable_typing then simple Type.universal_ty else
  let loc = e.Untyped.location in
  let unify = Scheme.finalize_ty_scheme ~loc in
  let ty_sch = match e.Untyped.term with

  | Untyped.Var x ->
      begin match Ctx.lookup env.context x with
      | Some (ctx, ty, cnstrs) ->
          (ctx, ty, cnstrs)
      | None ->
          let ty = Type.fresh_ty () in
          unify [(x, ty)] ty []
      end

  | Untyped.Const const ->
      simple (ty_of_const const)

  | Untyped.Tuple es ->
      let infer e (ctx, tys, chngs) =
        let ctx_e, ty_e, cnstrs_e = infer_expr env e in
        ctx_e @ ctx, ty_e :: tys, [
          just cnstrs_e
        ] @ chngs
      in
      let ctx, tys, chngs = List.fold_right infer es ([], [], []) in
      unify ctx (Type.Tuple tys) chngs

  | Untyped.Record [] ->
      assert false

  | Untyped.Record (((fld, _) :: _) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~loc "Fields in a record must be distinct";
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~loc "Unbound record field label %s" fld
      | Some (ty, (ty_name, fld_tys)) ->
          if List.length lst <> List.length fld_tys then
            Error.typing ~loc "The record of type %s has an incorrect number of fields" ty_name;
          let infer (fld, e) (ctx, chngs) =
            begin match C.lookup fld fld_tys with
            | None -> Error.typing ~loc "Unexpected field %s in a record of type %s" fld ty_name
            | Some fld_ty ->
                let ctx_e, ty_e, cnstrs_e = infer_expr env e in
                ctx_e @ ctx, [
                  ty_less ~loc ty_e fld_ty;
                  just cnstrs_e
                ] @ chngs
            end
        in
        let ctx, chngs = List.fold_right infer lst ([], []) in
        unify ctx ty chngs
      end

  | Untyped.Variant (lbl, e) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some (ty, arg_ty) ->
          begin match e, arg_ty with
            | None, None -> simple ty
            | Some e, Some arg_ty ->
                let ctx_e, ty_e, cnstrs_e = infer_expr env e in
                unify ctx_e ty [
                  ty_less ~loc ty_e arg_ty;
                  just cnstrs_e
                ]
            | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
            | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
          end
      end
      
  | Untyped.Lambda a ->
      let ctx, ty1, drty2, cnstrs = infer_abstraction env a in
      ctx, Type.Arrow (ty1, drty2), cnstrs
      
  | Untyped.Effect eff ->
      let r = Type.fresh_region_param () in
      begin match infer_effect env eff with
      | None -> Error.typing ~loc "Unbound effect %s" eff
      | Some (ty_par, ty_res) ->
          let drt = {Type.ops = [eff, r]; Type.rest = Type.fresh_dirt_param ()} in
          unify [] (Type.Arrow (ty_par, (ty_res, drt))) [
            Scheme.add_full_region r
          ]
      end

  | Untyped.Handler {Untyped.operations = ops; Untyped.value = a_val; Untyped.finally = a_fin} -> 
      let drt_mid = Type.fresh_dirt () in
      let ty_mid = Type.fresh_ty () in

      let infer (eff, a2) (ctx, chngs) =
        begin match infer_effect env eff with
        | None -> Error.typing ~loc "Unbound effect %s in a handler" eff
        | Some (ty_par, ty_arg) ->
            let ctx_a, ty_p, ty_k, drty_c, cnstrs_a = infer_abstraction2 env a2 in
            ctx_a @ ctx, [
              ty_less ~loc ty_par ty_p;
              ty_less ~loc (Type.Arrow (ty_arg, (ty_mid, drt_mid))) ty_k;
              dirty_less ~loc drty_c (ty_mid, drt_mid);
              just cnstrs_a
            ] @ chngs
        end
      in
      let ctxs, chngs = List.fold_right infer ops ([], []) in

      let make_dirt op (ops_in, ops_out) =
        let r_in = Type.fresh_region_param () in
        let r_out = Type.fresh_region_param () in
        (op, r_in) :: ops_in, (op, r_out) :: ops_out
      in
      let ops_in, ops_out = List.fold_right make_dirt (Common.uniq (List.map fst ops)) ([], []) in

      let ctx_val, ty_val, drty_val, cnstrs_val = infer_abstraction env a_val in
      let ctx_fin, ty_fin, drty_fin, cnstrs_fin = infer_abstraction env a_fin in

      let ty_in = Type.fresh_ty () in
      let drt_rest = Type.fresh_dirt_param () in
      let drt_in = {Type.ops = ops_in; Type.rest = drt_rest} in
      let drt_out = Type.fresh_dirt () in
      let ty_out = Type.fresh_ty () in

      unify (ctx_val @ ctx_fin @ ctxs) (Type.Handler((ty_in, drt_in), (ty_out, drt_out))) ([
        dirt_less {Type.ops = ops_out; Type.rest = drt_rest} drt_mid;
        ty_less ~loc ty_in ty_val;
        dirty_less ~loc drty_val (ty_mid, drt_mid);
        ty_less ~loc ty_mid ty_fin;
        dirt_less drt_mid drt_out;
        dirty_less ~loc drty_fin (ty_out, drt_out);
        just cnstrs_val;
        just cnstrs_fin
      ] @ chngs)

  in
  (* Print.debug "%t : %t" (Untyped.print_expression (e, loc)) (Scheme.print_ty_scheme ty_sch); *)
  ty_sch
              
(* [infer_comp env c] infers the dirty type scheme of a computation [c] in a
   typing environment [env] of generalised variables.
   The scheme consists of:
   - the context, which contains non-generalised variables and their types,
   - the type of the expression,
   - the dirt of the computation, and
   - constraints connecting all these types. *)
and infer_comp env c =
  if !Config.disable_typing then simple Type.universal_dirty else
  let loc = c.Untyped.location in
  let unify = Scheme.finalize_dirty_scheme ~loc in
  let drty_sch = match c.Untyped.term with

  | Untyped.Value e ->
      let ctx, ty, cnstrs = infer_expr env e in
      ctx, (ty, empty_dirt ()), cnstrs

  | Untyped.Let (defs, c) ->
      let vars, nonpoly, change = infer_let ~loc env defs in
      let change2 (ctx_c, drty_c, cnstrs_c) =
        Scheme.finalize_dirty_scheme ~loc (ctx_c) drty_c ([
          Scheme.remove_context ~loc nonpoly;
          just cnstrs_c
        ])
      in
      let env' = List.fold_right (fun (x, ty_sch) env -> {env with context = Ctx.extend env.context x ty_sch}) vars env in
      change2 (change (infer_comp env' c))

  | Untyped.LetRec (defs, c) ->
      let vars, change = infer_let_rec ~loc env defs in
      let env' = List.fold_right (fun (x, ty_sch) env -> {env with context = Ctx.extend env.context x ty_sch}) vars env in
      change (infer_comp env' c)

  | Untyped.Match (e, []) ->
      let ctx_e, ty_e, cnstrs_e = infer_expr env e in
      unify ctx_e (Type.fresh_ty (), empty_dirt ()) [
        ty_less ~loc ty_e Type.empty_ty;
        just cnstrs_e
      ]

  | Untyped.Match (e, cases) ->
      let ctx_e, ty_e, cnstrs_e = infer_expr env e in
      let drty = Type.fresh_dirty () in
      let infer_case ((p, c) as a) (ctx, chngs) =
        let ctx_a, ty_p, drty_c, cnstrs_a = infer_abstraction env a in
        ctx_a @ ctx, [
          ty_less ~loc:e.Untyped.location ty_e ty_p;
          dirty_less ~loc:c.Untyped.location drty_c drty;
          just cnstrs_a
        ] @ chngs
      in
      let ctx, chngs = List.fold_right infer_case cases (ctx_e, [just cnstrs_e]) in
      unify ctx drty chngs

  | Untyped.While (c1, c2) ->
      let ctx_c1, (ty_c1, drt_c1), cnstrs_c1 = infer_comp env c1 in
      let ctx_c2, (ty_c2, drt_c2), cnstrs_c2 = infer_comp env c2 in
      let drt = Type.fresh_dirt () in
      unify (ctx_c1 @ ctx_c2) (Type.unit_ty, drt) [
        ty_less ~loc ty_c1 Type.bool_ty;
        ty_less ~loc ty_c2 Type.unit_ty;
        dirt_less drt_c1 drt;
        dirt_less drt_c2 drt;
        just cnstrs_c1;
        just cnstrs_c2
      ]

  | Untyped.For (i, e1, e2, c, _) ->
      let ctx_e1, ty_e1, cnstrs_e1 = infer_expr env e1 in
      let ctx_e2, ty_e2, cnstrs_e2 = infer_expr env e2 in
      let ctx_c, (ty_c, drt_c), cnstrs_c = infer_comp env c in
      unify (ctx_e1 @ ctx_e2 @ ctx_c) (Type.unit_ty, drt_c) [
        ty_less ~loc:e1.Untyped.location ty_e1 Type.int_ty;
        ty_less ~loc:e2.Untyped.location ty_e2 Type.int_ty;
        ty_less ~loc:c.Untyped.location ty_c Type.unit_ty;
        just cnstrs_e1;
        just cnstrs_e2;
        just cnstrs_c
      ]

  | Untyped.Apply (e1, e2) ->
      let ctx_e1, ty_e1, cnstrs_e1 = infer_expr env e1 in
      let ctx_e2, ty_e2, cnstrs_e2 = infer_expr env e2 in
      let drty = Type.fresh_dirty () in
      unify (ctx_e1 @ ctx_e2) drty [
        ty_less ~loc ty_e1 (Type.Arrow (ty_e2, drty));
        just cnstrs_e1;
        just cnstrs_e2
      ]

  | Untyped.Handle (e, c) ->
      let ctx_e, ty_e, cnstrs_e = infer_expr env e
      and ctx_c, drty_c, cnstrs_c = infer_comp env c
      and drty = Type.fresh_dirty () in
      unify (ctx_e @ ctx_c) drty [
        ty_less ~loc ty_e (Type.Handler (drty_c, drty));
        just cnstrs_e;
        just cnstrs_c
      ]

  | Untyped.Check c ->
      ignore (infer_comp env c);
      simple (Type.unit_ty, empty_dirt ())

  in
  (* Print.debug "%t : %t" (Untyped.print_computation (c, loc)) (Scheme.print_dirty_scheme drty_sch); *)
  drty_sch

and infer_abstraction env (p, c) =
  let ctx_p, ty_p, cnstrs_p = infer_pattern p in
  let ctx_c, drty_c, cnstrs_c = infer_comp env c in
  match Scheme.finalize_ty_scheme ~loc:c.Untyped.location ctx_c (Type.Arrow (ty_p, drty_c)) [
    trim_context ~loc:c.Untyped.location ctx_p;
    just cnstrs_p;
    just cnstrs_c
  ] with
  | ctx, Type.Arrow (ty_p, drty_c), cnstrs -> ctx, ty_p, drty_c, cnstrs
  | _ -> assert false

and infer_abstraction2 env (p1, p2, c) =
  let ctx_p1, ty_p1, cnstrs_p1 = infer_pattern p1 in
  let ctx_p2, ty_p2, cnstrs_p2 = infer_pattern p2 in
  let ctx_c, drty_c, cnstrs_c = infer_comp env c in
  match Scheme.finalize_ty_scheme ~loc:c.Untyped.location ctx_c (Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c)) [
    trim_context ~loc:c.Untyped.location (ctx_p1 @ ctx_p2);
    just cnstrs_p1;
    just cnstrs_p2;
    just cnstrs_c
  ] with
  | ctx, Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c), cnstrs -> ctx, ty_p1, ty_p2, drty_c, cnstrs
  | _ -> assert false

and infer_let ~loc env defs =
  (* XXX Check for implicit sequencing *)
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (poly, nonpoly, ctx, chngs) =
    let ctx_p, ty_p, cnstrs_p = infer_pattern p in
    let ctx_c, drty_c, cnstrs_c = infer_comp env c in
    let poly, nonpoly =
      match c.Untyped.term with
      | Untyped.Value _ ->
          ctx_p @ poly, nonpoly
      | Untyped.Apply _ | Untyped.Match _ | Untyped.While _ | Untyped.For _
      | Untyped.Handle _ | Untyped.Let _ | Untyped.LetRec _ | Untyped.Check _ ->
          poly, ctx_p @ nonpoly
    in
    poly, nonpoly, ctx_c @ ctx, [
      dirty_less ~loc:c.Untyped.location drty_c (ty_p, drt);
      just cnstrs_p;
      just cnstrs_c
    ] @ chngs
  in
  let poly, nonpoly, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
  let extend_poly (x, ty) env =
    let ty_sch = Scheme.finalize_ty_scheme ~loc ctx ty chngs in
    (x, ty_sch) :: env
  in
  let vars = List.fold_right extend_poly poly [] in
  let change (ctx_c, (ty_c, drt_c), cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx @ ctx_c) (ty_c, drt) ([
      dirt_less drt_c drt;
      Scheme.less_context ~loc nonpoly;
      just cnstrs_c;
    ] @ chngs)
  in
  vars, nonpoly, change

and infer_let_rec ~loc env defs =
  let infer (x, a) (poly, ctx, chngs) =
    let ctx_a, ty_p, drty_c, cnstrs_a = infer_abstraction env a in
    (x, Type.Arrow (ty_p, drty_c)) :: poly, ctx_a @ ctx, [
      just cnstrs_a
    ] @ chngs
  in
  let poly, ctx, chngs = List.fold_right infer defs ([], [], []) in
  let chngs = trim_context ~loc poly :: chngs in
  let extend_poly (x, ty) env =
    let ty_sch = Scheme.finalize_ty_scheme ~loc ctx ty chngs in
    (x, ty_sch) :: env
  in
  let vars = List.fold_right extend_poly poly [] in
  let change (ctx_c, drty_c, cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx @ ctx_c) drty_c ([
        just cnstrs_c;
    ] @ chngs)
  in
  vars, change
