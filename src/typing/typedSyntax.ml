(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type effect = OldUtils.effect

type ('term, 'scheme) annotation = {
  term: 'term;
  scheme: 'scheme;
  location: Location.t;
}

type pattern = (plain_pattern, Scheme.ty_scheme) annotation
and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (OldUtils.field, pattern) OldUtils.assoc
  | PVariant of OldUtils.label * pattern option
  | PConst of Const.t
  | PNonbinding

let annotate t sch loc = {
  term = t;
  scheme = sch;
  location = loc;
}

(** Pure expressions *)
type expression = (plain_expression, Scheme.ty_scheme) annotation
and plain_expression =
  | Var of variable
  | Const of Const.t
  | Tuple of expression list
  | Record of (OldUtils.field, expression) OldUtils.assoc
  | Variant of OldUtils.label * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler

(** Impure computations *)
and computation = (plain_computation, Scheme.dirty_scheme) annotation
and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Handle of expression * computation
  | Check of computation

(** Handler definitions *)
and handler = {
  effect_clauses : (effect, abstraction2) OldUtils.assoc;
  value_clause : abstraction;
  finally_clause : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation, Scheme.abstraction_scheme) annotation

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation, Scheme.abstraction2_scheme) annotation

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc

let abstraction ?loc p c : abstraction =
  let loc = backup_location loc [p.location; c.location] in
  {
    term = (p, c);
    scheme = Scheme.abstract ~loc p.scheme c.scheme;
    location = loc;
  }

let abstraction2 ?loc p1 p2 c =
  let loc = backup_location loc [p1.location; p2.location; c.location] in
  {
    term = (p1, p2, c);
    scheme = Scheme.abstract2 ~loc p1.scheme p2.scheme c.scheme;
    location = c.location;
  }

let var ?loc x ty_sch =
  let loc = backup_location loc [] in
  {
    term = Var x;
    scheme = ty_sch;
    location = loc;
  }

let const ?loc c =
  let loc = backup_location loc [] in
  let ty = match c with
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty
  in
  {
    term = Const c;
    scheme = ([], ty, Constraints.empty);
    location = loc;
  }

let tuple ?loc es =
  let loc = backup_location loc (List.map (fun e -> e.location) es) in
  let ctx, tys, constraints =
    List.fold_right (fun e (ctx, tys, constraints) ->
      let e_ctx, e_ty, e_constraints = e.scheme in
      e_ctx @ ctx, e_ty :: tys, Constraints.list_union [e_constraints; constraints]
    ) es ([], [], Constraints.empty)
  in
  {
    term = Tuple es;
    scheme = Scheme.clean_ty_scheme ~loc (ctx, Type.Tuple tys, constraints);
    location = loc;
  }

let record ?loc lst =
  let loc = backup_location loc (List.map (fun (_, e) -> e.location) lst) in
  match lst with
  | [] -> assert false
  | ((fld, _) :: _) as lst ->
    if not (OldUtils.injective fst lst) then
      Error.typing ~loc "Fields in a record must be distinct";
    begin match Tctx.infer_field fld with
    | None -> Error.typing ~loc "Unbound record field label %s" fld
    | Some (ty, (ty_name, fld_tys)) ->
        if List.length lst <> List.length fld_tys then
          Error.typing ~loc "The record of type %s has an incorrect number of fields" ty_name;
        let infer (fld, e) (ctx, constraints) =
          begin match OldUtils.lookup fld fld_tys with
          | None -> Error.typing ~loc "Unexpected field %s in a record of type %s" fld ty_name
          | Some fld_ty ->
              let e_ctx, e_ty, e_constraints = e.scheme in
              e_ctx @ ctx, Constraints.add_ty_constraint ~loc e_ty fld_ty constraints
          end
      in
      let ctx, constraints = List.fold_right infer lst ([], Constraints.empty) in
      {
        term = Record lst;
        scheme = Scheme.clean_ty_scheme ~loc (ctx, ty, constraints);
        location = loc;
      }
    end

let variant ?loc (lbl, e) =
    let loc = backup_location loc (match e with None -> [] | Some e -> [e.location]) in
    begin match Tctx.infer_variant lbl with
    | None -> Error.typing ~loc "Unbound constructor %s" lbl
    | Some (ty, arg_ty) ->
        let ty_sch = begin match e, arg_ty with
          | None, None -> ([], ty, Constraints.empty)
          | Some e, Some arg_ty ->
              let e_ctx, e_ty, e_constraints = e.scheme in
              let constraints = Constraints.add_ty_constraint ~loc e_ty arg_ty e_constraints in
              e_ctx, ty, constraints
          | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
          | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
        end
        in
        {
          term = Variant (lbl, e);
          scheme = ty_sch;
          location = loc
        }
    end

let lambda ?loc a =
  let loc = backup_location loc [a.location] in
  let ctx, (ty, drty), constraints = a.scheme in
  {
    term = Lambda a;
    scheme = Scheme.clean_ty_scheme ~loc (ctx, Type.Arrow (ty, drty), constraints);
    location = loc
  }

let effect ?loc eff signature =
  let loc = backup_location loc [] in
    match signature eff with
    | None -> Error.typing ~loc "Unbound effect %s" eff
    | Some (ty_par, ty_res) ->
      let r = Type.fresh_region_param () in
      let drt = {Type.ops = [eff, r]; Type.rest = Type.fresh_dirt_param ()} in
      let ty = Type.Arrow (ty_par, (ty_res, drt)) in
      let constraints = Constraints.add_full_region r Constraints.empty in
      {
        term = Effect eff;
        scheme = Scheme.clean_ty_scheme ~loc ([], ty, constraints);
        location = loc;
      }

let handler ?loc h signature =
    let loc = backup_location loc (
      [h.value_clause.location; h.finally_clause.location] @
      List.map (fun (_, a2) -> a2.location) h.effect_clauses
    ) in
    let drt_mid = Type.fresh_dirt () in
    let ty_mid = Type.fresh_ty () in

    let fold (eff, a2) (ctx, constraints) =
      begin match signature eff with
      | None -> Error.typing ~loc "Unbound effect %s in a handler" eff
      | Some (ty_par, ty_arg) ->
          let ctx_a, (ty_p, ty_k, drty_c), cnstrs_a = a2.scheme in
          ctx_a @ ctx,
          Constraints.list_union [constraints; cnstrs_a]
          |> Constraints.add_ty_constraint ~loc ty_par ty_p
          |> Constraints.add_ty_constraint ~loc (Type.Arrow (ty_arg, (ty_mid, drt_mid))) ty_k
          |> Constraints.add_dirty_constraint ~loc drty_c (ty_mid, drt_mid)
      end
    in
    let ctxs, constraints = List.fold_right fold h.effect_clauses ([], Constraints.empty) in

    let make_dirt op (ops_in, ops_out) =
      let r_in = Type.fresh_region_param () in
      let r_out = Type.fresh_region_param () in
      (op, r_in) :: ops_in, (op, r_out) :: ops_out
    in
    let ops_in, ops_out = List.fold_right make_dirt (OldUtils.uniq (List.map fst h.effect_clauses)) ([], []) in

    let ctx_val, (ty_val, drty_val), cnstrs_val = h.value_clause.scheme in
    let ctx_fin, (ty_fin, drty_fin), cnstrs_fin = h.finally_clause.scheme in

    let ty_in = Type.fresh_ty () in
    let drt_rest = Type.fresh_dirt_param () in
    let drt_in = {Type.ops = ops_in; Type.rest = drt_rest} in
    let drt_out = Type.fresh_dirt () in
    let ty_out = Type.fresh_ty () in

    let constraints =
      Constraints.list_union [constraints; cnstrs_val; cnstrs_fin]
      |> Constraints.add_dirt_constraint {Type.ops = ops_out; Type.rest = drt_rest} drt_mid
      |> Constraints.add_ty_constraint ~loc ty_in ty_val
      |> Constraints.add_dirty_constraint ~loc drty_val (ty_mid, drt_mid)
      |> Constraints.add_ty_constraint ~loc ty_mid ty_fin
      |> Constraints.add_dirt_constraint drt_mid drt_out
      |> Constraints.add_dirty_constraint ~loc drty_fin (ty_out, drt_out)

    in

    let ty_sch = (ctx_val @ ctx_fin @ ctxs, Type.Handler((ty_in, drt_in), (ty_out, drt_out)), constraints) in
    {
      term = Handler h;
      scheme = Scheme.clean_ty_scheme ~loc ty_sch;
      location = loc;
    }


let value ?loc e =
  let loc = backup_location loc [e.location] in
  let ctx, ty, constraints = e.scheme in
  {
    term = Value e;
    scheme = (ctx, (ty, Type.fresh_dirt ()), constraints);
    location = loc
  }

let match' ?loc e cases =
  let loc = backup_location loc (
    e.location :: List.map (fun a -> a.location) cases
  ) in
  let ctx_e, ty_e, cnstrs_e = e.scheme in
  let drty = Type.fresh_dirty () in
  let drty_sch = match cases with
  | [] ->
      let constraints = Constraints.add_ty_constraint ~loc ty_e Type.empty_ty cnstrs_e in
      (ctx_e, drty, constraints)
  | _::_ ->
      let fold a (ctx, constraints) =
        let ctx_a, (ty_p, drty_c), cnstrs_a = a.scheme in
        ctx_a @ ctx,
          Constraints.list_union [cnstrs_a; constraints]
          |> Constraints.add_ty_constraint ~loc:e.location ty_e ty_p
          |> Constraints.add_dirty_constraint ~loc:a.location drty_c drty
      in
      let ctx, constraints = List.fold_right fold cases (ctx_e, cnstrs_e) in
      (ctx, drty, constraints)
  in
  {
    term = Match (e, cases);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc
  }

let apply ?loc e1 e2 =
  let loc = backup_location loc [e1.location; e2.location] in
  let ctx_e1, ty_e1, cnstrs_e1 = e1.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.scheme in
  let drty = Type.fresh_dirty () in
  let constraints =
    Constraints.list_union [cnstrs_e1; cnstrs_e2]
    |> Constraints.add_ty_constraint ~loc ty_e1 (Type.Arrow (ty_e2, drty)) in
  let drty_sch = (ctx_e1 @ ctx_e2, drty, constraints) in
  {
    term = Apply (e1, e2);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let handle ?loc e c =
  let loc = backup_location loc [e.location; c.location] in
  let ctx_e, ty_e, cnstrs_e = e.scheme in
  let ctx_c, drty_c, cnstrs_c = c.scheme in
  let drty = Type.fresh_dirty () in
  let constraints =
    Constraints.list_union [cnstrs_e; cnstrs_c]
    |> Constraints.add_ty_constraint ~loc ty_e (Type.Handler (drty_c, drty)) in
  let drty_sch = (ctx_e @ ctx_c, drty, constraints) in
  {
    term = Handle (e, c);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let check ?loc c =
  let loc = backup_location loc [c.location] in
  {
    term = Check c;
    scheme = ([], (Type.unit_ty, Type.fresh_dirt ()), Constraints.empty);
    location = loc;
  }

let let' ?loc defs c =
  let loc = backup_location loc (
    List.fold_right (fun (p, c) locs -> p.location :: c.location :: locs) defs [c.location]
  ) in
  (* XXX Check for implicit sequencing *)
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (poly_tys, nonpoly_tys, ctx, chngs) =
    let ctx_p, ty_p, cnstrs_p = p.scheme in
    let ctx_c, drty_c, cnstrs_c = c.scheme in
    let poly_tys, nonpoly_tys =
      match c.term with
      | Value _ ->
          ctx_p @ poly_tys, nonpoly_tys
      | Apply _ | Match _ | Handle _ | Let _ | LetRec _ | Check _ ->
          poly_tys, ctx_p @ nonpoly_tys
    in
    poly_tys, nonpoly_tys, ctx_c @ ctx, [
      Scheme.dirty_less ~loc:c.location drty_c (ty_p, drt);
      Scheme.just cnstrs_p;
      Scheme.just cnstrs_c
    ] @ chngs
  in
  let poly_tys, nonpoly_tys, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.finalize_ty_scheme ~loc ctx ty chngs) poly_tys in
  let change (ctx_c, (ty_c, drt_c), cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx @ ctx_c) (ty_c, drt) ([
      Scheme.less_context ~loc nonpoly_tys;
      Scheme.dirt_less drt_c drt;
      Scheme.just cnstrs_c;
    ] @ chngs)
  in
  let change2 (ctx_c, drty_c, cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx_c) drty_c ([
      Scheme.remove_context ~loc nonpoly_tys;
      Scheme.just cnstrs_c
    ])
  in
  {
    term = Let (defs, c);
    scheme = change2 (change c.scheme);
    location = loc;
  }

let let_rec' ?loc defs c =
  let loc = backup_location loc (
    c.location :: List.map (fun (_, a) -> a.location) defs
  ) in
  let drt = Type.fresh_dirt () in
  let add_binding (x, a) (poly_tys, nonpoly_tys, ctx, chngs) =
    let ctx_a, (ty_p, drty_c), cnstrs_a = a.scheme in
    let poly_tys, nonpoly_tys = (x, Type.Arrow (ty_p, drty_c)) :: poly_tys, nonpoly_tys in
    poly_tys, nonpoly_tys, ctx_a @ ctx, [
      Scheme.just cnstrs_a
    ] @ chngs
  in
  let poly_tys, nonpoly_tys, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
  let chngs = Scheme.trim_context ~loc poly_tys :: chngs in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.finalize_ty_scheme ~loc ctx ty chngs) poly_tys in
  let change (ctx_c, (ty_c, drt_c), cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx @ ctx_c) (ty_c, drt) ([
      Scheme.dirt_less drt_c drt;
      Scheme.just cnstrs_c;
    ] @ chngs)
  in
  let change2 (ctx_c, drty_c, cnstrs_c) =
    Scheme.finalize_dirty_scheme ~loc (ctx_c) drty_c ([
      Scheme.remove_context ~loc nonpoly_tys;
      Scheme.just cnstrs_c
    ])
  in
  {
    term = LetRec (defs, c);
    scheme = change2 (change c.scheme);
    location = loc;
  }
