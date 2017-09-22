
(********************)
(* HELPER FUNCTIONS *)
(********************)

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc

(* Get the type of a constant *)
let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty

(**********************************)
(* ABSTRACTION SMART CONSTRUCTORS *)
(**********************************)

let abstraction ?loc p c : Typed.abstraction =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  {
    term = (p, c);
    scheme = Scheme.abstract ~loc p.scheme c.scheme;
    location = loc;
  }

let abstraction2 ?loc p1 p2 c : Typed.abstraction2 =
  let loc = backup_location loc [p1.Typed.location; p2.Typed.location; c.Typed.location] in
  {
    term = (p1, p2, c);
    scheme = Scheme.abstract2 ~loc p.scheme c.scheme;
    location = loc;
  }

(*********************************)
(* EXPRESSION SMART CONSTRUCTORS *)
(*********************************)

let var ?loc x sch =
  let loc = backup_location loc [] in
  let term = Typed.Var x in
  Typed.annotate term sch loc

let const ?loc c =
  let loc = backup_location loc [] in
  let term = Typed.Const c in
  let sch = Scheme.const c in
  Typed.annotate term sch loc

let lambda ?loc p c =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  let param_ty = Scheme.get_type p.Typed.scheme in
  let term = Typed.Lambda (p, param_ty, c) in
  let sch = Scheme.lambda ~loc p.Typed.scheme c.Typed.scheme in
  Typed.annotate term sch loc

let tuple ?loc es =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) es) in
  let term = Typed.Tuple (List.map (fun e -> e.Typed.scheme) es) in
  let sch = Scheme.tuple in
  Typed.annotate term sch loc

let effect ?loc ((eff_name, (ty_par, ty_res)) as eff) =
  let loc = backup_location loc [] in
  let sch = Scheme.effect ty_par ty_res eff_name in
  let term = Typed.Effect eff in
  Typed.annotate term sch loc

let handler ?loc effect_clauses value_clause =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) (effect_clauses :: value_clause)) in
  let term = Typed.Handler {
    effect_clauses=effect_clauses;
    value_clause=value_clause
  } in
  (* let sch = Scheme.handler effect_clauses value_clause in *)
  Typed.annotate term sch loc


(**********************************)
(* COMPUTATION SMART CONSTRUCTORS *)
(**********************************)

let value ?loc e =
  let loc = backup_location loc [e.Typed.location] in
  Typed.annotate (Typed.Value e) (Scheme.make_dirty e.Typed.scheme) loc

let apply ?loc e1 e2 =
  let loc = backup_location loc [e1.Typed.location; e2.Typed.location] in
  let ctx_e1, ty_e1, cnstrs_e1 = e1.Typed.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.Typed.scheme in
  let drty = Type.fresh_dirty () in
  let constraints = Unification.union cnstrs_e1 cnstrs_e2  in
  let constraints = Unification.add_ty_constraint ty_e1 (Type.Arrow (ty_e2, drty)) constraints in
  let drty_sch = (ctx_e1 @ ctx_e2, drty, constraints) in
  Typed.annotate (Typed.Apply (e1, e2)) drty_sch loc

let patmatch ?loc es cases =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) cases) in
  let ctx_e, ty_e, cnstrs_e = es.Typed.scheme in
  let drty = Type.fresh_dirty () in
  let drty_sch = match cases with
    | [] ->
      let constraints = Unification.add_ty_constraint ty_e Type.empty_ty cnstrs_e in
      (ctx_e, drty, constraints)
    | _::_ ->
      let fold a (ctx, constraints) =
        let ctx_a, (ty_p, drty_c), cnstrs_a = a.Typed.scheme in
        ctx_a @ ctx,
        Unification.list_union [cnstrs_a; constraints]
        |> Unification.add_ty_constraint ty_e ty_p
        |> Unification.add_dirty_constraint drty_c drty
      in
      let ctx, constraints = List.fold_right fold cases (ctx_e, cnstrs_e) in
      (ctx, drty, constraints)
  in
  let term = Typed.Match (es, cases) in
  Typed.annotate term drty_sch loc



(******************************)
(* PATTERN SMART CONSTRUCTORS *)
(******************************)

let pvar ?loc x =
  let loc = backup_location loc [] in
  let ty = Type.fresh_ty () in

  let scheme = Scheme.simple ty in
  let scheme = Scheme.add_to_context x ty scheme in

  let pattern = Typed.PVar x in
  Typed.annotate pattern scheme loc

let pconst ?loc const =
  let loc = backup_location loc [] in

  let ty = ty_of_const const in
  let scheme = Scheme.simple ty in

  let pat = Typed.PConst const in
  Typed.annotate pat scheme loc

let pnonbinding ?loc =
  let loc = backup_location loc [] in

  let ty = Type.fresh_ty () in
  let scheme = Scheme.simple ty in

  let pat = Typed.PNonbinding in
  Typed.annotate pat scheme loc

let pas ?loc p x =
  let loc = backup_location loc [p.Typed.location] in
  let pat = Typed.PAs (p, x) in

  let ty = Scheme.get_type p.Typed.scheme in
  let scheme = Scheme.add_to_context x ty p.Typed.scheme in

  Typed.annotate pat scheme loc

let ptuple ?loc ps =
  let loc = backup_location loc (List.map (fun p -> p.Typed.location) ps) in
  let infer p (ctx, tys, chngs) =
    let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
    ctx_p @ ctx, ty_p :: tys, Unification.union cnstrs_p chngs
  in
  let ctx, tys, chngs = List.fold_right infer ps ([], [], Unification.empty) in
  let ty = Type.Tuple tys in
  let scheme = Scheme.simple ty in
  let pat = Typed.PTuple ps in
  Typed.annotate pat scheme loc
