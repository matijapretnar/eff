(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type effect = Common.effect * (Type.ty * Type.ty)

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
  | PRecord of (Common.field, pattern) Common.assoc
  | PVariant of Common.label * pattern option
  | PConst of Const.t
  | PNonbinding

let rec pattern_vars p =
  match p.term with
    | PVar x -> [x]
    | PAs (p,x) -> x :: pattern_vars p
    | PTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
    | PRecord lst -> List.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
    | PVariant (_, None) -> []
    | PVariant (_, Some p) -> pattern_vars p
    | PConst _ -> []
    | PNonbinding -> []

let annotate t sch loc = {
  term = t;
  scheme = sch;
  location = loc;
}

(** Pure expressions *)
type expression = (plain_expression, Scheme.ty_scheme) annotation
and plain_expression =
  | Var of variable
  | BuiltIn of string
  | Const of Const.t
  | Tuple of expression list
  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler

  | Pure of computation

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

  | Call of effect * expression * abstraction
  | Bind of computation * abstraction
  | LetIn of expression * abstraction

(** Handler definitions *)
and handler = {
  effect_clauses : (effect, abstraction2) Common.assoc;
  value_clause : abstraction;
  finally_clause : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation, Scheme.abstraction_scheme) annotation

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation, Scheme.abstraction2_scheme) annotation

type toplevel = plain_toplevel * Location.t
and plain_toplevel =
  | Tydef of (Common.tyname, Params.t * Tctx.tydef) Common.assoc
  | TopLet of (pattern * computation) list * (variable * Scheme.ty_scheme) list
  | TopLetRec of (variable * abstraction) list * (variable * Scheme.ty_scheme) list
  | External of variable * Type.ty * string
  | DefEffect of effect * (Type.ty * Type.ty)
  | Computation of computation
  | Use of string
  | Reset
  | Help
  | Quit
  | TypeOf of computation


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

let value ?loc e =
  let loc = backup_location loc [e.location] in
  let ctx, ty, constraints = e.scheme in
  {
    term = Value e;
    scheme = (ctx, (ty, Type.fresh_dirt ()), constraints);
    location = loc
  }



let a22a a2 =
  let (p1, p2, c) = a2.term in
  let ctx1, ty1, cnstrs1 = p1.scheme
  and ctx2, ty2, cnstrs2 = p2.scheme in
  let p = {
    term = PTuple [p1; p2];
    scheme = (
      ctx1 @ ctx2,
      Type.Tuple [ty1; ty2],
      Constraints.union cnstrs1 cnstrs2
    );
    location = a2.location;
  } in
  abstraction ~loc:a2.location p c
let a2a2 a =
  match a.term with
  | ({term = PTuple [p1; p2]}, c) -> abstraction2 ~loc:a.location p1 p2 c
  | _ -> assert false

let rec refresh_pattern sbst p =
  let sbst', p' = refresh_pattern' sbst p.term in
  sbst', {p with term = p'}
and refresh_pattern' sbst = function
  | PVar x ->
      let x' = Variable.refresh x in
      Common.update x x' sbst, PVar x'
  | PAs (p, x) ->
      let x' = Variable.refresh x in
      let sbst, p' = refresh_pattern (Common.update x x' sbst) p in
      sbst, PAs (p', x')
  | PTuple ps ->
    let sbst, ps' =
      List.fold_right (fun p (sbst, ps') ->
        let sbst, p' = refresh_pattern sbst p in
        sbst, p' :: ps'
      ) ps (sbst, []) in
    sbst, PTuple ps'
  | PRecord flds ->
    let sbst, flds' =
      List.fold_right (fun (lbl, p) (sbst, flds') ->
        let sbst, p' = refresh_pattern sbst p in
        sbst, (lbl, p') :: flds'
      ) flds (sbst, []) in
    sbst, PRecord flds'
  | PVariant (lbl, None) ->
      sbst, PVariant (lbl, None)
  | PVariant (lbl, Some p) ->
      let sbst, p' = refresh_pattern sbst p in 
      sbst, PVariant (lbl, Some p')
  | (PConst _ | PNonbinding) as p -> sbst, p

let rec refresh_expr sbst e =
  {e with term = refresh_expr' sbst e.term}
and refresh_expr' sbst = function
  | (Var x) as e ->
      begin match Common.lookup x sbst with
      | Some x' -> Var x'
      | None -> e
      end
  | Pure c ->
      Pure (refresh_comp sbst c)
  | Lambda a ->
      Lambda (refresh_abs sbst a)
  | Handler h ->
      Handler (refresh_handler sbst h)
  | Tuple es ->
      Tuple (List.map (refresh_expr sbst) es)
  | Record flds ->
      Record (Common.assoc_map (refresh_expr sbst) flds)
  | Variant (lbl, e) ->
      Variant (lbl, Common.option_map (refresh_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
and refresh_comp sbst c =
  {c with term = refresh_comp' sbst c.term}
and refresh_comp' sbst = function
  | Bind (c1, c2) ->
      Bind (refresh_comp sbst c1, refresh_abs sbst c2)
  | LetIn (e, a) ->
      LetIn (refresh_expr sbst e, refresh_abs sbst a)
  | Let (li, c1) ->
      let sbst', li' = List.fold_right (fun (p, c) (sbst', li') ->
        (* sbst' is what will be used for c1, but for definitons c, we use sbst *)
        let sbst', p' = refresh_pattern sbst' p in
        sbst', (p', refresh_comp sbst c) :: li'
      ) li (sbst, []) in
      Let (li', refresh_comp sbst' c1)
  | LetRec (li, c1) ->
      let new_xs, sbst' = List.fold_right (fun (x, _) (new_xs, sbst') ->
        let x' = Variable.refresh x in
        x' :: new_xs, Common.update x x' sbst'
      ) li ([], sbst) in
      let li' =
        List.combine new_xs (List.map (fun (_, a) -> refresh_abs sbst' a) li)
      in
      LetRec (li', refresh_comp sbst' c1)
  | Match (e, li) ->
      Match (refresh_expr sbst e, List.map (refresh_abs sbst) li)
  | Apply (e1, e2) ->
      Apply (refresh_expr sbst e1, refresh_expr sbst e2)
  | Handle (e, c) ->
      Handle (refresh_expr sbst e, refresh_comp sbst c)
  | Check c ->
      Check (refresh_comp sbst c)
  | Call (eff, e, a) ->
      Call (eff, refresh_expr sbst e, refresh_abs sbst a)
  | Value e ->
      Value (refresh_expr sbst e)
and refresh_handler sbst h = {
    effect_clauses = Common.assoc_map (refresh_abs2 sbst) h.effect_clauses;
    value_clause = refresh_abs sbst h.value_clause;
    finally_clause = refresh_abs sbst h.finally_clause;
  }
and refresh_abs sbst a = 
  let (p, c) = a.term in
  let sbst, p' = refresh_pattern sbst p in
  {a with term = (p', refresh_comp sbst c)}
and refresh_abs2 sbst a2 =
  a2a2 @@ refresh_abs sbst @@ a22a @@ a2

let rec subst_expr sbst e =
  {e with term = subst_expr' sbst e.term}
and subst_expr' sbst = function
  | (Var x) as e ->
      begin match Common.lookup x sbst with
      | Some e' -> e'
      | None -> e
      end
  | Pure c ->
      Pure (subst_comp sbst c)
  | Lambda a ->
      Lambda (subst_abs sbst a)
  | Handler h ->
      Handler (subst_handler sbst h)
  | Tuple es ->
      Tuple (List.map (subst_expr sbst) es)
  | Record flds ->
      Record (Common.assoc_map (subst_expr sbst) flds)
  | Variant (lbl, e) ->
      Variant (lbl, Common.option_map (subst_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
and subst_comp sbst c =
  {c with term = subst_comp' sbst c.term}
and subst_comp' sbst = function
  | Bind (c1, c2) ->
      Bind (subst_comp sbst c1, subst_abs sbst c2)
  | LetIn (e, a) ->
      LetIn (subst_expr sbst e, subst_abs sbst a)
  | Let (li, c1) ->
      let li' = List.map (fun (p, c) ->
        (* XXX Should we check that p & sbst have disjoint variables? *)
        (p, subst_comp sbst c)
      ) li
      in
      Let (li', subst_comp sbst c1)
  | LetRec (li, c1) ->
      let li' = List.map (fun (x, a) ->
        (* XXX Should we check that x does not appear in sbst? *)
        (x, subst_abs sbst a)
      ) li
      in
      LetRec (li', subst_comp sbst c1)
  | Match (e, li) ->
      Match (subst_expr sbst e, List.map (subst_abs sbst) li)
  | Apply (e1, e2) ->
      Apply (subst_expr sbst e1, subst_expr sbst e2)
  | Handle (e, c) ->
      Handle (subst_expr sbst e, subst_comp sbst c)
  | Check c ->
      Check (subst_comp sbst c)
  | Call (eff, e, a) ->
      Call (eff, subst_expr sbst e, subst_abs sbst a)
  | Value e ->
      Value (subst_expr sbst e)
and subst_handler sbst h = {
    effect_clauses = Common.assoc_map (subst_abs2 sbst) h.effect_clauses;
    value_clause = subst_abs sbst h.value_clause;
    finally_clause = subst_abs sbst h.finally_clause;
  }
and subst_abs sbst a = 
  let (p, c) = a.term in
  (* XXX Should we check that p & sbst have disjoint variables? *)
  {a with term = (p, subst_comp sbst c)}
and subst_abs2 sbst a2 =
  a2a2 @@ subst_abs sbst @@ a22a @@ a2

let assoc_equal eq flds flds' : bool =
  let rec equal_fields flds =
    match flds with
      | [] -> true
      | (f, x) :: flds ->
          begin match Common.lookup f flds' with
          | Some x' when eq x x' -> equal_fields flds
          | _ -> false
          end
  in
  List.length flds = List.length flds' &&
  equal_fields flds

let rec make_equal_pattern eqvars p p' =
  make_equal_pattern' eqvars p.term p'.term
and make_equal_pattern' eqvars p p' =
  match p, p' with
  | PVar x, PVar x' -> Some ((x, x') :: eqvars)
  | PAs (p, x), PAs (p', x') ->
      Common.option_map (fun eqvars ->
        (x, x') :: eqvars
      ) (make_equal_pattern eqvars p p')
  | PTuple ps, PTuple ps' ->
      List.fold_right2 (fun p p' -> function
        | Some eqvars' -> make_equal_pattern eqvars' p p'
        | None -> None
      ) ps ps' (Some eqvars)
  | PConst cst, PConst cst' when Const.equal cst cst' -> Some eqvars
  | PNonbinding, PNonbinding -> Some eqvars
  | _, _ -> None

let rec alphaeq_expr eqvars e e' =
  alphaeq_expr' eqvars e.term e'.term
and alphaeq_expr' eqvars e e' =
  match e, e' with
  | Var x, Var y ->
     List.mem (x, y) eqvars ||  Variable.compare x y = 0
  | Lambda a, Lambda a' ->
      alphaeq_abs eqvars a a'
  | Handler h, Handler h' ->
      alphaeq_handler eqvars h h'
  | Tuple es, Tuple es' ->
      List.for_all2 (alphaeq_expr eqvars) es es'
  | Record flds, Record flds' ->
      assoc_equal (alphaeq_expr eqvars) flds flds'
  | Variant (lbl, None), Variant (lbl', None) ->
      lbl = lbl'
  | Variant (lbl, Some e), Variant (lbl', Some e') ->
      lbl = lbl' && alphaeq_expr eqvars e e'
  | BuiltIn f, BuiltIn f' ->
      f = f'
  | Const cst, Const cst' ->
      Const.equal cst cst'
  | Effect eff, Effect eff' ->
      eff = eff'
  | Pure c, Pure c' ->
      alphaeq_comp eqvars c c'
  | _, _ -> false
and alphaeq_comp eqvars c c' =
  alphaeq_comp' eqvars c.term c'.term
and alphaeq_comp' eqvars c c' =
  match c, c' with
  | Bind (c1, c2), Bind (c1', c2') ->
      alphaeq_comp eqvars c1 c1' && alphaeq_abs eqvars c2 c2'
  | LetIn (e, a), LetIn (e', a') ->
      alphaeq_expr eqvars e e' && alphaeq_abs eqvars a a'
  | Let (li, c1), Let (li', c1') ->
      let eqvars' = List.fold_right2 (fun (p, c) (p', c') -> function
        | None -> None
        | Some eqvars' ->
          begin match make_equal_pattern eqvars' p p' with
          | Some eqvars' when alphaeq_comp eqvars c c' -> Some eqvars'
          | _ -> None
          end
      ) li li' (Some eqvars) in
      begin match eqvars' with
      | None -> false
      | Some eqvars' -> alphaeq_comp eqvars' c1 c1'
      end
  | LetRec (li, c1), LetRec (li', c1') ->
      (* XXX Not yet implemented *)
      false
  | Match (e, li), Match (e', li') ->
      alphaeq_expr eqvars e e' && List.for_all2 (alphaeq_abs eqvars) li li'
  | Apply (e1, e2), Apply (e1', e2') ->
      alphaeq_expr eqvars e1 e1' && alphaeq_expr eqvars e2 e2'
  | Handle (e, c), Handle (e', c') ->
      alphaeq_expr eqvars e e' && alphaeq_comp eqvars c c'
  | Check c, Check c' ->
      alphaeq_comp eqvars c c'
  | Call (eff, e, a), Call (eff', e', a') ->
      eff = eff' && alphaeq_expr eqvars e e' && alphaeq_abs eqvars a a'
  | Value e, Value e' ->
      alphaeq_expr eqvars e e'
  | _, _ -> false
and alphaeq_handler eqvars h h' =
  assoc_equal (alphaeq_abs2 eqvars) h.effect_clauses h'.effect_clauses &&
  alphaeq_abs eqvars h.value_clause h'.value_clause &&
  alphaeq_abs eqvars h.finally_clause h'.finally_clause
and alphaeq_abs eqvars {term = (p, c)} {term = (p', c')} =
  match make_equal_pattern eqvars p p' with
  | Some eqvars' -> alphaeq_comp eqvars' c c'
  | None -> false
and alphaeq_abs2 eqvars a2 a2' =
  alphaeq_abs eqvars (a22a a2) (a22a a2')

(*pure abstract*)

let var ?loc x ty_sch =
  let loc = backup_location loc [] in
  {
    term = Var x;
    scheme = ty_sch;
    location = loc;
  }

let built_in ?loc x ty_sch =
  let loc = backup_location loc [] in
  {
    term = BuiltIn x;
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
    if not (Pattern.linear_record lst) then
      Error.typing ~loc "Fields in a record must be distinct";
    begin match Tctx.infer_field fld with
    | None -> Error.typing ~loc "Unbound record field label %s" fld
    | Some (ty, (ty_name, fld_tys)) ->
        if List.length lst <> List.length fld_tys then
          Error.typing ~loc "The record of type %s has an incorrect number of fields" ty_name;
        let infer (fld, e) (ctx, constraints) =
          begin match Common.lookup fld fld_tys with
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

let effect ?loc ((eff_name, (ty_par, ty_res)) as eff) =
  let loc = backup_location loc [] in
    let r = Params.fresh_region_param () in
    let drt = {Type.ops = [eff_name, r]; Type.rest = Params.fresh_dirt_param ()} in
    let ty = Type.Arrow (ty_par, (ty_res, drt)) in
    let constraints = Constraints.add_full_region r Constraints.empty in
    {
      term = Effect eff;
      scheme = Scheme.clean_ty_scheme ~loc ([], ty, constraints);
      location = loc;
    }

let handler ?loc h =
    let loc = backup_location loc (
      [h.value_clause.location; h.finally_clause.location] @
      List.map (fun (_, a2) -> a2.location) h.effect_clauses
    ) in
    let drt_mid = Type.fresh_dirt () in
    let ty_mid = Type.fresh_ty () in

    let fold ((_, (ty_par, ty_arg)), a2) (ctx, constraints) =
      let ctx_a, (ty_p, ty_k, drty_c), cnstrs_a = a2.scheme in
      ctx_a @ ctx,
      Constraints.list_union [constraints; cnstrs_a]
      |> Constraints.add_ty_constraint ~loc ty_par ty_p
      |> Constraints.add_ty_constraint ~loc (Type.Arrow (ty_arg, (ty_mid, drt_mid))) ty_k
      |> Constraints.add_dirty_constraint ~loc drty_c (ty_mid, drt_mid)
    in
    let ctxs, constraints = List.fold_right fold h.effect_clauses ([], Constraints.empty) in

    let make_dirt (eff, _) (effs_in, effs_out) =
      let r_in = Params.fresh_region_param () in
      let r_out = Params.fresh_region_param () in
      (eff, r_in) :: effs_in, (eff, r_out) :: effs_out
    in
    let effs_in, effs_out = List.fold_right make_dirt (Common.uniq (List.map fst h.effect_clauses)) ([], []) in

    let ctx_val, (ty_val, drty_val), cnstrs_val = h.value_clause.scheme in
    let ctx_fin, (ty_fin, drty_fin), cnstrs_fin = h.finally_clause.scheme in

    let ty_in = Type.fresh_ty () in
    let drt_rest = Params.fresh_dirt_param () in
    let drt_in = {Type.ops = effs_in; Type.rest = drt_rest} in
    let drt_out = Type.fresh_dirt () in
    let ty_out = Type.fresh_ty () in

    let constraints =
      Constraints.list_union [constraints; cnstrs_val; cnstrs_fin]
      |> Constraints.add_dirt_constraint {Type.ops = effs_out; Type.rest = drt_rest} drt_mid
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

let pure ?loc c =
  (* XXX We are just throwing away the dirt, but we should check that it is empty
     and maybe recompute the constraints, though that likely won't be necessary
     in case the dirt is pure *)
  let loc = backup_location loc [c.location] in
  let ctx, (ty, _), constraints = c.scheme in
  {
    term = Pure c;
    scheme = (ctx, ty, constraints);
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
      | Apply _ | Match _ | Handle _ | Let _ | LetRec _
      | Check _ | Bind _ | LetIn _ | Call _ ->
          poly_tys, ctx_p @ nonpoly_tys
    in
    poly_tys, nonpoly_tys, ctx_c @ ctx, [
      Scheme.dirty_less ~loc:c.location drty_c (ty_p, drt);
      Scheme.just cnstrs_p;
      Scheme.just cnstrs_c
    ] @ chngs
  in
  let poly_tys, nonpoly_tys, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
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

let bind ?loc c1 c2 =
  let loc = backup_location loc [c1.location; c2.location] in
  let ctx_c1, (ty_c1, drt_c1), constraints_c1 = c1.scheme
  and ctx_c2, (ty_p, (ty_c2, drt_c2)), constraints_c2 = c2.scheme in
  let drt = Type.fresh_dirt () in
  let constraints =
    Constraints.union constraints_c1 constraints_c2 |>
    Constraints.add_dirt_constraint drt_c1 drt |>
    Constraints.add_dirt_constraint drt_c2 drt |>
    Constraints.add_ty_constraint ~loc ty_c1 ty_p
  in
  {
    term = Bind (c1, c2);
    scheme = Scheme.clean_dirty_scheme ~loc (ctx_c1 @ ctx_c2, (ty_c2, drt), constraints);
    location = loc;
  }

let let_in ?loc e1 c2 =
  let loc = backup_location loc [e1.location; c2.location] in
  let ctx_e1, ty_e1, constraints_e1 = e1.scheme
  and ctx_c2, (ty_p, drty_c2), constraints_c2 = c2.scheme in
  let constraints =
    Constraints.union constraints_e1 constraints_c2 |>
    Constraints.add_ty_constraint ~loc ty_e1 ty_p
  in
  {
    term = LetIn (e1, c2);
    scheme = Scheme.clean_dirty_scheme ~loc (ctx_e1 @ ctx_c2, drty_c2, constraints);
    location = loc;
  }


let call ?loc ((eff_name, (ty_par, ty_res)) as eff) e a =
    let loc = backup_location loc [e.location; a.location] in
    let ctx_e, ty_e, constraints_e = e.scheme
    and ctx_a, (ty_a, drty_a), constraints_a = a.scheme in
    let r = Params.fresh_region_param () in
    let drt_eff = {Type.ops = [eff_name, r]; Type.rest = Params.fresh_dirt_param ()} in
    let ((ty_out, drt_out) as drty_out) = Type.fresh_dirty () in
    let constraints =
      Constraints.union constraints_e constraints_a
      |> Constraints.add_full_region r
      |> Constraints.add_ty_constraint ~loc:e.location ty_e ty_par
      |> Constraints.add_ty_constraint ~loc:a.location ty_res ty_a
      |> Constraints.add_dirt_constraint drt_eff drt_out
      |> Constraints.add_dirty_constraint ~loc drty_a drty_out
    in
    {
      term = Call (eff, e, a);
      scheme = Scheme.clean_dirty_scheme ~loc (ctx_e @ ctx_a, drty_out, constraints);
      location = loc;
    }

let pattern_match p e =
  let _, ty_e, constraints_e = e.scheme
  and _, ty_p, constraints_p = p.scheme in
  let constraints =
    Constraints.union constraints_e constraints_p |>
    Constraints.add_ty_constraint ~loc:e.location ty_e ty_p
  in
  ignore constraints;
  let rec extend_subst p e sbst =
    match p.term, e.term with
    | PVar x, e -> Common.update x e sbst
    | PAs (p, x), e' ->
        let sbst = extend_subst p e sbst in
          Common.update x e' sbst
    | PNonbinding, _ -> sbst
    | PTuple ps, Tuple es -> List.fold_right2 extend_subst ps es sbst
    | PRecord ps, Record es ->
        begin
          let rec extend_record ps es sbst =
            match ps with
              | [] -> sbst
              | (f, p) :: ps ->
                  let e = List.assoc f es in
                    extend_record ps es (extend_subst p e sbst)
          in
            try
              extend_record ps es sbst
            with Not_found -> Error.runtime ~loc:e.location "Incompatible records in substitution."
        end
    | PVariant (lbl, None), Variant (lbl', None) when lbl = lbl' -> sbst
    | PVariant (lbl, Some p), Variant (lbl', Some e) when lbl = lbl' ->
        extend_subst p e sbst
    | PConst c, Const c' when Const.equal c c' -> sbst
    | _, _ -> Error.runtime ~loc:e.location "Cannot substitute an expression in a pattern."
  in
  extend_subst p e []

let (@@@) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)
let (---) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)
let concat_vars vars = List.fold_right (@@@) vars ([], [])

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_expr e
  | Let (li, cf) ->
      let xs, vars = List.fold_right (fun (p, c) (xs, vars) ->
        pattern_vars p, free_vars_comp c @@@ vars
      ) li ([], ([], [])) in
      vars @@@ (free_vars_comp cf --- xs)
  | LetRec (li, c1) ->
      let xs, vars = List.fold_right (fun (x, a) (xs, vars) ->
        x :: xs, free_vars_abs a @@@ vars
      ) li ([], free_vars_comp c1) in
      vars --- xs
  | Match (e, li) -> free_vars_expr e @@@ concat_vars (List.map free_vars_abs li)
  | Apply (e1, e2) -> free_vars_expr e1 @@@ free_vars_expr e2
  | Handle (e, c1) -> free_vars_expr e @@@ free_vars_comp c1
  | Check c1 -> free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_expr e1 @@@ free_vars_abs a1
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
  | LetIn (e, a) -> free_vars_expr e @@@ free_vars_abs a
and free_vars_expr e =
  match e.term with
  | Var v -> ([], [v])
  | Pure c -> free_vars_comp c
  | Tuple es -> concat_vars (List.map free_vars_expr es)
  | Lambda a -> free_vars_abs a
  | Handler h -> free_vars_handler h
  | Record flds -> concat_vars (List.map (fun (_, e) -> free_vars_expr e) flds)
  | Variant (_, None) -> ([], [])
  | Variant (_, Some e) -> free_vars_expr e
  | (BuiltIn _ | Effect _ | Const _) -> ([], [])
and free_vars_handler h =
  free_vars_abs h.value_clause @@@
  free_vars_abs h.finally_clause @@@
  concat_vars (List.map (fun (_, a2) -> free_vars_abs2 a2) h.effect_clauses)
and free_vars_abs a =
  let (p, c) = a.term in
  let (inside, outside) = free_vars_comp c --- pattern_vars p in
  (inside @ outside, [])
and free_vars_abs2 a2 = free_vars_abs @@ a22a @@ a2

let occurrences x (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x = y) ys) in
  (count inside, count outside)

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let print_variable = Variable.print

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PVar x -> print "%t" (print_variable x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record print_pattern lst ppf
  | PVariant (lbl, None) when lbl = Common.nil -> print "[]"
  | PVariant (lbl, None) -> print "%s" lbl
  | PVariant ("(::)", Some ({ term = PTuple [p1; p2] })) ->
      print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.term with
  | Var x ->
      print "%t" (print_variable x)
  | BuiltIn s ->
      print "%s" s
  | Const c ->
      print "%t" (Const.print c)
  | Tuple lst ->
      Print.tuple print_expression lst ppf
  | Record lst ->
      Print.record print_expression lst ppf
  | Variant (lbl, None) ->
      print "%s" lbl
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%s %t" lbl (print_expression e)
  | Lambda a ->
      print ~at_level:2 "fun %t" (print_abstraction a)
  | Handler h ->
      print "{@[<hov> value_clause = (@[fun %t@]);@ finally_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]}"
      (print_abstraction h.value_clause) (print_abstraction h.finally_clause)
      (print_effect_clauses h.effect_clauses)
  | Effect eff ->
      print ~at_level:2 "effect %t" (print_effect eff)
  | Pure c ->
      print ~at_level:1 "pure %t" (print_computation ~max_level:0 c)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | Apply (e1, e2) ->
      print ~at_level:1 "%t@ %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Value e ->
      print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Match (e, []) ->
      print ~at_level:2 "(match %t with _ -> assert false)" (print_expression e)
  | Match (e, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e) (Print.cases print_abstraction lst)
  | Handle (e, c) ->
      print ~at_level:1 "handle %t %t" (print_expression ~max_level:0 e) (print_computation ~max_level:0 c)
  | Let (lst, c) ->
      print ~at_level:2 "%t" (print_multiple_bind (lst, c))
  | LetRec (lst, c) ->
      print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Check c' ->
      print ~at_level:1 "check %S %t" (Common.to_string Location.print c.location) (print_computation ~max_level:0 c')
  | Call (eff, e, a) ->
      print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Bind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]" (print_computation ~max_level:0 c1) (print_abstraction a)
  | LetIn (e, {term = (p, c)}) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t" (print_pattern p) (print_expression e) (print_computation c)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
      print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), {term = (p1, p2, c)}) :: cases ->
      print ~at_level:1 "| %t -> (fun %t %t -> %t) %t"
      (print_effect eff) (print_pattern p1) (print_pattern p2) (print_computation c) (print_effect_clauses cases)

and print_abstraction {term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

and print_pure_abstraction {term = (p, e)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_expression e)

and print_multiple_bind (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation c')
  | (p, c) :: lst ->
      Format.fprintf ppf "%t >> fun %t -> %t"
      (print_computation c) (print_pattern p) (print_multiple_bind (lst, c'))

and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_top_let_abstraction (p, c) ppf =
  match c.term with
  | Value e ->
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ ->
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a)
