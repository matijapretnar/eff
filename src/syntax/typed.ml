open PPrint
(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t

type ('term, 'scheme) annotation = {
  term: 'term;
  scheme: 'scheme;
  location: Location.t;
}

type pattern = (variable Pattern.t, Scheme.ty_scheme) annotation

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
  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option
  | Lambda of abstraction
  | Effect of Common.effect
  | Handler of handler
  | PureLambda of pure_abstraction
  | PureApply of expression * expression

(** Impure computations *)
and computation = (plain_computation, Scheme.dirty_scheme) annotation
and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | While of computation * computation
  | For of variable * expression * expression * computation * bool
  | Apply of expression * expression
  | Handle of expression * computation
  | Check of computation
  
  | Call of Common.effect * expression * abstraction
  | Bind of computation * abstraction
  | LetIn of expression * abstraction

(** Handler definitions *)
and handler = {
  operations : (Common.effect, abstraction2) Common.assoc;
  value : abstraction;
  finally : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation, Scheme.abstraction_scheme) annotation

(** Pure abstractions that take a pattern and an expression instead of a computation. *)
and pure_abstraction = (pattern * expression, Scheme.pure_abstraction_scheme) annotation

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation, Scheme.abstraction2_scheme) annotation

let empty_dirt () = { Type.ops = []; Type.rest = Type.fresh_dirt_param () }

let abstraction ~loc p c : abstraction =
  {
    term = (p, c);
    scheme = Scheme.abstract ~loc p.scheme c.scheme;
    location = loc;
  }


let pure_abstraction ~loc p e : pure_abstraction =
  {
    term = (p, e);
    scheme = Scheme.pure_abstract ~loc p.scheme e.scheme;
    location = loc;
  }

let abstraction2 ~loc p1 p2 c =
  {
    term = (p1, p2, c);
    scheme = Scheme.abstract2 ~loc p1.scheme p2.scheme c.scheme;
    location = c.location;
  }


  (*pure abstract*)

let var ~loc x ty_sch =
  {
    term = Var x;
    scheme = ty_sch;
    location = loc;
  }

let const ~loc c =
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

let tuple ~loc es =
  let ctx, tys, constraints =
    List.fold_right (fun e (ctx, tys, constraints) ->
      let e_ctx, e_ty, e_constraints = e.scheme in
      e_ctx @ ctx, e_ty :: tys, Constraints.union e_constraints constraints
    ) es ([], [], Constraints.empty)
  in
  {
    term = Tuple es;
    scheme = Scheme.clean_ty_scheme ~loc (ctx, Type.Tuple tys, constraints);
    location = loc;
  }

let record ~loc = function
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

let variant ~loc (lbl, e) =
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

let lambda ~loc a =
  let ctx, (ty, drty), constraints = a.scheme in
  {
    term = Lambda a;
    scheme = Scheme.clean_ty_scheme ~loc (ctx, Type.Arrow (ty, drty), constraints);
    location = loc
  }

let pure_lambda ~loc a =
    let ctx, (ty1, ty2), constraints = a.scheme in
  {
    term = PureLambda a;
    scheme = Scheme.clean_ty_scheme ~loc (ctx, Type.PureArrow (ty2, ty2), constraints);
    location = loc
  }


let effect ~loc eff signature =
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

let handler ~loc h signature =
    let drt_mid = Type.fresh_dirt () in
    let ty_mid = Type.fresh_ty () in

    let fold (eff, a2) (ctx, constraints) =
      begin match signature eff with
      | None -> Error.typing ~loc "Unbound effect %s in a handler" eff
      | Some (ty_par, ty_arg) ->
          let ctx_a, (ty_p, ty_k, drty_c), cnstrs_a = a2.scheme in
          ctx_a @ ctx,
          constraints
          |> Constraints.union cnstrs_a
          |> Constraints.add_ty_constraint ~loc ty_par ty_p
          |> Constraints.add_ty_constraint ~loc (Type.Arrow (ty_arg, (ty_mid, drt_mid))) ty_k
          |> Constraints.add_dirty_constraint ~loc drty_c (ty_mid, drt_mid)
      end
    in
    let ctxs, constraints = List.fold_right fold h.operations ([], Constraints.empty) in

    let make_dirt op (ops_in, ops_out) =
      let r_in = Type.fresh_region_param () in
      let r_out = Type.fresh_region_param () in
      (op, r_in) :: ops_in, (op, r_out) :: ops_out
    in
    let ops_in, ops_out = List.fold_right make_dirt (Common.uniq (List.map fst h.operations)) ([], []) in

    let ctx_val, (ty_val, drty_val), cnstrs_val = h.value.scheme in
    let ctx_fin, (ty_fin, drty_fin), cnstrs_fin = h.finally.scheme in

    let ty_in = Type.fresh_ty () in
    let drt_rest = Type.fresh_dirt_param () in
    let drt_in = {Type.ops = ops_in; Type.rest = drt_rest} in
    let drt_out = Type.fresh_dirt () in
    let ty_out = Type.fresh_ty () in

    let constraints =
      constraints
      |> Constraints.union cnstrs_val
      |> Constraints.union cnstrs_fin
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


let value ~loc e =
  let ctx, ty, constraints = e.scheme in
  {
    term = Value e;
    scheme = (ctx, (ty, empty_dirt ()), constraints);
    location = loc
  }

let match' ~loc e cases =
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
          Constraints.add_ty_constraint ~loc:e.location ty_e ty_p (
          Constraints.add_dirty_constraint ~loc:a.location drty_c drty (
          Constraints.union cnstrs_a constraints))
      in
      let ctx, constraints = List.fold_right fold cases (ctx_e, cnstrs_e) in
      (ctx, drty, constraints)
  in
  {
    term = Match (e, cases);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc
  }

let while' ~loc c1 c2 =
  let ctx_c1, (ty_c1, drt_c1), cnstrs_c1 = c1.scheme in
  let ctx_c2, (ty_c2, drt_c2), cnstrs_c2 = c2.scheme in
  let drt = Type.fresh_dirt () in
  let drty_sch =
    (ctx_c1 @ ctx_c2, (Type.unit_ty, drt),
        Constraints.add_ty_constraint ~loc ty_c1 Type.bool_ty (
        Constraints.add_ty_constraint ~loc ty_c2 Type.unit_ty (
        Constraints.add_dirt_constraint drt_c1 drt (
        Constraints.add_dirt_constraint drt_c2 drt (
        Constraints.union cnstrs_c1 (
        cnstrs_c2
    )))))) in
  {
    term = While (c1, c2);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let for' ~loc i e1 e2 c up =
  let ctx_e1, ty_e1, cnstrs_e1 = e1.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.scheme in
  let ctx_c, (ty_c, drt_c), cnstrs_c = c.scheme in
  let drty_sch =
    (ctx_e1 @ ctx_e2 @ ctx_c, (Type.unit_ty, drt_c),
        Constraints.add_ty_constraint ~loc:e1.location ty_e1 Type.int_ty (
        Constraints.add_ty_constraint ~loc:e2.location ty_e2 Type.int_ty (
        Constraints.add_ty_constraint ~loc:c.location ty_c Type.unit_ty (
        Constraints.union cnstrs_e1 (
        Constraints.union cnstrs_e2 (
        cnstrs_c
    )))))) in
  {
    term = For (i, e1, e2, c, up);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }


let pure_apply ~loc e1 e2 =
  let ctx_e1, ty_e1, cnstrs_e1 = e1.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.scheme in
  let constraints = (Constraints.union cnstrs_e1 cnstrs_e2) in
  {
    term = PureApply (e1, e2);
    scheme = Scheme.clean_ty_scheme ~loc (ctx_e1 @ ctx_e2, Type.PureArrow (ty_e2, ty_e1), constraints);
    location = loc;
  }


let apply ~loc e1 e2 =
  let ctx_e1, ty_e1, cnstrs_e1 = e1.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.scheme in
  let drty = Type.fresh_dirty () in
  let constraints =
    Constraints.add_ty_constraint ~loc ty_e1 (Type.Arrow (ty_e2, drty)) (
    Constraints.union cnstrs_e1 cnstrs_e2) in
  let drty_sch = (ctx_e1 @ ctx_e2, drty, constraints) in
  {
    term = Apply (e1, e2);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let handle ~loc e c =
  let ctx_e, ty_e, cnstrs_e = e.scheme in
  let ctx_c, drty_c, cnstrs_c = c.scheme in
  let drty = Type.fresh_dirty () in
  let constraints =
    Constraints.add_ty_constraint ~loc ty_e (Type.Handler (drty_c, drty)) (
    Constraints.union cnstrs_e cnstrs_c) in
  let drty_sch = (ctx_e @ ctx_c, drty, constraints) in
  {
    term = Handle (e, c);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let check ~loc c =
  {
    term = Check c;
    scheme = ([], (Type.unit_ty, empty_dirt ()), Constraints.empty);
    location = loc;
  }

let let' ~loc defs c =
  (* XXX Check for implicit sequencing *)
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (poly_tys, nonpoly_tys, ctx, chngs) =
    let ctx_p, ty_p, cnstrs_p = p.scheme in
    let ctx_c, drty_c, cnstrs_c = c.scheme in
    let poly_tys, nonpoly_tys =
      match c.term with
      | Value _ ->
          ctx_p @ poly_tys, nonpoly_tys
      | Apply _ | Match _ | While _ | For _
      | Handle _ | Let _ | LetRec _ | Check _
      | Bind _ | LetIn _ ->
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

let let_rec' ~loc defs c =
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

let bind ~loc c1 c2 =
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

let let_in ~loc e1 c2 =
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


let (^+^) x y = x ^^ space ^^ y

let rec prettyE e =
  prettyE' e.term
and prettyE' e = match e with
  | Var x 
  -> pretty_var x
  | Const c 
  -> pretty_const c
  | Lambda a 
  -> parens (string "fun" ^+^ pretty_abstraction a)
  | Effect eff 
  -> parens (string "fun x -> apply_effect" ^+^ pretty_effect eff ^+^ string "x" ^+^ string "(fun y -> value y)")
  | Handler h 
  -> pretty_handler h
and prettyC c = 
   prettyC' c.term
and prettyC' c = match c with
   | Value e -> string "value" ^+^ parens (prettyE e)
   | LetIn (e,a) ->
      let (p, c2) = a.term in
      group (string "let*" ^+^ pretty_pattern p.term ^+^ string "=" ^+^ prettyE e ^^ break 1 ^^ 
                         string "in" ^+^ prettyC c2)
   | Bind (c1,a) ->
      let (p, c2) = a.term in
      parens (prettyC c1) ^+^ string ">>" ^+^ parens (string "fun" ^+^ pretty_pattern p.term ^+^ string "->" ^+^ prettyC c2)
(*   | Conditional (e,c1,c2) 
                   -> group (string "if" ^+^ parens (prettyE e) ^^ break 1 ^^
                               nest 2 (string "then" ^+^ parens (prettyC c1) ^^ break 1 ^^
                                       string "else" ^+^ parens (prettyC c2))) *)
  | Apply (e1, e2) -> parens (prettyE e1 ^+^ prettyE e2)
  | Handle (e, c)  -> 
    prefix 2 1 (prefix 2 1 (string "handle") (parens (prettyE e))) (parens (prettyC c))
(*   | Call (eff,e1,e2) 
  -> string "apply_effect*" ^+^ pretty_effect eff ^+^ prettyE e1 ^+^ pretty_abstraction e2 *)
  | LetRec _ -> failwith "Not implemented"
  (* | LetEffectIn (eff, c) -> group (string "let effect" ^+^ pretty_effect eff ^+^ string "in" ^+^ prettyC c) *)

and pretty_var x = string (Common.to_string (Variable.print) x)

and pretty_const c = string (Common.to_string (Const.print) c)

and pretty_abstraction a =
  let (p, c) = a.term in
  pretty_pattern p.term ^+^ string "->" ^+^ prettyC c

and pretty_pure_abstraction (v, e) =
  pretty_var v ^+^ string "->*" ^+^ prettyE e

and pretty_pattern p = match fst p with
  | Pattern.Var x -> pretty_var x
  (* Catch all case *)
  | _ -> string (Common.to_string Untyped.print_pattern p)

and pretty_h_effs cases  =  pretty_h_effs_aux cases
and pretty_h_effs_aux cases =
  match cases with
  | [] -> string "Nil"
  | (eff, a2) :: cases ->
    let (p, k, c) = a2.term in
    string "Cons" ^+^ 
       parens ( dquotes (string eff) ^^ comma ^+^ parens (string "fun" ^+^ pretty_pattern p.term ^+^ pretty_pattern k.term ^+^ string "->" ^+^ prettyC c) ^^ comma ^+^ pretty_h_effs_aux cases)

and pretty_effect eff = dquotes (string eff)

and pretty_handler h =
 braces (space ^^ prefix 3 1 (string "value = " ^^ parens (string "fun" ^+^ pretty_abstraction h.value) ^^ semi) 
                             (string "effect_cases = " ^^ pretty_h_effs h.operations))      

let printE et chan =
   let document = prettyE et ^^ hardline in
   ToChannel.pretty 1. 60 chan document

let printC ct chan =
   let document = prettyC ct ^^ hardline in
   ToChannel.pretty 1. 60 chan document
