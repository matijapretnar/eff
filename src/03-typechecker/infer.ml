open Utils
module TypeCheckerPrimitives = Primitives
open Language
module Untyped = UntypedSyntax

let identity_instantiation (params : Type.Params.t)
    (constraints : Constraints.t) =
  Substitution.
    {
      type_param_to_type_coercions =
        Constraints.TyConstraints.fold_expanded
          (fun _s _t1 _t2 w ty1 ty2 ->
            Type.TyCoercionParam.Map.add w
              (TyCoercion.tyCoercionVar w (ty1, ty2)))
          constraints.ty_constraints Type.TyCoercionParam.Map.empty;
      type_param_to_type_subs =
        params.ty_params |> Type.TyParam.Map.bindings
        |> List.map (fun (p, skel) -> (p, Type.tyParam p skel))
        |> Type.TyParam.Map.of_bindings;
      dirt_var_to_dirt_coercions =
        Constraints.DirtConstraints.fold_expanded
          (fun _d1 _d2 w _effs drt1 drt2 ->
            Type.DirtCoercionParam.Map.add w
              (DirtCoercion.dirtCoercionVar w (drt1, drt2)))
          constraints.dirt_constraints Type.DirtCoercionParam.Map.empty;
      dirt_var_to_dirt_subs =
        params.dirt_params |> Dirt.Param.Set.elements
        |> List.map (fun d -> (d, Dirt.no_effect d))
        |> Dirt.Param.Map.of_bindings;
      skel_param_to_skel_subs =
        params.skel_params |> Language.Skeleton.Param.Set.elements
        |> List.map (fun s -> (s, Language.Skeleton.Param s))
        |> Language.Skeleton.Param.Map.of_bindings;
    }

let fresh_instantiation cnstrs (params : Type.Params.t)
    (constraints : Constraints.t) =
  let _, subst = Substitution.of_parameters params in
  let add_dirt_constraint _d1 _d2 w _effs drt1 drt2 (subst, constraints) =
    let w' = Type.DirtCoercionParam.refresh w
    and drt1' = Substitution.apply_substitutions_to_dirt subst drt1
    and drt2' = Substitution.apply_substitutions_to_dirt subst drt2 in
    let coer' = DirtCoercion.dirtCoercionVar w' (drt1', drt2') in
    let subst' = Substitution.add_dirt_var_coercion w coer' subst
    and constraints' =
      UnresolvedConstraints.add_dirt_inequality (w', (drt1', drt2')) constraints
    in
    (subst', constraints')
  in
  let add_ty_constraint _s _t1 _t2 w ty1 ty2 (subst, constraints) =
    let w' = Type.TyCoercionParam.refresh w
    and ty1' = Substitution.apply_substitutions_to_type subst ty1
    and ty2' = Substitution.apply_substitutions_to_type subst ty2 in
    let coer' = TyCoercion.tyCoercionVar w' (ty1', ty2') in
    let subst' = Substitution.add_type_coercion w coer' subst
    and constraints' =
      UnresolvedConstraints.add_ty_inequality (w', (ty1', ty2')) constraints
    in
    (subst', constraints')
  in
  (subst, cnstrs)
  |> Constraints.TyConstraints.fold_expanded add_ty_constraint
       constraints.ty_constraints
  |> Constraints.DirtConstraints.fold_expanded add_dirt_constraint
       constraints.dirt_constraints

type state = {
  variables : TyScheme.t Term.Variable.Map.t;
  effects : Term.effect Effect.Map.t;
  type_definitions : TypeDefinitionContext.state;
}

let extend_poly_var x ty_scheme state =
  { state with variables = Term.Variable.Map.add x ty_scheme state.variables }

let extend_var x ty state = extend_poly_var x (TyScheme.monotype ty) state
let extend_vars vars state = Term.Variable.Map.fold extend_var vars state

(* Initial type inference state: everything is empty *)
let initial_state : state =
  {
    variables = Term.Variable.Map.empty;
    effects = Effect.Map.empty;
    type_definitions = TypeDefinitionContext.initial_state;
  }

(* Typecheck a list of things *)
let infer_many infer cnstrs xs =
  List.fold_right
    (fun x (xs', cnstrs) ->
      let x', cnstrs' = infer cnstrs x in
      (x' :: xs', cnstrs'))
    xs ([], cnstrs)

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

let rec infer_pattern state cnstrs pat =
  let pat', cnstrs = infer_pattern' ~loc:pat.at state cnstrs pat.it in
  (pat', cnstrs)

and infer_pattern' ~loc state cnstrs = function
  | Untyped.PVar x ->
      let alpha = Type.fresh_ty_with_fresh_skel () in
      (Term.pVar x alpha, cnstrs)
  | Untyped.PAnnotated (p, ty) ->
      let p', cnstrs' = infer_pattern state cnstrs p in
      ({ p' with ty }, UnresolvedConstraints.add_ty_equality (ty, p'.ty) cnstrs')
  | Untyped.PNonbinding ->
      let alpha = Type.fresh_ty_with_fresh_skel () in
      (Term.pNonbinding alpha, cnstrs)
  | Untyped.PConst c -> (Term.pConst c, cnstrs)
  | Untyped.PTuple ps ->
      let ps', cnstrs' = infer_many (infer_pattern state) cnstrs ps in
      let p = Term.pTuple ps' in
      (p, cnstrs')
  | Untyped.PVariant (lbl, p) -> (
      match
        (p, TypeDefinitionContext.infer_variant lbl state.type_definitions)
      with
      | None, (None, out_ty) -> (Term.pVariant (lbl, None) out_ty, cnstrs)
      | Some p, (Some in_ty, out_ty) ->
          let p', cnstrs' = infer_pattern state cnstrs p in
          ( Term.pVariant (lbl, Some p') out_ty,
            UnresolvedConstraints.add_ty_equality (in_ty, p'.ty) cnstrs' )
      | _ -> assert false)
  | Untyped.PAs (p, x) ->
      let p', cnstrs' = infer_pattern state cnstrs p in
      (Term.pAs (p', x), cnstrs')
  | Untyped.PRecord flds ->
      let hd_fld, _ = List.hd (Type.Field.Map.bindings flds) in
      let out_ty, (ty_name, fld_tys) =
        TypeDefinitionContext.infer_field hd_fld state.type_definitions
      in
      let infer_field cnstrs (fld, p) =
        let p', cnstrs' = infer_pattern state cnstrs p in
        match Type.Field.Map.find_opt fld fld_tys with
        | None ->
            Error.typing ~loc "Field %t does not belong to type %t"
              (Type.Field.print fld)
              (Language.TyName.print ty_name)
        | Some fld_ty ->
            ( (fld, p'),
              UnresolvedConstraints.add_ty_equality (fld_ty, p'.ty) cnstrs' )
      in
      let flds', cnstrs' =
        infer_many infer_field cnstrs (Effect.Map.bindings flds)
      in
      (Term.pRecord out_ty (Type.Field.Map.of_bindings flds'), cnstrs')

let cast_expression cnstrs e ty =
  let omega, cnstrs' = UnresolvedConstraints.fresh_ty_coer cnstrs (e.ty, ty) in
  (Term.castExp (e, omega), cnstrs')

let cast_computation cnstrs c dirty =
  let omega, cnstrs' =
    UnresolvedConstraints.fresh_dirty_coer cnstrs (c.ty, dirty)
  in
  (Term.castComp (c, omega), cnstrs')

let cast_abstraction cnstrs { term = pat, cmp; _ } dirty =
  let cmp', cnstrs' = cast_computation cnstrs cmp dirty in
  (Term.abstraction (pat, cmp'), cnstrs')

let full_cast_abstraction cnstrs { term = pat, cmp; _ } ty_in dirty_out =
  let x_pat, x_var = Term.fresh_variable "x" ty_in in
  let exp', cnstrs' = cast_expression cnstrs x_var pat.ty in
  let cmp', cnstrs'' = cast_computation cnstrs' cmp dirty_out in
  ( Term.abstraction (x_pat, Term.letVal (exp', Term.abstraction (pat, cmp'))),
    cnstrs'' )

(* ************************************************************************* *)
(*                             VALUE TYPING                                  *)
(* ************************************************************************* *)

let rec infer_expression state cnstrs exp =
  let exp', cnstrs' = infer_expression' state cnstrs exp.it in
  let resolved = Unification.unify ~loc:exp.at state.type_definitions cnstrs' in
  let exp' = Term.apply_sub_exp resolved.Constraints.substitution exp' in
  Print.debug "%t -> %t : %t / %t"
    (Untyped.print_expression exp)
    (Term.print_expression exp')
    (Type.print_ty exp'.ty)
    (UnresolvedConstraints.print cnstrs);
  (exp', UnresolvedConstraints.from_resolved resolved)

and infer_expression' state (cnstrs : UnresolvedConstraints.t) = function
  | Untyped.Var x ->
      let ty_scheme = Term.Variable.Map.find x state.variables in
      let subst, cnstrs' =
        fresh_instantiation cnstrs ty_scheme.TyScheme.params
          ty_scheme.constraints
      in
      (Term.poly_var x subst ty_scheme.ty, cnstrs')
  | Untyped.Const c -> (Term.const c, cnstrs)
  | Untyped.Annotated (e, ty) ->
      let e', cnstrs' = infer_expression state cnstrs e in
      let e'', cnstrs'' = cast_expression cnstrs' e' ty in
      (e'', cnstrs'')
  | Untyped.Tuple es ->
      let es, cnstrs' = infer_many (infer_expression state) cnstrs es in
      (Term.tuple es, cnstrs')
  | Untyped.Record flds ->
      let hd_fld, _ = List.hd (Type.Field.Map.bindings flds) in
      let out_ty, (ty_name, fld_tys) =
        TypeDefinitionContext.infer_field hd_fld state.type_definitions
      in
      let fold fld e (flds', cnstrs) =
        let e', cnstrs' = infer_expression state cnstrs e in
        match Type.Field.Map.find_opt fld fld_tys with
        | None ->
            Error.typing ~loc:e.at "Field %t does not belong to type %t"
              (Type.Field.print fld)
              (Language.TyName.print ty_name)
        | Some fld_ty ->
            let e'', cnstrs'' = cast_expression cnstrs' e' fld_ty in
            ((fld, e'') :: flds', cnstrs'')
      in
      let flds', cnstrs' = Type.Field.Map.fold fold flds ([], cnstrs) in
      (Term.record out_ty (Type.Field.Map.of_bindings flds'), cnstrs')
  | Untyped.Variant (lbl, mbe) -> (
      match
        (TypeDefinitionContext.infer_variant lbl state.type_definitions, mbe)
      with
      | (None, ty_out), None -> (Term.variant (lbl, None) ty_out, cnstrs)
      | (Some ty_in, ty_out), Some e ->
          let e', cnstrs' = infer_expression state cnstrs e in
          let castExp, cnstrs'' = cast_expression cnstrs' e' ty_in in
          (Term.variant (lbl, Some castExp) ty_out, cnstrs'')
      | _, _ -> assert false)
  | Untyped.Lambda abs ->
      let abs', cnstrs' = infer_abstraction state cnstrs abs in
      (Term.lambda abs', cnstrs')
  | Untyped.Effect eff ->
      let eff' = Effect.Map.find eff state.effects in
      let in_ty, out_ty = eff'.ty in
      let s = Effect.Set.singleton eff in
      let out_drty = (out_ty, Dirt.closed s) in
      let x_pat, x_var = Term.fresh_variable "x" in_ty
      and y_pat, y_var = Term.fresh_variable "y" out_ty in
      let ret, cnstrs' = cast_computation cnstrs (Term.value y_var) out_drty in
      let outVal =
        Term.lambda
          (Term.abstraction
             (x_pat, Term.call (eff', x_var, Term.abstraction (y_pat, ret))))
      in
      (outVal, cnstrs')
  | Untyped.Handler hand -> infer_handler state cnstrs hand

and infer_handler state cnstrs
    { Untyped.value_clause; effect_clauses; finally_clause } =
  let ty_mid = Type.fresh_ty_with_fresh_skel ()
  and ty_out = Type.fresh_ty_with_fresh_skel ()
  and drt_out = Dirt.fresh () in

  let dirty_mid = (ty_mid, drt_out) and dirty_out = (ty_out, drt_out) in

  let infer_effect_clause cnstrs (eff, abs2) =
    let eff' = Effect.Map.find eff state.effects in
    let ty_eff1, ty_eff2 = eff'.ty in
    let ty_cont = Type.arrow (ty_eff2, dirty_mid) in
    let { term = pat1, pat2, cmp; _ }, cnstrs' =
      infer_abstraction2 state cnstrs abs2
    in
    let pat1' = { pat1 with ty = ty_eff1 }
    and pat2' = { pat2 with ty = ty_cont } in
    let cnstrs'' =
      cnstrs'
      |> UnresolvedConstraints.add_ty_equality (pat1.ty, ty_eff1)
      |> UnresolvedConstraints.add_ty_equality (pat2.ty, ty_cont)
    in
    let cmp', cnstrs''' = cast_computation cnstrs'' cmp dirty_mid in
    let outExpr = (eff', Term.abstraction2 (pat1', pat2', cmp')) in
    (outExpr, cnstrs''')
  in

  let value_clause', cnstrs' = infer_abstraction state cnstrs value_clause in
  let effect_clauses', cnstrs'' =
    infer_many infer_effect_clause cnstrs' (Assoc.to_list effect_clauses)
  in
  let finally_clause', cnstrs''' =
    infer_abstraction state cnstrs'' finally_clause
  in

  let value_clause'', cnstrs'''' =
    cast_abstraction cnstrs''' value_clause' dirty_mid
  in
  let finally_clause'', cnstrs''''' =
    full_cast_abstraction cnstrs'''' finally_clause' ty_mid dirty_out
  in

  let drt_in =
    drt_out
    |> Dirt.add_effects (Term.handled_effects (Assoc.of_list effect_clauses'))
  in

  let handler =
    Term.handlerWithFinally
      (Term.handler_clauses value_clause''
         (Assoc.of_list effect_clauses')
         drt_in)
      finally_clause''
  in
  (handler, cnstrs''''')

(* ************************************************************************* *)
(*                          COMPUTATION TYPING                               *)
(* ************************************************************************* *)
and infer_computation state cnstrs cmp =
  let cmp', cnstrs' = infer_computation' ~loc:cmp.at state cnstrs cmp.it in
  let resolved = Unification.unify ~loc:cmp.at state.type_definitions cnstrs' in
  let cmp' = Term.apply_sub_comp resolved.Constraints.substitution cmp' in
  Print.debug "%t -> %t : %t / %t"
    (Untyped.print_computation cmp)
    (Term.print_computation cmp')
    (Type.print_dirty cmp'.ty)
    (UnresolvedConstraints.print cnstrs);
  (cmp', UnresolvedConstraints.from_resolved resolved)

(* Dispatch: Type inference for a plan computation *)
and infer_computation' ~loc state cnstrs = function
  | Untyped.Value exp ->
      let exp', cnstrs' = infer_expression state cnstrs exp in
      (Term.value exp', cnstrs')
  (* Nest a list of let-bindings *)
  | Let ([], c2) ->
      let c, cnstrs' = infer_computation state cnstrs c2 in
      (c, cnstrs')
  | Let ([ (pdef, c1) ], c2) ->
      let trgC1, cnstrs' = infer_computation state cnstrs c1 in
      let trgC2, cnstrs'' = infer_abstraction state cnstrs' (pdef, c2) in
      let ty1', (ty2, _) = trgC2.ty in
      let delta = Dirt.fresh () in
      let cresC1, cnstrs''' = cast_computation cnstrs'' trgC1 (ty1', delta) in
      let cresC2, cnstrs'''' = cast_abstraction cnstrs''' trgC2 (ty2, delta) in
      (Term.bind (cresC1, cresC2), cnstrs'''')
  | Let ((pat, c1) :: rest, c2) ->
      let subCmp = { it = Untyped.Let (rest, c2); at = c2.at } in
      infer_computation' ~loc state cnstrs (Untyped.Let ([ (pat, c1) ], subCmp))
  | LetRec (defs, c2) ->
      let defs', cnstrs' = infer_rec_definitions state cnstrs defs in
      let state' =
        List.fold_left
          (fun state (x, abs) -> extend_var x (Type.arrow abs.ty) state)
          state (Assoc.to_list defs')
      in
      let trgC2, cnstrs'' = infer_computation state' cnstrs' c2 in
      (Term.letRec (defs', trgC2), cnstrs'')
  | Match (exp, cases) ->
      let ty_in = Type.fresh_ty_with_fresh_skel ()
      and dirty_out = Type.fresh_dirty_with_fresh_skel () in
      let infer_case cnstrs case =
        let case', cnstrs' = infer_abstraction state cnstrs case in
        let ty_in', _ = case'.ty
        and case'', cnstrs'' = cast_abstraction cnstrs' case' dirty_out in
        (case'', UnresolvedConstraints.add_ty_equality (ty_in, ty_in') cnstrs'')
      in
      let cases', cnstrs' = infer_many infer_case cnstrs cases in
      let exp', cnstrs'' = infer_expression state cnstrs' exp in
      let exp'', cnstrs''' = cast_expression cnstrs'' exp' ty_in in
      (Term.match_ (exp'', cases') dirty_out, cnstrs''')
  | Apply (expr1, expr2) ->
      let expr1', cnstrs' = infer_expression state cnstrs expr1 in
      let expr2', cnstrs'' = infer_expression state cnstrs' expr2 in
      let outType = Type.fresh_dirty_with_fresh_skel () in
      let castexpr1, cnstrs''' =
        cast_expression cnstrs'' expr1' (Type.arrow (expr2'.ty, outType))
      in
      (Term.apply (castexpr1, expr2'), cnstrs''')
  | Handle (hand, cmp) ->
      let hand', cnstrs' = infer_expression state cnstrs hand in
      let cmp', cnstrs'' = infer_computation state cnstrs' cmp in
      let out_ty = Type.fresh_dirty_with_fresh_skel () in
      let castHand, cnstrs''' =
        cast_expression cnstrs'' hand' (Type.handler (cmp'.ty, out_ty))
      in
      (Term.handle (castHand, cmp'), cnstrs''')
  | Check cmp ->
      let cmp', cnstrs' = infer_computation state cnstrs cmp in
      (Term.check (loc, cmp'), cnstrs')

(* Typecheck a (potentially) recursive let *)
and infer_rec_definitions state cnstrs defs =
  let defs_with_fresh_types =
    List.map
      (fun (x, abs) ->
        let ty_in = Type.fresh_ty_with_fresh_skel () in
        let ty_out = Type.fresh_dirty_with_fresh_skel () in
        (x, abs, ty_in, ty_out))
      defs
  in
  let (state_extended_with_all_defs : state) =
    List.fold_left
      (fun state (f, _, ty_in, ty_out) ->
        extend_var f (Type.arrow (ty_in, ty_out)) state)
      state defs_with_fresh_types
  in
  let defs'', cnstrs' =
    infer_many
      (fun cnstrs (f, abs, ty_in, ty_out) ->
        let abs', cnstrs' =
          infer_abstraction state_extended_with_all_defs cnstrs abs
        in
        let abs'', cnstrs'' = full_cast_abstraction cnstrs' abs' ty_in ty_out in
        ((f, abs''), cnstrs''))
      cnstrs defs_with_fresh_types
  in
  (Assoc.of_list defs'', cnstrs')

and infer_abstraction state cnstrs (pat, cmp) :
    Term.abstraction * UnresolvedConstraints.t =
  let trgPat, cnstrs' = infer_pattern state cnstrs pat in
  let state' = extend_vars (Term.pattern_vars trgPat) state in
  let trgCmp, cnstrs'' = infer_computation state' cnstrs' cmp in
  (Term.abstraction (trgPat, trgCmp), cnstrs'')

and infer_abstraction2 state cnstrs (pat1, pat2, cmp) :
    Term.abstraction2 * UnresolvedConstraints.t =
  let trgPat1, cnstrs' = infer_pattern state cnstrs pat1 in
  let trgPat2, cnstrs'' = infer_pattern state cnstrs' pat2 in
  let state' =
    extend_vars
      (Term.Variable.Map.compatible_union
         (Term.pattern_vars trgPat1)
         (Term.pattern_vars trgPat2))
      state
  in
  let trgCmp, cnstrs''' = infer_computation state' cnstrs'' cmp in
  (Term.abstraction2 (trgPat1, trgPat2, trgCmp), cnstrs''')

(* ************************************************************************* *)
(* ************************************************************************* *)

let process_computation state comp =
  Print.debug "HER There";
  let comp', cnstrs =
    infer_computation state UnresolvedConstraints.empty comp
  in
  let resolved = Unification.unify ~loc:comp.at state.type_definitions cnstrs in
  let resolved =
    if !Config.simplify_coercions then
      ConstraintSimplifier.simplify_computation ~loc:comp.at
        state.type_definitions resolved comp'.ty
    else resolved
  in
  let cmp' = Term.apply_sub_comp resolved.substitution comp' in

  Print.debug "Inferred type: %t" (Type.print_dirty cmp'.ty);
  Print.debug "Full comp: %t" (Term.print_computation cmp');
  let params =
    match comp.it with
    | Language.UntypedSyntax.Value _ ->
        Type.Params.union
          (Type.free_params_dirty cmp'.ty)
          (Constraints.free_params resolved)
    | _ -> Type.Params.empty
  in
  Exhaust.check_computation state.type_definitions comp;
  (params, cmp', resolved)

let process_top_let ~loc state defs =
  Print.debug "TOPLET";
  let fold (pat, cmp) (state', defs) =
    let pat', cnstrs = infer_pattern state UnresolvedConstraints.empty pat in
    let cmp', cnstrs' = infer_computation state cnstrs cmp in
    let constraints =
      Unification.unify ~loc state.type_definitions
        (UnresolvedConstraints.add_ty_equality (pat'.ty, fst cmp'.ty) cnstrs')
    in
    Print.debug "Inferred type: %t" (Type.print_dirty cmp'.ty);
    Print.debug "Full comp: %t" (Term.print_computation cmp');
    let constraints =
      if !Config.simplify_coercions then
        ConstraintSimplifier.simplify_computation ~loc state.type_definitions
          constraints cmp'.ty
      else constraints
    in
    Print.debug "After optimization";
    let pat'', cmp'' =
      ( Term.apply_sub_pat constraints.substitution pat',
        Term.apply_sub_comp constraints.substitution cmp' )
    in
    Print.debug "Inferred type: %t" (Type.print_dirty cmp''.ty);
    Print.debug "Full comp: %t" (Term.print_computation cmp'');
    let vars' =
      Term.Variable.Map.map
        (Substitution.apply_sub_ty constraints.substitution)
        (Term.pattern_vars pat')
    in
    let params =
      match cmp.it with
      | Language.UntypedSyntax.Value _ ->
          Type.Params.union
            (Type.free_params_dirty cmp''.ty)
            (Constraints.free_params constraints)
      | _ -> Type.Params.empty
    in
    let state'' =
      Term.Variable.Map.fold
        (fun x ty state -> extend_poly_var x { params; constraints; ty } state)
        vars' state'
    in
    Exhaust.is_irrefutable state.type_definitions pat;
    Exhaust.check_computation state.type_definitions cmp;
    (state'', (pat'', params, constraints, cmp'') :: defs)
  in
  List.fold_right fold defs (state, [])

let process_top_let_rec ~loc state defs =
  Assoc.iter
    (fun (_, (p, c)) ->
      Exhaust.is_irrefutable state.type_definitions p;
      Exhaust.check_computation state.type_definitions c)
    defs;
  let defs', cnstrs =
    infer_rec_definitions state UnresolvedConstraints.empty (Assoc.to_list defs)
  in
  let constraints = Unification.unify state.type_definitions ~loc cnstrs in
  let constraints =
    if !Config.simplify_coercions then
      ConstraintSimplifier.simplify_top_let_rec ~loc state.type_definitions
        constraints
        (defs' |> Assoc.values_of |> List.map (fun abs -> abs.ty))
    else constraints
  in
  let defs =
    Assoc.map
      (Term.apply_substitutions_to_abstraction constraints.substitution)
      defs'
  in
  let defs_params = Term.free_params_definitions defs in
  let cnstrs_params = Constraints.free_params constraints in
  let params = Type.Params.union defs_params cnstrs_params in
  let state', defs' =
    Assoc.fold_right
      (fun (f, (abs : Term.abstraction)) (state, defs) ->
        let (ty_scheme : TyScheme.t) =
          TyScheme.{ params; constraints; ty = Type.arrow abs.ty }
        in
        let state' = extend_poly_var f ty_scheme state in
        (state', (f, (params, constraints, abs)) :: defs))
      defs (state, [])
  in
  let subst =
    List.map
      (fun (f, (params, constraints, abs)) ->
        let inst = identity_instantiation params constraints in
        (f, Term.poly_var f inst (Type.arrow abs.ty)))
      defs'
    |> Assoc.of_list
  in
  let defs'' =
    List.map
      (fun (f, (params, constraints, abs)) ->
        Print.debug "Inferred type: %t for %t" (Type.print_abs_ty abs.ty)
          (Term.print_abstraction abs);
        (f, (params, constraints, Term.subst_abs subst abs)))
      defs'
  in
  (state', Assoc.of_list defs'')

let add_type_definitions state type_definitions =
  {
    state with
    type_definitions =
      TypeDefinitionContext.extend_type_definitions type_definitions
        state.type_definitions;
  }

let process_def_effect eff eff_sig state =
  let eff' = { term = eff; ty = eff_sig } in
  ({ state with effects = Effect.Map.add eff eff' state.effects }, eff')

let load_primitive_effect state eff prim =
  process_def_effect eff
    (TypeCheckerPrimitives.primitive_effect_signature prim)
    state

let load_primitive_value state x prim =
  let ty = TypeCheckerPrimitives.primitive_value_type_scheme prim in
  extend_poly_var x ty state
