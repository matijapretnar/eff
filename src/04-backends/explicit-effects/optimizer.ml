open Utils

type state = unit

let initial_state = ()

let rec optimize_ty_coercion state (tcoer : Constraint.ty_coercion) =
  reduce_ty_coercion state
    { tcoer with term = optimize_ty_coercion' state tcoer.term }

and optimize_ty_coercion' state tcoer =
  match tcoer with
  | ReflTy _ -> tcoer
  | ArrowCoercion (tc, dc) ->
      ArrowCoercion
        (optimize_ty_coercion state tc, optimize_dirty_coercion state dc)
  | HandlerCoercion (dc1, dc2) ->
      HandlerCoercion
        (optimize_dirty_coercion state dc1, optimize_dirty_coercion state dc2)
  | TyCoercionVar _ -> tcoer
  | ApplyCoercion (v, lst) ->
      ApplyCoercion (v, List.map (optimize_ty_coercion state) lst)
  | TupleCoercion lst ->
      TupleCoercion (List.map (optimize_ty_coercion state) lst)
  | QualTyCoer (ct_ty, tc) -> QualTyCoer (ct_ty, optimize_ty_coercion state tc)
  | QualDirtCoer (ct_drt, tc) ->
      QualDirtCoer (ct_drt, optimize_ty_coercion state tc)

and optimize_dirt_coercion state (dcoer : Constraint.dirt_coercion) =
  reduce_dirt_coercion state
    { dcoer with term = optimize_dirt_coercion' state dcoer.term }

and optimize_dirt_coercion' state (dcoer : Constraint.dirt_coercion') =
  match dcoer with
  | ReflDirt _ | DirtCoercionVar _ | Empty _ -> dcoer
  | UnionDirt (s, dc) -> UnionDirt (s, optimize_dirt_coercion state dc)

and optimize_dirty_coercion state { term = tcoer, dcoer; _ } =
  Constraint.bangCoercion
    (optimize_ty_coercion state tcoer, optimize_dirt_coercion state dcoer)

and reduce_ty_coercion state ty_coer =
  { ty_coer with term = reduce_ty_coercion' state ty_coer.term }

and reduce_ty_coercion' _state = function
  | ArrowCoercion
      ( { term = ReflTy ty1; _ },
        { term = { term = ReflTy ty2; _ }, { term = ReflDirt drt; _ }; _ } ) ->
      ReflTy (Type.Arrow (ty1, (ty2, drt)))
  | tcoer -> tcoer

and reduce_dirt_coercion state drt_coer =
  { drt_coer with term = reduce_dirt_coercion' state drt_coer.term }

and reduce_dirt_coercion' _state = function
  | Empty drt when Type.is_empty_dirt drt -> ReflDirt drt
  | UnionDirt (effects, { term = ReflDirt drt; _ }) ->
      ReflDirt (Type.add_effects effects drt)
  | dcoer -> dcoer

let rec optimize_expression state exp =
  Print.debug "EXP: %t : %t" (Term.print_expression exp) (Type.print_ty exp.ty);
  let exp' = optimize_expression' state exp in
  Print.debug "EXP': %t : %t"
    (Term.print_expression exp')
    (Type.print_ty exp'.ty);
  assert (Type.types_are_equal exp.ty exp'.ty);
  let exp'' = reduce_expression state exp' in
  Print.debug "EXP'': %t : %t"
    (Term.print_expression exp'')
    (Type.print_ty exp''.ty);
  assert (Type.types_are_equal exp'.ty exp''.ty);
  exp''

and optimize_expression' state exp =
  match exp.term with
  | Term.Var _ | Term.Const _ -> exp
  | Term.Tuple exps -> Term.tuple (List.map (optimize_expression state) exps)
  | Term.Record flds -> Term.record (Assoc.map (optimize_expression state) flds)
  | Term.Variant (lbl, arg) ->
      Term.variant (lbl, optimize_expression state arg) exp.ty
  | Term.Lambda abs -> Term.lambda (optimize_abstraction state abs)
  | Term.Effect _ -> exp
  | Term.Handler hnd -> Term.handler (optimize_handler state hnd)
  | Term.CastExp (exp, coer) ->
      Term.castExp
        (optimize_expression state exp, optimize_ty_coercion state coer)
  | Term.LambdaTyCoerVar (w, exp) ->
      Term.lambdaTyCoerVar (w, optimize_expression state exp)
  | Term.LambdaDirtCoerVar (d, exp) ->
      Term.lambdaDirtCoerVar (d, optimize_expression state exp)
  | Term.ApplyTyCoercion (exp, tcoer) ->
      Term.applyTyCoercion
        (optimize_expression state exp, optimize_ty_coercion state tcoer)
  | Term.ApplyDirtCoercion (exp, dcoer) ->
      Term.applyDirtCoercion
        (optimize_expression state exp, optimize_dirt_coercion state dcoer)

and optimize_computation state cmp =
  Print.debug "CMP: %t" (Term.print_computation cmp);
  let cmp' = optimize_computation' state cmp in
  Print.debug "CMP': %t" (Term.print_computation cmp');
  assert (Type.dirty_types_are_equal cmp.ty cmp'.ty);
  let cmp'' = reduce_computation state cmp' in
  Print.debug "CMP'': %t" (Term.print_computation cmp'');
  assert (Type.dirty_types_are_equal cmp'.ty cmp''.ty);
  cmp''

and optimize_computation' state cmp =
  match cmp.term with
  | Term.Value exp -> Term.value (optimize_expression state exp)
  | Term.LetVal (exp, abs) ->
      Term.letVal (optimize_expression state exp, optimize_abstraction state abs)
  | Term.LetRec (defs, cmp) -> Term.letRec (defs, optimize_computation state cmp)
  | Term.Match (exp, cases) ->
      Term.match_
        ( optimize_expression state exp,
          List.map (optimize_abstraction state) cases )
        cmp.ty
  | Term.Apply (exp1, exp2) ->
      Term.apply (optimize_expression state exp1, optimize_expression state exp2)
  | Term.Handle (exp, cmp) ->
      Term.handle (optimize_expression state exp, optimize_computation state cmp)
  | Term.Call (eff, exp, abs) ->
      Term.call
        (eff, optimize_expression state exp, optimize_abstraction state abs)
  | Term.Op (eff, exp) -> Term.op (eff, optimize_expression state exp)
  | Term.Bind (cmp, abs) ->
      Term.bind (optimize_computation state cmp, optimize_abstraction state abs)
  | Term.CastComp (cmp, dtcoer) ->
      Term.castComp
        (optimize_computation state cmp, optimize_dirty_coercion state dtcoer)

and optimize_handler state hnd =
  {
    hnd with
    term =
      {
        Term.value_clause = optimize_abstraction state hnd.term.value_clause;
        Term.effect_clauses =
          Assoc.map (optimize_abstraction2 state) hnd.term.effect_clauses;
      };
  }

and optimize_abstraction state abs =
  { abs with term = optimize_abstraction' state abs.term }

and optimize_abstraction' state (pat, cmp) =
  (pat, optimize_computation state cmp)

and optimize_abstraction2 state (pat1, pat2, cmp) =
  (pat1, pat2, optimize_computation state cmp)

and reduce_expression _state expr =
  match expr.term with
  | Term.CastExp (exp, tcoer) when Constraint.is_trivial_ty_coercion tcoer ->
      exp
  | _ -> expr

and reduce_computation _state comp =
  match comp.term with
  | Term.CastComp (cmp, dtcoer) when Constraint.is_trivial_dirty_coercion dtcoer
    ->
      cmp
  | _ -> comp
