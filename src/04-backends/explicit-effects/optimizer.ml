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
  let exp' = optimize_expression' state exp in
  reduce_expression state exp'

and optimize_expression' state exp =
  match exp with
  | Term.Var _ | Term.Const _ -> exp
  | Term.Tuple exps -> Tuple (List.map (optimize_expression state) exps)
  | Term.Record flds -> Record (Assoc.map (optimize_expression state) flds)
  | Term.Variant (lbl, exp) -> Variant (lbl, optimize_expression state exp)
  | Term.Lambda abs -> Lambda (optimize_abstraction state abs)
  | Term.Effect _ -> exp
  | Term.Handler hnd -> Term.Handler (optimize_handler state hnd)
  | Term.CastExp (exp, coer) ->
      CastExp (optimize_expression state exp, optimize_ty_coercion state coer)
  | Term.LambdaTyCoerVar (w, coerty, exp) ->
      LambdaTyCoerVar (w, coerty, optimize_expression state exp)
  | Term.LambdaDirtCoerVar (d, coerty, exp) ->
      LambdaDirtCoerVar (d, coerty, optimize_expression state exp)
  | Term.ApplyTyCoercion (exp, tcoer) ->
      ApplyTyCoercion
        (optimize_expression state exp, optimize_ty_coercion state tcoer)
  | Term.ApplyDirtCoercion (exp, dcoer) ->
      ApplyDirtCoercion
        (optimize_expression state exp, optimize_dirt_coercion state dcoer)

and optimize_computation state cmp =
  let cmp' = optimize_computation' state cmp in
  reduce_computation state cmp'

and optimize_computation' state = function
  | Term.Value exp -> Term.Value (optimize_expression state exp)
  | Term.LetVal (exp, abs) ->
      Term.LetVal (optimize_expression state exp, optimize_abstraction state abs)
  | Term.LetRec (defs, cmp) -> Term.LetRec (defs, optimize_computation state cmp)
  | Term.Match (exp, drty, cases) ->
      Term.Match (optimize_expression state exp, drty, cases)
  | Term.Apply (exp1, exp2) ->
      Term.Apply (optimize_expression state exp1, optimize_expression state exp2)
  | Term.Handle (exp, cmp) ->
      Term.Handle (optimize_expression state exp, optimize_computation state cmp)
  | Term.Call (eff, exp, abs) ->
      Term.Call
        (eff, optimize_expression state exp, optimize_abstraction state abs)
  | Term.Op (eff, exp) -> Term.Op (eff, optimize_expression state exp)
  | Term.Bind (cmp, abs) ->
      Term.Bind (optimize_computation state cmp, optimize_abstraction state abs)
  | Term.CastComp (cmp, dtcoer) ->
      Term.CastComp
        (optimize_computation state cmp, optimize_dirty_coercion state dtcoer)

and optimize_handler state hnd =
  {
    Term.value_clause = optimize_abstraction state hnd.value_clause;
    Term.effect_clauses =
      Assoc.map (optimize_abstraction2 state) hnd.effect_clauses;
  }

and optimize_abstraction state (pat, ty, cmp) =
  (pat, ty, optimize_computation state cmp)

and optimize_abstraction2 state (pat1, pat2, cmp) =
  (pat1, pat2, optimize_computation state cmp)

and reduce_expression _state = function
  | Term.CastExp (exp, tcoer) when Constraint.is_trivial_ty_coercion tcoer ->
      exp
  | exp -> exp

and reduce_computation state = function
  | Term.CastComp (cmp, dtcoer) when Constraint.is_trivial_dirty_coercion dtcoer
    ->
      cmp
  | Term.CastComp (Term.Value exp, { term = tcoer, _; _ }) ->
      Term.Value (reduce_expression state (Term.CastExp (exp, tcoer)))
  | cmp -> cmp
