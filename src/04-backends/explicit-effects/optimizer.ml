open Utils

type state = unit

let initial_state = ()

let optimize_ty_coercion _state tcoer = tcoer

and optimize_dirt_coercion _state dcoer = dcoer

and optimize_dirty_coercion _state dtcoer = dtcoer

let rec optimize_expression state exp =
  let exp' = optimize_expression' state exp in
  reduce_expression state exp'

and optimize_expression' state exp =
  match exp with
  | Term.Var _ | Term.Const _ -> exp
  | Term.Tuple exps -> Tuple (List.map (optimize_expression state) exps)
  | Term.Record flds -> Record (Assoc.map (optimize_expression state) flds)
  | Term.Variant (lbl, exp) -> Variant (lbl, optimize_expression state exp)
  | Term.Lambda abs -> Lambda (optimize_abstraction_with_ty state abs)
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
      Term.LetVal
        (optimize_expression state exp, optimize_abstraction_with_ty state abs)
  | Term.LetRec (defs, cmp) -> Term.LetRec (defs, optimize_computation state cmp)
  | Term.Match (exp, drty, cases) ->
      Term.Match (optimize_expression state exp, drty, cases)
  | Term.Apply (exp1, exp2) ->
      Term.Apply (optimize_expression state exp1, optimize_expression state exp2)
  | Term.Handle (exp, cmp) ->
      Term.Handle (optimize_expression state exp, optimize_computation state cmp)
  | Term.Call (eff, exp, abs) ->
      Term.Call
        ( eff,
          optimize_expression state exp,
          optimize_abstraction_with_ty state abs )
  | Term.Op (eff, exp) -> Term.Op (eff, optimize_expression state exp)
  | Term.Bind (cmp, abs) ->
      Term.Bind (optimize_computation state cmp, optimize_abstraction state abs)
  | Term.CastComp (cmp, dtcoer) ->
      Term.CastComp
        (optimize_computation state cmp, optimize_dirty_coercion state dtcoer)

and optimize_handler state hnd =
  {
    Term.value_clause = optimize_abstraction_with_ty state hnd.value_clause;
    Term.effect_clauses =
      Assoc.map (optimize_abstraction2 state) hnd.effect_clauses;
  }

and optimize_abstraction state (pat, cmp) = (pat, optimize_computation state cmp)

and optimize_abstraction_with_ty state (pat, ty, cmp) =
  (pat, ty, optimize_computation state cmp)

and optimize_abstraction2 state (pat1, pat2, cmp) =
  (pat1, pat2, optimize_computation state cmp)

and reduce_expression _state = function
  | Term.CastExp (exp, Constraint.ReflTy _) -> exp
  | exp -> exp

and reduce_computation _state = function
  | Term.CastComp
      (cmp, Constraint.BangCoercion (Constraint.ReflTy _, Constraint.ReflDirt _))
    ->
      cmp
  | cmp -> cmp
