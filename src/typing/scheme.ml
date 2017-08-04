type context = (Untyped.variable, Type.ty) Common.assoc
type 'a t = context * 'a * Unification.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t
type abstraction_scheme = (Type.ty * Type.dirty) t
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t

let simple ty = ([], ty, Unification.empty)

let add_to_context v ty (ctx, t, u) = (Common.update v ty ctx, t, u)

let get_type (ctx, ty, u) = ty

let refresh (ctx, ty, cnstrs) =
  let sbst = Params.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, (* Constraints.subst sbst *) cnstrs

let abstract ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  ([], (ty_p, drty_c), Unification.empty)
