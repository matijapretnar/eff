type context = (Untyped.variable, Type.ty) Common.assoc
type 'a t = context * 'a * Unification.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t

let refresh (ctx, ty, cnstrs) =
  let sbst = Params.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, (* Constraints.subst sbst *) cnstrs
