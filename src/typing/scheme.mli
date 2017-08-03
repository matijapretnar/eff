type context = (Untyped.variable, Type.ty) Common.assoc
type 'a t = context * 'a * Unification.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t

val refresh : ty_scheme -> ty_scheme
