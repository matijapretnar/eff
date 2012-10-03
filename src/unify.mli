val unify_ty_scheme : pos:Common.position -> (Core.variable * Type.ty) list -> Type.ty -> (Type.t -> Type.t) list -> Type.ty_scheme
val unify_dirty_scheme : pos:Common.position -> (Core.variable * Type.ty) list -> (Type.instance_param list * Type.ty * Type.dirt_param) -> (Type.t -> Type.t) list -> Type.dirty_scheme
val normalize_ty_scheme : pos:Common.position -> Type.ty_scheme -> Type.ty_scheme
val normalize_dirty_scheme : pos:Common.position -> Type.dirty_scheme -> Type.dirty_scheme