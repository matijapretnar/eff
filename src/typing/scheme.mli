type context = (Untyped.variable, Type.ty) Common.assoc
type 'a t = context * 'a * Constraints.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t
type abstraction_scheme = (Type.ty * Type.dirty) t
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t
type change

val refresh : ty_scheme -> ty_scheme
val simple : 'a -> 'a t
val abstract : loc:Location.t -> ty_scheme -> dirty_scheme -> abstraction_scheme
val abstract2 : loc:Location.t -> ty_scheme -> ty_scheme -> dirty_scheme -> abstraction2_scheme
val region_param_less : Type.region_param -> Type.region_param -> change
val add_full_region : Type.region_param -> change
val just : Constraints.t -> change
val dirt_less : Type.dirt -> Type.dirt -> change
val ty_less : loc:Location.t -> Type.ty -> Type.ty -> change
val dirty_less : loc:Location.t -> Type.dirty -> Type.dirty -> change
val trim_context : loc:Location.t -> context -> change
val remove_context : loc:Location.t -> context -> change
val less_context : loc:Location.t -> context -> change
val finalize_ty_scheme : loc:Location.t -> context -> Type.ty -> change list -> ty_scheme
val finalize_dirty_scheme : loc:Location.t -> context -> Type.dirty -> change list -> dirty_scheme
val clean_ty_scheme : loc:Location.t -> ty_scheme -> ty_scheme
val clean_dirty_scheme : loc:Location.t -> dirty_scheme -> dirty_scheme
val finalize_pattern_scheme : loc:Location.t -> context -> Type.ty -> change list -> ty_scheme
val add_to_top : loc:Location.t -> context -> Constraints.t -> (dirty_scheme -> dirty_scheme)
val normalize_context : loc:Location.t -> ty_scheme -> ty_scheme
val subst_ty_scheme : Type.substitution -> ty_scheme -> ty_scheme
val subst_dirty_scheme : Type.substitution -> dirty_scheme -> dirty_scheme
val pos_neg_ty_scheme : ty_scheme -> (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t * (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t
val pos_neg_dirtyscheme : dirty_scheme -> (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t * (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t
