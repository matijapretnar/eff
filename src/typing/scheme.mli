type context = (Syntax.variable, Type.ty) Common.assoc
type ty_scheme = context * Type.ty * Constraints.t
type dirty_scheme = context * Type.dirty * Constraints.t
type change

val refresh : ty_scheme -> ty_scheme

val region_param_less : Type.region_param -> Type.region_param -> change
val add_full_region : Type.region_param -> change
val just : Constraints.t -> change
val dirt_less : loc:Location.t -> Type.dirt -> Type.dirt -> change
val ty_less : loc:Location.t -> Type.ty -> Type.ty -> change
val dirty_less : loc:Location.t -> Type.dirty -> Type.dirty -> change
val trim_context : loc:Location.t -> context -> change
val remove_context : loc:Location.t -> context -> change
val less_context : loc:Location.t -> context -> change
val finalize_ty_scheme : loc:Location.t -> context -> Type.ty -> change list -> ty_scheme
val finalize_dirty_scheme : loc:Location.t -> context -> Type.dirty -> change list -> dirty_scheme
val finalize_pattern_scheme : context -> Type.ty -> change list -> ty_scheme
val add_to_top : loc:Location.t -> context -> Constraints.t -> (dirty_scheme -> dirty_scheme)
val print_ty_scheme : ty_scheme -> Format.formatter -> unit
val print_dirty_scheme : dirty_scheme -> Format.formatter -> unit
