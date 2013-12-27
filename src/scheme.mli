type context = (Syntax.variable, Type.ty) Common.assoc
type ty_scheme = context * Type.ty * Constraints.t
type dirty_scheme = context * Type.dirty * Constraints.t
type change

val refresh : ty_scheme -> ty_scheme

val region_param_less : Type.region_param -> Type.region_param -> change
val add_instance_constraint : Type.instance_param -> Type.region_param -> change
val add_handled_constraint : Type.region_param -> Type.region_param -> Type.region_param list -> change
val just : Constraints.t -> change
val dirt_less : pos:Common.position -> Type.dirt -> Type.dirt -> change
val ty_less : pos:Common.position -> Type.ty -> Type.ty -> change
val dirty_less : pos:Common.position -> Type.dirty -> Type.dirty -> change
val trim_context : pos:Common.position -> context -> change
val remove_context : pos:Common.position -> context -> change
val less_context : pos:Common.position -> context -> change
val finalize_ty_scheme : pos:Common.position -> context -> Type.ty -> change list -> ty_scheme
val finalize_dirty_scheme : pos:Common.position -> context -> Type.dirty -> change list -> dirty_scheme
val finalize_pattern_scheme : context -> Type.ty -> change list -> ty_scheme
val add_to_top : pos:Common.position -> context -> Constraints.t -> (dirty_scheme -> dirty_scheme)
val print_ty_scheme : ty_scheme -> Format.formatter -> unit
val print_dirty_scheme : dirty_scheme -> Format.formatter -> unit
