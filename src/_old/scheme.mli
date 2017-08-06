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
val region_param_less : Params.region_param -> Params.region_param -> change
val add_full_region : Params.region_param -> change
val just : Constraints.t -> change
val dirt_less : Type.dirt -> Type.dirt -> change
val ty_less : loc:Location.t -> Type.ty -> Type.ty -> change
val dirty_less : loc:Location.t -> Type.dirty -> Type.dirty -> change
val trim_context : loc:Location.t -> context -> change
val remove_context : loc:Location.t -> context -> change
val less_context : loc:Location.t -> context -> change
val collect_constraints : change list -> Constraints.t
val finalize_ty_scheme : loc:Location.t -> context -> Type.ty -> change list -> ty_scheme
val finalize_dirty_scheme : loc:Location.t -> context -> Type.dirty -> change list -> dirty_scheme
val clean_ty_scheme : loc:Location.t -> ty_scheme -> ty_scheme
val clean_dirty_scheme : loc:Location.t -> dirty_scheme -> dirty_scheme
val finalize_pattern_scheme : loc:Location.t -> context -> Type.ty -> change list -> ty_scheme
val add_to_top : loc:Location.t -> context -> Constraints.t -> (dirty_scheme -> dirty_scheme)
val beautify_ty_scheme : ty_scheme -> ty_scheme
val beautify_dirty_scheme : dirty_scheme -> dirty_scheme
val skeletons_non_poly_scheme : 'a t -> Params.ty_param list list * Params.t
val print_ty_scheme : ty_scheme -> Format.formatter -> unit
val print_dirty_scheme : dirty_scheme -> Format.formatter -> unit
val is_pure : ?loc:Location.t -> dirty_scheme -> bool
val is_surely_pure : ?loc:Location.t -> dirty_scheme -> bool
val is_surely_pure_for_handler : dirty_scheme -> Common.effect list -> bool
