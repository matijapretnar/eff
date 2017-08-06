type t

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val list_union : t list -> t

val subst : Params.substitution -> t -> t

val garbage_collect : Params.t -> Params.t -> t -> t

val add_ty_constraint : loc:Location.t -> Type.ty -> Type.ty -> t -> t

val skeletons : t -> Params.ty_param list list

val add_dirt_constraint : Type.dirt -> Type.dirt -> t -> t

val add_dirty_constraint : loc:Location.t -> Type.dirty -> Type.dirty -> t -> t

val add_region_param_constraint : Params.region_param -> Params.region_param -> t -> t

val add_full_region : Params.region_param -> t -> t

val add_full_dirt : Params.dirt_param -> t -> t
val tag_wildcard_dirt_ty : Type.ty -> t -> t
val tag_wildcard_dirt_dirty : Type.dirty -> t -> t

val is_pure : t -> Type.dirt -> bool
val is_surely_pure : t -> Type.dirt -> bool
val is_surely_pure_for_handler : t -> Type.dirt -> Common.effect list -> bool

val expand_ty : Type.ty -> Type.ty
val expand_dirt : Type.dirt -> Type.dirt

val non_empty_dirts : t -> Params.dirt_param list

val non_empty_regions : t -> Params.region_param list

val print : t -> Format.formatter -> unit
val expand_constraints : t -> t
