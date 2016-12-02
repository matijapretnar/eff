type t

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val list_union : t list -> t

val subst : Type.substitution -> t -> t

val expand_ty : t -> Type.ty -> Type.ty

val garbage_collect :
    (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t ->
    (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t ->
    t -> t

val add_ty_constraint : loc:Location.t -> Type.ty -> Type.ty -> t -> t

val skeletons : t -> Type.ty_param list list

val add_dirt_constraint : Type.dirt -> Type.dirt -> t -> t

val add_dirty_constraint : loc:Location.t -> Type.dirty -> Type.dirty -> t -> t

val add_region_param_constraint : Type.region_param -> Type.region_param -> t -> t

val add_full_region : Type.region_param -> t -> t

val non_empty_dirts : t -> Type.dirt_param list

val print : t -> Format.formatter -> unit
