type t

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val subst : Type.substitution -> t -> t

val garbage_collect :
    (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t ->
    (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t ->
    t -> t

val add_ty_constraint : Type.ty_param -> Type.ty_param -> t -> t

val remove_ty : Type.ty_param -> t -> Type.ty_param list * Type.ty_param list * t

val skeletons : t -> Type.ty_param list list

val add_dirt_constraint : Type.dirt_param -> Type.dirt_param -> t -> t

val remove_dirt : Type.dirt_param -> t -> Type.dirt_param list * Type.dirt_param list * t

val add_region_constraint : Type.region_param -> Type.region_param -> t -> t

val add_full_region : Type.region_param -> t -> t

val print : non_poly:(Type.ty_param, Type.dirt_param, Type.region_param) Trio.t -> t -> Format.formatter -> unit
