type t

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val subst : Type.substitution -> t -> t

val garbage_collect : Type.region_param list -> Type.region_param list -> t -> t

val pos_handled : Type.region_param list -> Type.region_param list -> t -> Type.region_param list

val add_region_constraint : Type.region_param -> Type.region_param -> Type.region_param list -> t -> t

val add_instance_constraint : Type.instance_param -> Type.region_param -> Type.region_param list -> t -> t

val print : non_poly:('a, 'b, Type.region_param) Trio.t -> t -> Format.formatter -> unit
