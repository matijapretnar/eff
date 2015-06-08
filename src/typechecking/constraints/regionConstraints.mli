type t

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val subst : Type.substitution -> t -> t

val garbage_collect : Type.region_param list -> Type.region_param list -> t -> t

val add_region_constraint : Type.region_param -> Type.region_param -> t -> t

val add_full_region : Type.region_param -> t -> t

val print : non_poly:('a, 'b, Type.region_param) Trio.t -> t -> Format.formatter -> unit
