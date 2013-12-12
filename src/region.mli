type elt = Type.region_param
type t

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val subst : Type.substitution -> t -> t

val garbage_collect : elt list -> elt list -> t -> t

val pos_handled : elt list -> elt list -> t -> elt list

val add_region_constraint : elt -> elt -> t -> t

val add_handled_constraint : elt -> elt -> elt list -> t -> t

val add_instance_constraint : Type.instance_param -> elt -> t -> t

val print : non_poly:('a, 'b, Type.region_param) Trio.t -> t -> Format.formatter -> unit

