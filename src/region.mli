type elt = Type.region_param
type t

type region_bound =
  | Without of Type.region_param * Type.region_param list
  | Instance of Type.instance_param

(** The empty graph. *)
val empty : t

val union : t -> t -> t

val subst : Type.substitution -> t -> t

val add_region_bound : elt -> region_bound list -> t -> t

val add_region_constraint : elt -> elt -> t -> t

val garbage_collect : elt list -> elt list -> t -> t

val pos_handled : elt list -> elt list -> t -> elt list

val print : non_poly:('a, 'b, Type.region_param) Trio.t -> t -> Format.formatter -> unit

