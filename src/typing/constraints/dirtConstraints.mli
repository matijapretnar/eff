type t

(** The empty graph. *)
val empty : t

(** Add an edge to the graph. *)
val add_edge : Type.dirt_param -> Type.dirt_param -> t -> t

val skeletons : t -> Type.dirt_param list list

val get_prec : Type.dirt_param -> t -> Type.dirt_param list

val map : (Type.dirt_param -> Type.dirt_param) -> t -> t

val garbage_collect : Type.dirt_param list -> Type.dirt_param list -> t -> t

val remove_skeleton : Type.dirt_param -> t -> t * Type.dirt_param list * (Type.dirt_param * Type.dirt_param) list

val union : t -> t -> t
