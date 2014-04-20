type t

(** The empty graph. *)
val empty : t

(** Add an edge to the graph. *)
val add_edge : Type.ty_param -> Type.ty_param -> t -> t

val skeletons : t -> Type.ty_param list list

val get_prec : Type.ty_param -> t -> Type.ty_param list

val map : (Type.ty_param -> Type.ty_param) -> t -> t

val garbage_collect : Type.ty_param list -> Type.ty_param list -> t -> t

val remove_skeleton : Type.ty_param -> t -> t * Type.ty_param list * (Type.ty_param * Type.ty_param) list

val union : t -> t -> t
