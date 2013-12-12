type elt = Type.region_param
type t

(** The empty graph. *)
val empty : t

(** Add an edge to the graph. *)
val add_edge : elt -> elt -> t -> t

val get_succ : elt -> t -> elt list

(** Fold over the edges of the graph. *)
val fold_edges : (elt -> elt -> 'a -> 'a) -> t -> 'a -> 'a

val union : t -> t -> t

val map : (elt -> elt) -> t -> t

val garbage_collect : elt list -> elt list -> t -> t
