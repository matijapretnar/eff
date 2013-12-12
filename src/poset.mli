module type Vertex =
sig
  type t
  val compare : t -> t -> int
end

module Make (V : Vertex) :
sig
  type elt = V.t
  type t

  (** The empty graph. *)
  val empty : t

  (** Add an edge to the graph. *)
  val add_edge : elt -> elt -> t -> t

  val skeletons : t -> elt list list

  val get_prec : elt -> t -> elt list

  val map : (elt -> elt) -> t -> t

  val garbage_collect : elt list -> elt list -> t -> t

  val remove_skeleton : elt -> t -> t * elt list * (elt * elt) list

  val union : t -> t -> t
end
