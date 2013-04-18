module type Vertex =
sig
  type t
  val compare : t -> t -> int
end

module Make (V : Vertex) :
  (* XXX Change the [V] signature so that [Common.position] is a parameter. 
     Also add printers for vertices to [V] so that the module can export printing of a graph. *)
sig
  type elt = V.t
  type t

  (** The empty graph. *)
  val empty : t

  (** Add an edge to the graph. *)
  val add_edge : elt -> elt -> t -> t

  (** Add an edge to the graph. *)
  val add_vertex : elt -> t -> t
  val mem : elt -> t -> bool

  val keys : t -> elt list

  (** Remove a vertex from the graph. Return a new graph together with the predecessors
      and successors of the removed vertex. *)
  val remove_vertex : elt -> t -> elt list * elt list * t
  val get_succ : elt -> t -> elt list
  val get_prec : elt -> t -> elt list

  (** Fold over the edges of the graph. *)
  val fold_edges : (elt -> elt -> 'a -> 'a) -> t -> 'a -> 'a

  val union : t -> t -> t

  val map : (elt -> elt) -> t -> t

  val garbage_collect : elt list -> elt list -> t -> t

  (* val print : t -> Format.formatter -> unit *)
end
