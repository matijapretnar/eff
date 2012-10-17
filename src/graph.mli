module type Vertex =
sig
  type t
  type bound
  val sup : bound -> bound -> bound
  val inf : bound -> bound -> bound
  val compare : t -> t -> int
  (* val print : t -> Format.formatter -> unit *)
end

module Make (V : Vertex) :
  (* XXX Change the [V] signature so that [Common.position] is a parameter. 
     Also add printers for vertices to [V] so that the module can export printing of a graph. *)
sig
  type elt = V.t
  type bound = V.bound
  type t

  (** The empty graph. *)
  val empty : t

  (** Add an edge to the graph. *)
  val add_edge : elt -> elt -> t -> t

  val add_lower_bound : elt -> V.bound -> t -> t
  val add_upper_bound : elt -> V.bound -> t -> t

  (** Add an edge to the graph. *)
  val add_vertex : elt -> t -> t

  (** Remove a vertex from the graph. Return a new graph together with the predecessors
      and successors of the removed vertex. *)
  val remove_vertex : elt -> t -> elt list * elt list * t

  (** Fold over the edges of the graph. *)
  val fold_edges : (elt -> elt -> 'a -> 'a) -> t -> 'a -> 'a

  (** Fold over the vertices of the graph together with their in- and out-sets. *)
  (* val fold_vertices : (elt -> (elt * Common.position) list -> (elt * Common.position) list -> bound -> bound -> 'a -> 'a) -> t -> 'a -> 'a *)

  val bounds : t -> (elt * V.bound option * V.bound option) list

  (** Filter edges of the graph. *)
  val filter_edges : (elt -> elt -> bool) -> t -> t

  val join : t -> t -> t
  val union : t -> t -> t

  val map : (elt -> elt) -> (bound -> bound) -> t -> t

  val collect : elt list -> elt list -> t -> t

  (* val print : t -> Format.formatter -> unit *)
end
