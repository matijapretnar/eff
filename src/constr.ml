(* Directed graphs of constraints. *)

(** Directed graphs represented as maps from vertices to sets of predcessors and successors. *)
module Make (Vertex : Map.OrderedType) :
sig
  type elt = Vertex.t
  type t

  (** The empty graph. *)
  val empty : t

  (** Add an edge to the graph. *)
  val add_edge : elt -> elt -> Common.position -> t -> t

  (** Remove a vertex from the graph. Return a new graph together with the predecessors
      and successors of the removed vertex. *)
  val remove_vertex : elt -> t -> (elt * Common.position) list * (elt * Common.position) list * t

  (** Fold over the edges of the graph. *)

  val fold : (elt -> elt -> Common.position -> 'a -> 'a) -> t -> 'a -> 'a
end =
struct
  type elt = Vertex.t

  module S = Set.Make(struct
    type t = Vertex.t * Common.position
    let compare = Pervasives.compare
  end)

  module G = Map.Make(Vertex)

  type t = (S.t * S.t) G.t

  let empty = G.empty

  let get x (g : t) =
    try G.find x g with Not_found -> (S.empty, S.empty)

  let add_edge x y pos (g : t) =
    let (inx, outx) = get x g in
    let (iny, outy) = get y g in
      G.add x (inx, S.add (y, pos) outx) (G.add y (S.add (x, pos) iny, outy) g)

  let remove_vertex x (g : t) =
    (* We must remove [x] as a key from [g], as well as an element of any in- our out-set *)
    let remove_x = S.filter (fun (y, _) -> x <> y) in
    let (inx, outx) = get x g in
      S.elements inx, S.elements outx,
      G.fold
        (fun y (iny, outy) g -> G.add y (remove_x iny, remove_x outy) g)
        (G.remove x g)
        G.empty

  let fold f grph acc =
    G.fold (fun x (_, outx) acc -> S.fold (fun (y, pos) acc -> f x y pos acc) outx acc) grph acc
end

module Ty = Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
end)

module Region = Make(struct
  type t = Type.region
  let compare = Pervasives.compare
end)

module Dirt = Make(struct
  type t = Type.dirt
  let compare = Pervasives.compare
end)

type t = {
  mutable ty_graph : Ty.t;
  mutable region_graph : Region.t;
  mutable dirt_graph : Dirt.t
}

let empty = {
  ty_graph = Ty.empty;
  region_graph = Region.empty;
  dirt_graph = Dirt.empty
}

let add_ty_edge g p1 p2 pos =
  g.ty_graph <-  Ty.add_edge p1 p2 pos g.ty_graph

let add_region_edge g p1 p2 pos =
  g.region_graph <-  Region.add_edge p1 p2 pos g.region_graph

let add_dirt_edge g p1 p2 pos =
  g.dirt_graph <-  Dirt.add_edge p1 p2 pos g.dirt_graph

let remove_ty g x =
  let (inx, outx, g') = Ty.remove_vertex x g.ty_graph in
    g.ty_graph <- g' ;
    (inx, outx)

let fold_ty f g acc = Ty.fold f g.ty_graph acc
let fold_region f g acc = Region.fold f g.region_graph acc
let fold_dirt f g acc = Dirt.fold f g.dirt_graph acc
