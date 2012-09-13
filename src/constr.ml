(* Directed graphs of constraints. *)

module type VERTEX =
sig
  type t
  val compare : t -> t -> int
  val print : t -> Format.formatter -> unit
end

(** Directed graphs represented as maps from vertices to sets of predcessors and successors. *)
module Make (Vertex : VERTEX) :
  (* XXX Change the [Vertex] signature so that [Common.position] is a parameter. 
     Also add printers for vertices to [Vertex] so that the module can export printing of a graph. *)
sig
  type elt = Vertex.t
  type t

  (** The empty graph. *)
  val empty : t

  (** Add an edge to the graph. *)
  val add_edge : elt -> elt -> Common.position -> t -> t

  (** Add an edge to the graph. *)
  val add_vertex : elt -> t -> t

  (** Remove a vertex from the graph. Return a new graph together with the predecessors
      and successors of the removed vertex. *)
  val remove_vertex : elt -> t -> (elt * Common.position) list * (elt * Common.position) list * t

  (** Fold over the edges of the graph. *)
  val fold_edges : (elt -> elt -> Common.position -> 'a -> 'a) -> t -> 'a -> 'a

  (** Fold over the vertices of the graph together with their in- and out-sets. *)
  val fold_vertices : (elt -> (elt * Common.position) list -> (elt * Common.position) list -> 'a -> 'a) -> t -> 'a -> 'a

  (** Create a transitive closure of a graph.  *)
  val transitive_closure : t -> t

  (** Filter edges of the graph. *)
  val filter_edges : (elt -> elt -> Common.position -> bool) -> t -> t

  val print : t -> Format.formatter -> unit
end =
struct
  type elt = Vertex.t

  module S = Set.Make(struct
    type t = Vertex.t * Common.position
    let compare (x, _) (y, _) = Vertex.compare x y
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

  let add_vertex x (g : t) =
    if G.mem x g then g else G.add x (S.empty, S.empty) g

  let remove_vertex x (g : t) =
    (* We must remove [x] as a key from [g], as well as an element of any in- our out-set *)
    let remove_x = S.filter (fun (y, _) -> x <> y) in
    let (inx, outx) = get x g in
      S.elements inx, S.elements outx,
      G.fold
        (fun y (iny, outy) g -> G.add y (remove_x iny, remove_x outy) g)
        (G.remove x g)
        G.empty

  let fold_edges f grph acc =
    G.fold (fun x (_, outx) acc -> S.fold (fun (y, pos) acc -> f x y pos acc) outx acc) grph acc

  let fold_vertices f grph acc =
    G.fold (fun x (inx, outx) acc -> f x (S.elements inx) (S.elements outx) acc) grph acc

  let filter_edges p grph =
    fold_edges (fun x y pos acc -> if p x y pos then add_edge x y pos acc else acc) grph G.empty

  let transitive_closure grph =
    let add_closure_edges x y pos closure =
      let (inx, outx) = get x closure
      and (iny, outy) = get y closure in
      let left = S.add (x, pos) (S.diff inx iny)
      and right = S.add (y, pos) (S.diff outy outx) in
        S.fold (fun (x', _) grph ->
          S.fold (fun (y', _) grph ->
            add_edge x' y' pos grph
            ) right grph
          ) left closure
    in
    fold_edges add_closure_edges grph G.empty

    let print grph ppf =
      fold_vertices
        (fun x inx outx () ->
          Print.print ppf "@[%t <= %t <= %t@];@."
            (Print.sequence "," Vertex.print (List.map fst inx))
            (Vertex.print x)
            (Print.sequence "," Vertex.print (List.map fst outx))
        )
        grph ()
end

module Ty = Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
  let print = Print.ty_param []
end)

module Region = Make(struct
  type t = Type.region
  let compare = Pervasives.compare
  let print = Print.region Trio.empty
end)

module Dirt = Make(struct
  type t = Type.dirt
  let compare = Pervasives.compare
  let print = Print.dirt Trio.empty
end)

type t = {
  mutable ty_graph : Ty.t;
  mutable region_graph : Region.t;
  mutable dirt_graph : Dirt.t
}

let empty () = {
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

let fold_ty f g acc = Ty.fold_edges f g.ty_graph acc
let fold_region f g acc = Region.fold_edges f g.region_graph acc
let fold_dirt f g acc = Dirt.fold_edges f g.dirt_graph acc

let print grph ppf =
  Print.print ppf "TYPES:@.%t@.REGIONS:@.%t@.DIRT:@.%t@." 
  (Ty.print grph.ty_graph) (Region.print grph.region_graph) (Dirt.print grph.dirt_graph)

let garbage_collect ty_p drt_p rgn_p grph =
  {
    ty_graph = Ty.filter_edges ty_p (Ty.transitive_closure grph.ty_graph);
    dirt_graph = Dirt.filter_edges drt_p (Dirt.transitive_closure grph.dirt_graph);
    region_graph = Region.filter_edges rgn_p (Region.transitive_closure grph.region_graph);
  }
