(* Directed graphs of constraints. *)

let compare_fst (x, _) (y, _) = Pervasives.compare x y

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
end =
struct
  type elt = Vertex.t

  module S = Set.Make(struct
    type t = Vertex.t * Common.position
    let compare = compare_fst
  end)

  module G = Map.Make(Vertex)

  type t = (S.t * S.t) G.t

  let empty = G.empty

  let get x (g : t) =
    try G.find x g with Not_found -> (S.empty, S.empty)

  let in_edges x g = fst (G.find x g)

  let out_edges x g = snd (G.find x g)

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
    (* XXX Get a student to implement this properly *)
    let closure_step grph =
      let added_new = ref false in
      let add x y pos grph =
        let (inx, outx) = get x grph in
        if S.mem (y, Common.Nowhere) outx then
          grph
        else begin
          added_new := true;
          let (iny, outy) = get y grph in
          G.add x (inx, S.add (y, pos) outx) (G.add y (S.add (x, pos) iny, outy) grph)
        end
      in
      let add_closure_edges x y pos closure =
        let (inx, _) = get x closure
        and (_, outy) = get y closure
        in
        let closure =
          S.fold (fun (x', _) grph -> add x' y pos grph) inx closure in
        S.fold (fun (y', _) grph -> add x y' pos grph) outy closure
      in
      fold_edges add_closure_edges grph grph, !added_new
    in
    let rec loop grph =
      let grph, b = closure_step grph in
      if b then loop grph else grph
    in
    loop grph

end

module Ty = Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
  let print = Print.ty_param []
end)

module Region = Make(struct
  type t = Type.region
  let compare = Pervasives.compare
  let print = Print.region ([],[],[])
end)

module Dirt = Make(struct
  type t = Type.dirt
  let compare = Pervasives.compare
  let print = Print.dirt ([],[],[])
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

let transitive_closure grph = {
  ty_graph = Ty.transitive_closure grph.ty_graph;
  dirt_graph = Dirt.transitive_closure grph.dirt_graph;
  region_graph = Region.transitive_closure grph.region_graph
}

let print_ty {ty_graph = grph} ppf =
  Ty.fold_vertices
    (fun x inx outx () ->
      Print.print ppf "@[%t <= %t <= %t@];@."
        (Print.sequence "," (Print.ty_param []) (List.map fst inx))
        (Print.ty_param [] x)
        (Print.sequence "," (Print.ty_param []) (List.map fst outx))
    )
    grph ()

let print_region {region_graph = grph} ppf =
  Region.fold_vertices
    (fun x inx outx () ->
      Print.print ppf "@[%t <= %t <= %t@];@."
        (Print.sequence "," (Print.region ([],[],[])) (List.map fst inx))
        (Print.region ([],[],[]) x)
        (Print.sequence "," (Print.region ([],[],[])) (List.map fst outx))
    )
    grph ()

let print_dirt {dirt_graph = grph} ppf =
  Dirt.fold_vertices
    (fun x inx outx () ->
      Print.print ppf "@[%t <= %t <= %t@];@. "
        (Print.sequence "," (Print.dirt ([],[],[])) (List.map fst inx))
        (Print.dirt ([],[],[]) x)
        (Print.sequence "," (Print.dirt ([],[],[])) (List.map fst outx))
    )
    grph ()

let print grph ppf =
  Print.print ppf "TYPES:@.%t@.REGIONS:@.%t@.DIRT:@.%t@." 
  (print_ty grph) (print_region grph) (print_dirt grph)

let garbage_collect ty_p drt_p rgn_p grph =
  (* grph *)
  {
    ty_graph = Ty.filter_edges ty_p (Ty.transitive_closure grph.ty_graph);
    dirt_graph = Dirt.filter_edges drt_p (Dirt.transitive_closure grph.dirt_graph);
    region_graph = Region.filter_edges rgn_p (Region.transitive_closure grph.region_graph);
  }
