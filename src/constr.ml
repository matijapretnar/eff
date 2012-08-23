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

  (** Compress arcs of variables in a graph. Ok, we know this comment is cryptic. *)
  val compress : (elt -> bool) -> t -> t * (elt * elt) list

  (** Create a transitive closure of a graph.  *)
  val transitive_closure : t -> t

  (** Filter edges of the graph. *)
  val filter_edges : (elt -> elt -> Common.position -> bool) -> t -> t
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

  let compress is_var grph =
    let get_arc x0 grph =
      (* Get the predecessor arc on which [x] lives, assuming [is_var x = true]. *)
      let rec get_arc_prec x grph =
        let inx = in_edges x grph in
          if S.cardinal inx <> 1
          then [x]
          else
            let (y, _) = S.choose inx in
            let is_ok = y <> x0 && is_var y && (S.cardinal (out_edges y grph) = 1) in
            x :: (if is_ok then get_arc_prec y grph else [])
      in
      (* Get the successor arc on which [x] lives, assuming [is_var x = true]. *)
      let rec get_arc_succ x grph =
        let outx = out_edges x grph in
        (* Print.debug "get_arc_succ %t [%t]" (Vertex.print x) (Print.sequence "" Vertex.print (List.map fst (S.elements outx))) ; *)
          if S.cardinal outx <> 1
          then [x]
          else
            let (y, _) = S.choose outx in
            let is_ok = y <> x0 && is_var y && (S.cardinal (in_edges y grph) = 1) in
            x :: (if is_ok then get_arc_succ y grph else [])
      in
        if is_var x0 then
          let prec = List.tl (get_arc_prec x0 grph) in
          let succ = get_arc_succ x0 grph in
          (* Print.debug "FOUND PRECARC FROM %t: (%t)" (Vertex.print x0) (Print.sequence "<-" Vertex.print prec) ; *)
          (* Print.debug "FOUND SUCARC FROM %t: (%t)" (Vertex.print x0) (Print.sequence "->" Vertex.print succ) ; *)
            List.rev_append prec succ
        else
          [x0]
    in
    (* List of points to be removed (and where to reconnect edges) *)
    let lst =
      G.fold
        (fun x _ lst -> 
          if List.mem_assoc x lst then lst
          else
            let arc = get_arc x grph in
            let y = List.hd arc in
              List.fold_left (fun lst x -> (x,y) :: lst) lst arc)
        grph []
    in
    let grph =
      G.fold
        (fun x (inx, _) grph ->
          let y = List.assoc x lst in
            if x <> y
            then grph
            else
              S.fold (fun (z, pos) grph -> add_edge (List.assoc z lst) y pos grph) inx (add_vertex y grph)
        )
        grph G.empty
    in
      grph, List.filter (fun (x, y) -> x <> y) lst

  let transitive_closure grph =
    let add_edge x y pos closure =
      let (inx, _) = get x closure
      and (_, outy) = get y closure
      in
      let closure =
        S.fold (fun (x', _) grph -> add_edge x' y pos grph) inx closure in
      let closure =
        S.fold (fun (y', _) grph -> add_edge x y' pos grph) outy closure in
      add_edge x y pos closure
    in
    fold_edges add_edge grph G.empty

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

let compress_ty grph =
  let g, lst = Ty.compress (fun _ -> true) grph.ty_graph in
    grph.ty_graph <- g ;
    lst

let compress_region grph =
  let g, lst =
    Region.compress
      (function Type.RegionParam _ -> true | Type.RegionInstance _ | Type.RegionTop -> false)
      grph.region_graph
  in
    grph.region_graph <- g ;
    lst

let compress_dirt grph =
  let g, lst =
    Dirt.compress
      (function Type.DirtParam _ -> true | Type.DirtAtom _ | Type.DirtEmpty -> false)
      grph.dirt_graph
  in
    grph.dirt_graph <- g ;
    lst

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
