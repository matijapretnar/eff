(* Directed graphs of constraints. *)

(** Directed graphs represented as maps from vertices to sets of predecessors and successors. *)



type dirt =
  | DirtParam of Type.dirt_param
  | DirtAtom of Type.region_param * Common.opsym
  | DirtEmpty

and region =
  | RegionParam of Type.region_param
  | RegionAtom of instance

and instance =
  | InstanceParam of Type.instance_param
  | InstanceTop

type constraints =
  | TypeConstraint of Type.ty * Type.ty * Common.position
  | DirtConstraint of dirt * dirt * Common.position
  | RegionConstraint of region * region * Common.position


let fresh_dirt () = DirtParam (Type.fresh_dirt_param ())

let fresh_region () = RegionParam (Type.fresh_region_param ())

let fresh_instance () = RegionAtom (InstanceParam (Type.fresh_instance_param ()))

let subst_dirt sbst = function
  | DirtEmpty -> DirtEmpty
  | DirtParam d -> DirtParam (sbst.Type.dirt_param d)
  | DirtAtom (r, op) -> DirtAtom (sbst.Type.region_param r, op)

let subst_region sbst = function
  | RegionParam r -> RegionParam (sbst.Type.region_param r)
  | RegionAtom _ as rgn -> rgn

let subst_constraints sbst = function
  | TypeConstraint (ty1, ty2, pos) -> TypeConstraint (Type.subst_ty sbst ty1, Type.subst_ty sbst ty2, pos)
  | DirtConstraint (drt1, drt2, pos) -> DirtConstraint (subst_dirt sbst drt1, subst_dirt sbst drt2, pos)
  | RegionConstraint (rgn1, rgn2, pos) -> RegionConstraint (subst_region sbst rgn1, subst_region sbst rgn2, pos)



module Ty = Graph.Make(struct
  type t = Type.ty_param
  type bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
  (* let print = Print.ty_param [] *)
end)

module Region = Graph.Make(struct
  type t = region
  type bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
  (* let print = Print.region Trio.empty *)
end)

module Dirt = Graph.Make(struct
  type t = dirt
  type bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
  (* let print = Print.dirt Trio.empty *)
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
  g.ty_graph <- Ty.add_edge p1 p2 pos g.ty_graph

let add_region_edge g p1 p2 pos =
  g.region_graph <- Region.add_edge p1 p2 pos g.region_graph

let add_dirt_edge g p1 p2 pos =
  g.dirt_graph <- Dirt.add_edge p1 p2 pos g.dirt_graph

let remove_ty g x =
  let (inx, outx, g') = Ty.remove_vertex x g.ty_graph in
    g.ty_graph <- g' ;
    (inx, outx)

let fold_ty f g acc = Ty.fold_edges f g.ty_graph acc
let fold_region f g acc = Region.fold_edges f g.region_graph acc
let fold_dirt f g acc = Dirt.fold_edges f g.dirt_graph acc

(* let print grph ppf =
  Print.print ppf "TYPES:@.%t@.REGIONS:@.%t@.DIRT:@.%t@." 
  (Ty.print grph.ty_graph) (Region.print grph.region_graph) (Dirt.print grph.dirt_graph)
 *)
let garbage_collect ty_p drt_p rgn_p grph =
  {
    ty_graph = Ty.filter_edges ty_p grph.ty_graph;
    dirt_graph = Dirt.filter_edges drt_p grph.dirt_graph;
    region_graph = Region.filter_edges rgn_p grph.region_graph;
  }
