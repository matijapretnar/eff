type region_bound =
  | Without of Type.region_param * Type.region_param list
  | Instance of Type.instance_param

module Ty = Graph.Make(struct
  type t = Type.ty_param
  type lower_bound = unit
  type upper_bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
end)

module Region = Graph.Make(struct
  type t = Type.region_param
  type lower_bound = region_bound list
  type upper_bound = unit
  let sup insts1 insts2 = Common.uniq (insts1 @ insts2)
  let inf () () = ()
  let compare = Pervasives.compare
end)

module Dirt = Graph.Make(struct
  type t = Type.dirt_param
  type lower_bound = unit
  type upper_bound = unit
  let inf () () = ()
  let sup () () = ()
  let compare = Pervasives.compare
end)

type t = {
  ty_graph : Ty.t;
  region_graph : Region.t;
  dirt_graph : Dirt.t;
}

let empty = {
  ty_graph = Ty.empty;
  region_graph = Region.empty;
  dirt_graph = Dirt.empty;
}

let remove_ty g x =
  Ty.remove_vertex x g.ty_graph
let remove_dirt g x =
  Dirt.remove_vertex x g.dirt_graph
let get_succ g x =
  Dirt.get_succ x g.dirt_graph

let subst_region_bound sbst = function
  | Without (p, rs) -> Without (sbst.Type.region_param p, List.map sbst.Type.region_param rs)
  | Instance i -> Instance (sbst.Type.instance_param i)


let subst_constraints sbst cnstr = {
  ty_graph = Ty.map (fun p -> match sbst.Type.ty_param p with Type.TyParam q -> q | _ -> assert false) (fun () -> ()) (fun () -> ()) cnstr.ty_graph;
  dirt_graph = Dirt.map (fun d -> match sbst.Type.dirt_param d with { Type.ops = []; Type.rest = d' } -> d' | _ -> assert false) (fun () -> ()) (fun () -> ()) cnstr.dirt_graph;
  region_graph = Region.map sbst.Type.region_param (List.map (subst_region_bound sbst)) (fun () -> ()) cnstr.region_graph;
}

let fold_ty f g acc = Ty.fold_edges f g.ty_graph acc
let fold_region f g acc = Region.fold_edges f g.region_graph acc
let fold_dirt f g acc = Dirt.fold_edges f g.dirt_graph acc

let add_ty_constraint ty1 ty2 cstr =
  {cstr with ty_graph = Ty.add_edge ty1 ty2 cstr.ty_graph}

let add_dirt_constraint drt1 drt2 cstr =
  {cstr with dirt_graph = Dirt.add_edge drt1 drt2 cstr.dirt_graph}

let add_region_constraint rgn1 rgn2 cstr =
  {cstr with region_graph = Region.add_edge rgn1 rgn2 cstr.region_graph}

let add_region_bound r bnd cstr =
  {cstr with region_graph = Region.add_lower_bound r bnd cstr.region_graph }

let join_disjoint_constraints cstr1 cstr2 = 
  {
    ty_graph = Ty.union cstr1.ty_graph cstr2.ty_graph;
    dirt_graph = Dirt.union cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.union cstr1.region_graph cstr2.region_graph;
  }

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    ty_graph = Ty.garbage_collect pos_ts neg_ts grph.ty_graph;
    dirt_graph = Dirt.garbage_collect pos_ds neg_ds grph.dirt_graph;
    region_graph = Region.garbage_collect pos_rs neg_rs grph.region_graph;
  }

let rec topological_sort = function
  | [] -> []
  | deps ->
    let is_leaf (d, ds) = ds = [] in
    let leaves, non_leaves = List.partition is_leaf deps in
    let leaves = List.map fst leaves in
    let new_deps = Common.assoc_map (fun ds -> List.filter (fun d -> not (List.mem d leaves)) ds) non_leaves in
    leaves @ topological_sort new_deps

let simplify grph =
  let region_leaves = Region.leaves grph.region_graph in
  let bound_dependency bnd = match bnd with None -> [] | Some bnd -> List.fold_right (fun bnd dep -> match bnd with
  | Without (d, _) -> d :: dep
  | Instance _ -> dep) bnd []
  in
  let dependency = Region.fold_vertices (fun x inx _ infx _ dep -> (x, bound_dependency infx @ inx) :: dep) grph.region_graph [] in
  let sort = topological_sort dependency in
  region_leaves, dependency, sort


let less pp p1 p2 ppf =
  Print.print ppf "%t <= %t" (pp p1) (pp p2)

let rec print_region_bound ?(non_poly=Trio.empty) bnd ppf =
  match bnd with
  | Instance i -> Type.print_instance_param i ppf
  | Without (prs, rs) -> Print.print ppf "%t - [%t]" (Type.print_region_param prs) (Print.sequence "," (Type.print_region_param) rs)


let print_region_bounds bnd ppf =
  Print.sequence "," print_region_bound bnd ppf

let bounds pp pp' p inf (* sup *) pps =
  match inf with
  | None -> pps
  | Some inf -> (fun ppf -> Print.print ppf "%t <= %t" (pp' inf) (pp p)) :: pps

let rec sequence2 sep pps ppf =
  match pps with
  | [] -> ()
  | [pp] -> pp ppf
  | pp :: pps -> Format.fprintf ppf "%t%s@ %t" pp sep (sequence2 sep pps)

let print ?(non_poly=Trio.empty) g ppf =
  let pps = fold_ty (fun p1 p2 lst -> less (Type.print_ty_param ~non_poly) p1 p2 :: lst) g [] in
  let pps = fold_dirt (fun d1 d2 lst -> less (Type.print_dirt_param ~non_poly) d1 d2 :: lst) g pps in
  let pps = fold_region (fun r1 r2 lst -> less (Type.print_region_param ~non_poly) r1 r2 :: lst) g pps in
  let pps = List.fold_right (fun (r, bound1, bound2) pps -> bounds (Type.print_region_param ~non_poly) print_region_bounds r bound1 (* bound2 *) pps) (Region.bounds g.region_graph) pps in
  Print.print ppf "%t"
    (sequence2 "," pps)


