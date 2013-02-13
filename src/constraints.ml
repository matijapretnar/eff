type presence =
  | Region of Type.region_param
  | Without of Type.presence_param * Type.region_param list

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
  type lower_bound = (Type.instance_param list) option
  type upper_bound = unit
  let sup rgn1 rgn2 =
    match rgn1, rgn2 with
    | Some insts1, Some insts2 -> Some (Common.uniq (insts1 @ insts2))
    | Some insts, None | None, Some insts -> Some insts
    | None, None -> None
  let inf () () = ()
  let compare = Pervasives.compare
end)

module Dirt = Graph.Make(struct
  type t = Type.presence_param
  type lower_bound = presence list
  type upper_bound = unit
  let inf () () = ()
  let sup prs1 prs2 = prs1 @ prs2
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

let subst_presence sbst = function
  | Region r -> Region (sbst.Type.region_param r)
  | Without (p, rs) -> Without (sbst.Type.presence_param p, List.map sbst.Type.region_param rs)


let subst_constraints sbst cnstr = {
  ty_graph = Ty.map (fun p -> match sbst.Type.ty_param p with Type.TyParam q -> q | _ -> assert false) (fun () -> ()) (fun () -> ()) cnstr.ty_graph;
  dirt_graph = Dirt.map sbst.Type.presence_param (List.map (subst_presence sbst)) (fun () -> ()) cnstr.dirt_graph;
  region_graph = Region.map sbst.Type.region_param (fun insts -> Common.option_map (fun insts -> List.map (fun ins -> match sbst.Type.instance_param ins with Some i -> i | None -> assert false) insts) insts) (fun () -> ()) cnstr.region_graph;
}

let fold_ty f g acc = Ty.fold_edges f g.ty_graph acc
let fold_region f g acc = Region.fold_edges f g.region_graph acc
let fold_dirt f g acc = Dirt.fold_edges f g.dirt_graph acc

let add_region_low_bound i r cstr =
  {cstr with region_graph = Region.add_lower_bound r (Some [i]) cstr.region_graph}

let add_ty_constraint ty1 ty2 cstr =
  {cstr with ty_graph = Ty.add_edge ty1 ty2 cstr.ty_graph}

let add_dirt_constraint drt1 drt2 cstr =
  {cstr with dirt_graph = Dirt.add_edge drt1 drt2 cstr.dirt_graph}

let add_region_constraint rgn1 rgn2 cstr =
  {cstr with region_graph = Region.add_edge rgn1 rgn2 cstr.region_graph}

let add_presence_bound d bnd cstr =
  {cstr with dirt_graph = Dirt.add_lower_bound d bnd cstr.dirt_graph }

let join_disjoint_constraints cstr1 cstr2 = 
  {
    ty_graph = Ty.union cstr1.ty_graph cstr2.ty_graph;
    dirt_graph = Dirt.union cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.union cstr1.region_graph cstr2.region_graph;
  }

let garbage_collect (pos_ts, neg_ts) (pos_ds, neg_ds) (pos_rs, neg_rs) grph =
  {
    ty_graph = Ty.garbage_collect pos_ts neg_ts grph.ty_graph;
    dirt_graph = Dirt.garbage_collect pos_ds neg_ds grph.dirt_graph;
    region_graph = Region.garbage_collect pos_rs neg_rs grph.region_graph;
  }

let less pp p1 p2 ppf =
  Print.print ppf "%t <= %t" (pp p1) (pp p2)

let print_region_bound insts ppf =
  match insts with
  | None -> Print.print ppf "X"
  | Some insts -> Print.sequence "," Type.print_instance_param insts ppf

let rec print_presence ?(non_poly=Trio.empty) drt ppf =
  match drt with
  | Region r -> Type.print_region_param ~non_poly r ppf
  | Without (prs, rs) -> Print.print ppf "%t - [%t]" (Type.print_presence_param prs) (Print.sequence "," (Type.print_region_param) rs)


let print_dirt_bound bnd ppf =
  Print.sequence "," print_presence bnd ppf

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
  let pps = fold_ty (fun p1 p2 lst -> if p1 = p2 then lst else less (Type.print_ty_param ~non_poly) p1 p2 :: lst) g [] in
  let pps = fold_dirt (fun d1 d2 lst -> if d1 = d2 then lst else less (Type.print_presence_param ~non_poly) d1 d2 :: lst) g pps in
  let pps = fold_region (fun r1 r2 lst -> if r1 = r2 then lst else less (Type.print_region_param ~non_poly) r1 r2 :: lst) g pps in
  let pps = List.fold_right (fun (r, bound1, bound2) pps -> bounds (Type.print_region_param ~non_poly) print_region_bound r bound1 (* bound2 *) pps) (Region.bounds g.region_graph) pps in
  let pps = List.fold_right (fun (r, bound1, bound2) pps -> bounds (Type.print_presence_param ~non_poly) print_dirt_bound r bound1 (* bound2 *) pps) (Dirt.bounds g.dirt_graph) pps in
  Print.print ppf "%t"
    (sequence2 "," pps)


