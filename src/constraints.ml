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
  ty_graph : Ty.t list;
  region_graph : Region.t;
  dirt_graph : Dirt.t;
  region_bounds : (Type.region_param, region_bound list) Common.assoc
}

let empty = {
  ty_graph = [];
  region_graph = Region.empty;
  dirt_graph = Dirt.empty;
  region_bounds = [];
}

let remove_ty g x =
  let rec remove unremoved = function
  | [] -> ([], [], unremoved)
  | g :: gs ->
      if Ty.mem x g then
        let (pred, succ, g') = Ty.remove_vertex x g in
        (pred, succ, unremoved @ g' :: gs)
      else
        remove (g :: unremoved) gs
  in
  remove [] g.ty_graph

let remove_dirt g x =
  Dirt.remove_vertex x g.dirt_graph
let get_succ g x =
  Dirt.get_succ x g.dirt_graph

let subst_region_bound sbst = function
  | Without (p, rs) -> Without (sbst.Type.region_param p, List.map sbst.Type.region_param rs)
  | Instance i -> Instance (sbst.Type.instance_param i)


let subst_constraints sbst cnstr = {
  ty_graph = List.map (Ty.map (fun p -> match sbst.Type.ty_param p with Type.TyParam q -> q | _ -> assert false) (fun () -> ()) (fun () -> ())) cnstr.ty_graph;
  dirt_graph = Dirt.map (fun d -> match sbst.Type.dirt_param d with { Type.ops = []; Type.rest = d' } -> d' | _ -> assert false) (fun () -> ()) (fun () -> ()) cnstr.dirt_graph;
  region_graph = Region.map sbst.Type.region_param (List.map (subst_region_bound sbst)) (fun () -> ()) cnstr.region_graph;
  region_bounds = List.map (fun (r, bnd) -> (sbst.Type.region_param r, List.map (subst_region_bound sbst) bnd)) cnstr.region_bounds
}

let fold_ty f g acc = List.fold_right (fun g acc -> Ty.fold_edges f g acc) g.ty_graph acc
let fold_region f g acc = Region.fold_edges f g.region_graph acc
let fold_dirt f g acc = Dirt.fold_edges f g.dirt_graph acc

let add_ty_constraint ty1 ty2 cstr =
  let within, without = List.partition (fun g -> Ty.mem ty1 g or Ty.mem ty2 g) cstr.ty_graph in
  let new_graphs =
    match within with
    | [] -> (Ty.add_edge ty1 ty2 Ty.empty) :: without
    | [g] -> (Ty.add_edge ty1 ty2 g) :: without
    | [g1; g2] -> (Ty.add_edge ty1 ty2 (Ty.union g1 g2)) :: without
    | _ -> assert false
  (* Poglej, če sta že v skupnem constraintu *)
  (* Sicer dodaj novega *)
  in
  {cstr with ty_graph = new_graphs}

let add_dirt_constraint drt1 drt2 cstr =
  {cstr with dirt_graph = Dirt.add_edge drt1 drt2 cstr.dirt_graph}

let join_disjoint_constraints cstr1 cstr2 = 
  {
    ty_graph = Common.uniq (cstr1.ty_graph @ cstr2.ty_graph);
    dirt_graph = Dirt.union cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.union cstr1.region_graph cstr2.region_graph;
    region_bounds = Common.assoc_map (Common.compose Common.uniq List.flatten) (Common.assoc_flatten (cstr1.region_bounds @ cstr2.region_bounds))
  }

let add_region_bound r bnd cstr =
  let succ = Region.get_succ r cstr.region_graph in
  let new_bounds = List.map (fun r -> (r, bnd)) (r :: succ) in
  { cstr with region_bounds =
  Common.assoc_map (Common.compose Common.uniq List.flatten) (Common.assoc_flatten (new_bounds @ cstr.region_bounds)) }

let add_region_constraint rgn1 rgn2 cstr =
  let new_cstr = {cstr with region_graph = Region.add_edge rgn1 rgn2 cstr.region_graph} in
  match Common.lookup rgn1 cstr.region_bounds with
  | None -> new_cstr
  | Some bnds -> add_region_bound rgn2 bnds new_cstr

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    ty_graph = List.filter (fun g -> g <> Ty.empty) (List.map (Ty.garbage_collect pos_ts neg_ts) grph.ty_graph);
    dirt_graph = Dirt.garbage_collect pos_ds neg_ds grph.dirt_graph;
    region_graph = Region.garbage_collect pos_rs neg_rs grph.region_graph;
    region_bounds = List.filter (fun (r, ds) -> List.mem r pos_rs && ds != []) grph.region_bounds
  }

let simplify (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  let ty_subst = List.fold_right (fun g sbst -> (Ty.simplify pos_ts neg_ts g) @ sbst) grph.ty_graph []
  and dirt_subst = Dirt.simplify pos_ds neg_ds grph.dirt_graph
  and region_subst = Region.simplify pos_rs neg_rs grph.region_graph
  in
  {
    Type.identity_subst with
    Type.ty_param = (fun p -> match Common.lookup p ty_subst with Some q -> Type.TyParam q | None -> Type.TyParam p);
    Type.dirt_param = (fun p -> match Common.lookup p dirt_subst with Some q -> Type.simple_dirt q | None -> Type.simple_dirt p);
    Type.region_param = (fun p -> match Common.lookup p region_subst with Some q -> q | None -> p);
  }

let rec topological_sort = function
  | [] -> []
  | deps ->
    let is_leaf (d, ds) = ds = [] in
    let leaves, non_leaves = List.partition is_leaf deps in
    let leaves = List.map fst leaves in
    let new_deps = Common.assoc_map (fun ds -> List.filter (fun d -> not (List.mem d leaves)) ds) non_leaves in
    leaves @ topological_sort new_deps

let less pp p1 p2 ppf =
  Print.print ppf "%t %s %t" (pp p1) (Symbols.less ()) (pp p2)

let rec print_region_bound ?(non_poly=Trio.empty) bnd ppf =
  match bnd with
  | Instance i -> Type.print_instance_param i ppf
  | Without (prs, rs) -> Print.print ppf "%t - [%t]" (Type.print_region_param prs) (Print.sequence ", " (Type.print_region_param) rs)


let print_region_bounds bnd ppf =
  Print.sequence ", " print_region_bound bnd ppf

let bounds pp pp' p inf (* sup *) pps =
  match inf with
  | [] -> pps
  | inf -> (fun ppf -> Print.print ppf "%t %s %t" (pp' inf) (Symbols.less ()) (pp p)) :: pps

let rec sequence2 sep pps ppf =
  match pps with
  | [] -> ()
  | [pp] -> pp ppf
  | pp :: pps -> Format.fprintf ppf "%t%s@ %t" pp sep (sequence2 sep pps)

let print ?(non_poly=Trio.empty) skeletons g ppf =
  let pps = [] in
  (* let pps = fold_ty (fun p1 p2 lst -> if p1 != p2 then less (Type.print_ty_param skeletons ~non_poly) p1 p2 :: lst else lst) g [] in *)
  (* let pps = fold_dirt (fun d1 d2 lst -> if d1 != d2 then less (Type.print_dirt_param ~non_poly) d1 d2 :: lst else lst) g pps in *)
  let pps = fold_region (fun r1 r2 lst -> if r1 != r2 then less (Type.print_region_param ~non_poly) r1 r2 :: lst else lst) g pps in
  let pps = List.fold_right (fun (r, bound1) pps -> bounds (Type.print_region_param ~non_poly) print_region_bounds r bound1 (* bound2 *) pps) g.region_bounds pps in
  if pps != [] then
    Print.print ppf " | %t" (sequence2 "," pps)


