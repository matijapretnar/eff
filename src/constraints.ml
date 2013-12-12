type region_bound =
  | Without of Type.region_param * Type.region_param list
  | Instance of Type.instance_param

module Ty = Poset.Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
end)

module Dirt = Poset.Make(struct
  type t = Type.dirt_param
  let compare = Pervasives.compare
end)

type t = {
  ty_graph : Ty.t;
  region_graph : Region.t;
  dirt_graph : Dirt.t;
  region_bounds : (Type.region_param, region_bound list) Common.assoc
}

let empty = {
  ty_graph = Ty.empty;
  region_graph = Region.empty;
  dirt_graph = Dirt.empty;
  region_bounds = [];
}

let subst_region_bound sbst = function
  | Without (p, rs) -> Without (sbst.Type.region_param p, List.map sbst.Type.region_param rs)
  | Instance i -> Instance (sbst.Type.instance_param i)


let subst_constraints sbst cnstr = {
  ty_graph = Ty.map (fun p -> match sbst.Type.ty_param p with Type.TyParam q -> q | _ -> assert false) cnstr.ty_graph;
  dirt_graph = Dirt.map (fun d -> match sbst.Type.dirt_param d with { Type.ops = []; Type.rest = d' } -> d' | _ -> assert false) cnstr.dirt_graph;
  region_graph = Region.map sbst.Type.region_param cnstr.region_graph;
  region_bounds = List.map (fun (r, bnd) -> (sbst.Type.region_param r, List.map (subst_region_bound sbst) bnd)) cnstr.region_bounds
}

let fold_region f g acc = Region.fold_edges f g.region_graph acc

let join_disjoint_constraints cstr1 cstr2 = 
  {
    ty_graph = Ty.union cstr1.ty_graph cstr2.ty_graph;
    dirt_graph = Dirt.union cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.union cstr1.region_graph cstr2.region_graph;
    region_bounds = Common.assoc_map (Common.compose Common.uniq List.flatten) (Common.assoc_flatten (cstr1.region_bounds @ cstr2.region_bounds))
  }

let add_ty_constraint ty1 ty2 cstr =
  { cstr with ty_graph = Ty.add_edge ty1 ty2 cstr.ty_graph }

let add_dirt_constraint drt1 drt2 cstr =
  { cstr with dirt_graph = Dirt.add_edge drt1 drt2 cstr.dirt_graph }

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
    ty_graph = Ty.garbage_collect pos_ts neg_ts grph.ty_graph;
    dirt_graph = Dirt.garbage_collect pos_ds neg_ds grph.dirt_graph;
    region_graph = Region.garbage_collect pos_rs neg_rs grph.region_graph;
    region_bounds = List.filter (fun (r, ds) -> List.mem r pos_rs && ds != []) grph.region_bounds
  }

let region_less ~non_poly r1 r2 ppf =
  Print.print ppf "%t %s %t" (Type.print_region_param ~non_poly r1) (Symbols.less ()) (Type.print_region_param ~non_poly r2)

let print_region_bounds ~non_poly bnds ppf =
  let print bnd ppf =
    match bnd with
    | Instance i -> Type.print_instance_param i ppf
    | Without (prs, rs) -> Print.print ppf "%t - [%t]" (Type.print_region_param ~non_poly prs) (Print.sequence ", " (Type.print_region_param ~non_poly) rs)
  in
  Print.sequence ", " print bnds ppf

let bounds ~non_poly r bnds ppf =
  match bnds with
  | [] -> ()
  | bnds -> Print.print ppf "%t %s %t" (print_region_bounds ~non_poly bnds) (Symbols.less ()) (Type.print_region_param ~non_poly r)

let print ~non_poly skeletons g ppf =
  let pps = fold_region (fun r1 r2 lst -> if r1 != r2 then region_less ~non_poly r1 r2 :: lst else lst) g [] in
  let pps = List.fold_right (fun (r, bnds) lst -> if bnds != [] then bounds ~non_poly r bnds :: lst else lst) g.region_bounds pps in
  if pps != [] then
    Print.print ppf " | %t" (Print.sequence "," Common.id pps)


