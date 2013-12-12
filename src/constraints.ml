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
}

let empty = {
  ty_graph = Ty.empty;
  region_graph = Region.empty;
  dirt_graph = Dirt.empty;
}

let add_ty_constraint ty1 ty2 cstr =
  { cstr with ty_graph = Ty.add_edge ty1 ty2 cstr.ty_graph }

let add_region_bound r bnd cstr =
  { cstr with region_graph = Region.add_region_bound r bnd cstr.region_graph }

let add_region_constraint rgn1 rgn2 cstr =
  { cstr with region_graph = Region.add_region_constraint rgn1 rgn2 cstr.region_graph }

let add_dirt_constraint drt1 drt2 cstr =
  { cstr with dirt_graph = Dirt.add_edge drt1 drt2 cstr.dirt_graph }

let union cstr1 cstr2 = 
  {
    ty_graph = Ty.union cstr1.ty_graph cstr2.ty_graph;
    dirt_graph = Dirt.union cstr1.dirt_graph cstr2.dirt_graph;
    region_graph = Region.union cstr1.region_graph cstr2.region_graph;
  }

let subst sbst cnstr =
  {
    ty_graph = Ty.map (fun p -> match sbst.Type.ty_param p with Type.TyParam q -> q | _ -> assert false) cnstr.ty_graph;
    region_graph = Region.subst sbst cnstr.region_graph;
    dirt_graph = Dirt.map (fun d -> match sbst.Type.dirt_param d with { Type.ops = []; Type.rest = d' } -> d' | _ -> assert false) cnstr.dirt_graph;
  }

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    ty_graph = Ty.garbage_collect pos_ts neg_ts grph.ty_graph;
    dirt_graph = Dirt.garbage_collect pos_ds neg_ds grph.dirt_graph;
    region_graph = Region.garbage_collect pos_rs neg_rs grph.region_graph;
  }
