module TyPoset = Poset.Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
  let print = Type.print_ty_param ~non_poly:Trio.empty
end)

module DirtPoset = Poset.Make(struct
  type t = Type.dirt_param
  let compare = Pervasives.compare
  let print = Type.print_dirt_param ~non_poly:Trio.empty
end)

module RegionPoset = Poset.Make(struct
  type t = Type.region_param
  let compare = Pervasives.compare
  let print = Type.print_region_param ~non_poly:Trio.empty
end)

module FullRegions = Set.Make(struct
  type t = Type.region_param
  let compare = Pervasives.compare
end)

type t = {
  ty_poset : TyPoset.t;
  dirt_poset: DirtPoset.t;
  region_poset: RegionPoset.t;
  full_regions: FullRegions.t;
}

let empty = {
  ty_poset = TyPoset.empty;
  dirt_poset = DirtPoset.empty;
  region_poset = RegionPoset.empty;
  full_regions = FullRegions.empty;
}

let union constraints1 constraints2 = {
  ty_poset = TyPoset.merge constraints1.ty_poset constraints2.ty_poset;
  dirt_poset = DirtPoset.merge constraints1.dirt_poset constraints2.dirt_poset;
  region_poset = RegionPoset.merge constraints1.region_poset constraints2.region_poset;
  full_regions = FullRegions.union constraints1.full_regions constraints2.full_regions;
}

let subst sbst constraints = {
  ty_poset = TyPoset.map sbst.Type.ty_param constraints.ty_poset;
  dirt_poset = DirtPoset.map sbst.Type.dirt_param constraints.dirt_poset;
  region_poset = RegionPoset.map sbst.Type.region_param constraints.region_poset;
  full_regions = FullRegions.fold (fun r s -> FullRegions.add (sbst.Type.region_param r) s) constraints.full_regions FullRegions.empty;
}

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) constraints = {
  ty_poset = TyPoset.filter (fun x y -> List.mem x neg_ts && List.mem y pos_ts) constraints.ty_poset;
  dirt_poset = DirtPoset.filter (fun x y -> List.mem x neg_ds && List.mem y pos_ds) constraints.dirt_poset;
  region_poset = RegionPoset.filter (fun x y -> List.mem x neg_rs && List.mem y pos_rs && not (FullRegions.mem y constraints.full_regions)) constraints.region_poset;
  full_regions = FullRegions.filter (fun r -> List.mem r pos_rs) constraints.full_regions;
}

let add_ty_constraint t1 t2 constraints =
  {constraints with ty_poset = TyPoset.add t1 t2 constraints.ty_poset}

let remove_ty t constraints =
  let smaller, greater, ty_poset = TyPoset.remove t constraints.ty_poset in
  smaller, greater, {constraints with ty_poset = ty_poset}

let skeletons constraints =
  (* XXX Not yet implemented *)
  []

let add_dirt_constraint d1 d2 constraints =
  {constraints with dirt_poset = DirtPoset.add d1 d2 constraints.dirt_poset}

let remove_dirt d constraints =
  let smaller, greater, dirt_poset = DirtPoset.remove d constraints.dirt_poset in
  smaller, greater, {constraints with dirt_poset = dirt_poset}

let add_full_region r constraints =
  let new_full_regions = r :: RegionPoset.get_succ r constraints.region_poset in
  {constraints with full_regions = List.fold_right FullRegions.add new_full_regions constraints.full_regions}

let add_region_constraint r1 r2 constraints =
  if FullRegions.mem r1 constraints.full_regions then
    add_full_region r2 constraints
  else
    {constraints with region_poset = RegionPoset.add r1 r2 constraints.region_poset}

let print ~non_poly constraints ppf =
  Print.print ppf "ty_poset: %t\ndirt_poset: %t\nregion_poset: %t\n; FULL: %t"
    (TyPoset.print constraints.ty_poset)
    (DirtPoset.print constraints.dirt_poset)
    (RegionPoset.print constraints.region_poset)
    (Print.sequence "," (Type.print_region_param ~non_poly) (FullRegions.elements constraints.full_regions))
