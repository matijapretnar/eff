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
  tys : TyPoset.t;
  dirts: DirtPoset.t;
  regions: RegionPoset.t;
  full_regions: FullRegions.t;
}

let empty = {
  tys = TyPoset.empty;
  dirts = DirtPoset.empty;
  regions = RegionPoset.empty;
  full_regions = FullRegions.empty;
}

let union bnds1 bnds2 = {
  tys = TyPoset.merge bnds1.tys bnds2.tys;
  dirts = DirtPoset.merge bnds1.dirts bnds2.dirts;
  regions = RegionPoset.merge bnds1.regions bnds2.regions;
  full_regions = FullRegions.union bnds1.full_regions bnds2.full_regions;
}

let subst sbst bnds = {
  tys = TyPoset.map sbst.Type.ty_param bnds.tys;
  dirts = DirtPoset.map sbst.Type.dirt_param bnds.dirts;
  regions = RegionPoset.map sbst.Type.region_param bnds.regions;
  full_regions = FullRegions.fold (fun r s -> FullRegions.add (sbst.Type.region_param r) s) bnds.full_regions FullRegions.empty;
}

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) bnds = {
  tys = TyPoset.filter (fun x y -> List.mem x neg_ts && List.mem y pos_ts) bnds.tys;
  dirts = DirtPoset.filter (fun x y -> List.mem x neg_ds && List.mem y pos_ds) bnds.dirts;
  regions = RegionPoset.filter (fun x y -> List.mem x neg_rs && List.mem y pos_rs && not (FullRegions.mem y bnds.full_regions)) bnds.regions;
  full_regions = FullRegions.filter (fun r -> List.mem r pos_rs) bnds.full_regions;
}

let add_ty_constraint t1 t2 bnds =
  {bnds with tys = TyPoset.add t1 t2 bnds.tys}

let remove_ty t bnds =
  let smaller, greater, tys = TyPoset.remove t bnds.tys in
  smaller, greater, {bnds with tys = tys}

let add_dirt_constraint d1 d2 bnds =
  {bnds with dirts = DirtPoset.add d1 d2 bnds.dirts}

let remove_dirt d bnds =
  let smaller, greater, dirts = DirtPoset.remove d bnds.dirts in
  smaller, greater, {bnds with dirts = dirts}

let add_region_constraint r1 r2 bnds =
  if FullRegions.mem r1 bnds.full_regions then
    let new_full_regions = r2 :: RegionPoset.get_succ r2 bnds.regions in
    {bnds with full_regions = List.fold_right FullRegions.add new_full_regions bnds.full_regions}
  else
    {bnds with regions = RegionPoset.add r1 r2 bnds.regions}

let add_full_region r bnds =
  let new_full_regions = r :: RegionPoset.get_succ r bnds.regions in
  {bnds with full_regions = List.fold_right FullRegions.add new_full_regions bnds.full_regions}

let print ~non_poly bnds ppf =
  Print.print ppf "DIRTS: %t@.REGIONS: %t@.; FULL: %t"
    (DirtPoset.print bnds.dirts)
    (RegionPoset.print bnds.regions)
    (Print.sequence "," (Type.print_region_param ~non_poly) (FullRegions.elements bnds.full_regions))
