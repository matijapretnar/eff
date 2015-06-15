type t = {
  ty : TyConstraints.t;
  region : RegionConstraints.t;
  dirt : DirtConstraints.t;
}

let empty = {
  ty = TyConstraints.empty;
  region = RegionConstraints.empty;
  dirt = DirtConstraints.empty;
}

let add_ty_constraint ty1 ty2 cnstrs =
  { cnstrs with ty = TyConstraints.add_edge ty1 ty2 cnstrs.ty }

let add_region_constraint r1 r2 cnstrs =
  { cnstrs with region = RegionConstraints.add_region_constraint r1 r2 cnstrs.region }

let add_full_region r cnstrs =
  { cnstrs with region = RegionConstraints.add_full_region r cnstrs.region }

let add_dirt_constraint d1 d2 cnstrs =
  { cnstrs with dirt = DirtConstraints.add_edge d1 d2 cnstrs.dirt }

let union cnstrs1 cnstrs2 = 
  {
    ty = TyConstraints.union cnstrs1.ty cnstrs2.ty;
    dirt = DirtConstraints.union cnstrs1.dirt cnstrs2.dirt;
    region = RegionConstraints.union cnstrs1.region cnstrs2.region;
  }

let subst sbst cnstr =
  {
    ty = TyConstraints.map sbst.Type.ty_param cnstr.ty;
    region = RegionConstraints.subst sbst cnstr.region;
    dirt = DirtConstraints.map sbst.Type.dirt_param cnstr.dirt;
  }

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    ty = TyConstraints.garbage_collect pos_ts neg_ts grph.ty;
    dirt = DirtConstraints.garbage_collect pos_ds neg_ds grph.dirt;
    region = RegionConstraints.garbage_collect pos_rs neg_rs grph.region;
  }
