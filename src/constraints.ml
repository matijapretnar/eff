type t = {
  ty : ConstraintsTy.t;
  region : ConstraintsRegion.t;
  dirt : ConstraintsDirt.t;
}

let empty = {
  ty = ConstraintsTy.empty;
  region = ConstraintsRegion.empty;
  dirt = ConstraintsDirt.empty;
}

let add_ty_constraint ty1 ty2 cnstrs =
  { cnstrs with ty = ConstraintsTy.add_edge ty1 ty2 cnstrs.ty }

let add_region_constraint r1 r2 rs cnstrs =
  { cnstrs with region = ConstraintsRegion.add_region_constraint r1 r2 rs cnstrs.region }

let add_instance_constraint inst r rs cnstrs =
  { cnstrs with region = ConstraintsRegion.add_instance_constraint inst r rs cnstrs.region }

let add_dirt_constraint d1 d2 cnstrs =
  { cnstrs with dirt = ConstraintsDirt.add_edge d1 d2 cnstrs.dirt }

let union cnstrs1 cnstrs2 = 
  {
    ty = ConstraintsTy.union cnstrs1.ty cnstrs2.ty;
    dirt = ConstraintsDirt.union cnstrs1.dirt cnstrs2.dirt;
    region = ConstraintsRegion.union cnstrs1.region cnstrs2.region;
  }

let subst sbst cnstr =
  {
    ty = ConstraintsTy.map (fun p -> match sbst.Type.ty_param p with Type.TyParam q -> q | _ -> assert false) cnstr.ty;
    region = ConstraintsRegion.subst sbst cnstr.region;
    dirt = ConstraintsDirt.map (fun d -> match sbst.Type.dirt_param d with { Type.ops = []; Type.rest = d' } -> d' | _ -> assert false) cnstr.dirt;
  }

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    ty = ConstraintsTy.garbage_collect pos_ts neg_ts grph.ty;
    dirt = ConstraintsDirt.garbage_collect pos_ds neg_ds grph.dirt;
    region = ConstraintsRegion.garbage_collect pos_rs neg_rs grph.region;
  }
