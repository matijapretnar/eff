type t = {
  ty : TyConstraints.t;
  new_constraints : NewConstraints.t;
  dirt : DirtConstraints.t;
}

let empty = {
  ty = TyConstraints.empty;
  new_constraints = NewConstraints.empty;
  dirt = DirtConstraints.empty;
}

let add_ty_constraint ty1 ty2 cnstrs =
  { cnstrs with ty = TyConstraints.add_edge ty1 ty2 cnstrs.ty }

let add_region_constraint r1 r2 cnstrs =
  { cnstrs with new_constraints = NewConstraints.add_region_constraint r1 r2 cnstrs.new_constraints }

let add_full_region r cnstrs =
  { cnstrs with new_constraints = NewConstraints.add_full_region r cnstrs.new_constraints }

let add_dirt_constraint d1 d2 cnstrs =
  { cnstrs with dirt = DirtConstraints.add_edge d1 d2 cnstrs.dirt }

let union cnstrs1 cnstrs2 = 
  {
    ty = TyConstraints.union cnstrs1.ty cnstrs2.ty;
    dirt = DirtConstraints.union cnstrs1.dirt cnstrs2.dirt;
    new_constraints = NewConstraints.union cnstrs1.new_constraints cnstrs2.new_constraints;
  }

let subst sbst cnstr =
  {
    ty = TyConstraints.map sbst.Type.ty_param cnstr.ty;
    new_constraints = NewConstraints.subst sbst cnstr.new_constraints;
    dirt = DirtConstraints.map sbst.Type.dirt_param cnstr.dirt;
  }

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    ty = TyConstraints.garbage_collect pos_ts neg_ts grph.ty;
    dirt = DirtConstraints.garbage_collect pos_ds neg_ds grph.dirt;
    new_constraints = NewConstraints.garbage_collect pos_rs neg_rs grph.new_constraints;
  }
