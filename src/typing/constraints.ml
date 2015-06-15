type t = {
  new_constraints : NewConstraints.t;
}

let empty = {
  new_constraints = NewConstraints.empty;
}

let add_ty_constraint ty1 ty2 cnstrs =
  {
    new_constraints = NewConstraints.add_ty_constraint ty1 ty2 cnstrs.new_constraints
  }

let add_dirt_constraint d1 d2 cnstrs =
  {
    new_constraints = NewConstraints.add_dirt_constraint d1 d2 cnstrs.new_constraints
  }

let skeletons cnstrs = []

let remove_ty t cnstrs =
  let smaller, greater, new_constraints = NewConstraints.remove_ty t cnstrs.new_constraints in
  smaller, greater, {
    new_constraints = new_constraints
  }

let remove_dirt d cnstrs =
  let smaller, greater, new_constraints = NewConstraints.remove_dirt d cnstrs.new_constraints in
  smaller, greater, {
    new_constraints = new_constraints
  }

let add_region_constraint r1 r2 cnstrs =
  {
    new_constraints = NewConstraints.add_region_constraint r1 r2 cnstrs.new_constraints
  }

let add_full_region r cnstrs =
  {
    new_constraints = NewConstraints.add_full_region r cnstrs.new_constraints
  }

let union cnstrs1 cnstrs2 = 
  {
    new_constraints = NewConstraints.union cnstrs1.new_constraints cnstrs2.new_constraints;
  }

let subst sbst cnstr =
  {
    new_constraints = NewConstraints.subst sbst cnstr.new_constraints;
  }

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph =
  {
    new_constraints = NewConstraints.garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) grph.new_constraints;
  }
