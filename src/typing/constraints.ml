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

module TyMap = Map.Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
end)

module DirtMap = Map.Make(struct
  type t = Type.dirt_param
  let compare = Pervasives.compare
end)

type t = {
  ty_poset : TyPoset.t;
  dirt_poset: DirtPoset.t;
  region_poset: RegionPoset.t;
  full_regions: FullRegions.t;
  ty_expansion : Type.ty TyMap.t;
  dirt_expansion : Type.dirt DirtMap.t;
}

let rec expand_ty ty_expansion dirt_expansion = function
  | Type.Apply (ty_name, args) -> Type.Apply (ty_name, expand_args ty_expansion dirt_expansion args)
  | Type.Param t as ty ->
    begin try
      TyMap.find t ty_expansion
    with
      Not_found -> ty
    end
  | Type.Basic _ as ty -> ty
  | Type.Tuple tys -> Type.Tuple (Common.map (expand_ty ty_expansion dirt_expansion) tys)
  | Type.Arrow (ty, drty) -> Type.Arrow (expand_ty ty_expansion dirt_expansion ty, expand_dirty ty_expansion dirt_expansion drty)
  | Type.PureArrow(ty1,ty2) -> Type.PureArrow (expand_ty ty_expansion dirt_expansion ty1, expand_ty ty_expansion dirt_expansion ty2)
  | Type.Handler (drty1, drty2) -> Type.Handler (expand_dirty ty_expansion dirt_expansion drty1, expand_dirty ty_expansion dirt_expansion drty2)

and expand_dirty ty_expansion dirt_expansion (ty, drt) = (expand_ty ty_expansion dirt_expansion ty, expand_dirt dirt_expansion drt)

and expand_dirt dirt_expansion ({Type.ops=ops; Type.rest=rest} as drt) =
  begin try
    let {Type.ops=new_ops; Type.rest=new_rest} = DirtMap.find rest dirt_expansion in
    {Type.ops = new_ops @ ops; Type.rest = new_rest }
  with
    Not_found -> drt
  end

and expand_args ty_expansion dirt_expansion (tys, drts, rs) =
  (Common.map (expand_ty ty_expansion dirt_expansion) tys, Common.map (expand_dirt dirt_expansion) drts, rs)

let add_ty_param_constraint t1 t2 constraints =
  {constraints with ty_poset = TyPoset.add t1 t2 constraints.ty_poset}

let remove_ty_param t constraints =
  let smaller, greater, ty_poset = TyPoset.remove t constraints.ty_poset in
  smaller, greater, {constraints with ty_poset = ty_poset}

let add_dirt_param_constraint d1 d2 constraints =
  {constraints with dirt_poset = DirtPoset.add d1 d2 constraints.dirt_poset}

let remove_dirt_param d constraints =
  let smaller, greater, dirt_poset = DirtPoset.remove d constraints.dirt_poset in
  smaller, greater, {constraints with dirt_poset = dirt_poset}

let add_full_region r constraints =
  let new_full_regions = r :: RegionPoset.get_succ r constraints.region_poset in
  {constraints with full_regions = List.fold_right FullRegions.add new_full_regions constraints.full_regions}

let add_region_param_constraint r1 r2 constraints =
  if FullRegions.mem r1 constraints.full_regions then
    add_full_region r2 constraints
  else
    {constraints with region_poset = RegionPoset.add r1 r2 constraints.region_poset}

let skeletons constraints =
  (* XXX Not yet implemented *)
  []

let rec add_ty_constraint ~loc ty1 ty2 constraints =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  let ty1 = expand_ty constraints.ty_expansion constraints.dirt_expansion ty1
  and ty2 = expand_ty constraints.ty_expansion constraints.dirt_expansion ty2 in
  match ty1, ty2 with

  | (ty1, ty2) when ty1 = ty2 -> constraints

  | (Type.Param t1, Type.Param t2) -> add_ty_param_constraint t1 t2 constraints

  | (Type.Param t, ty) ->
      add_ty_constraint ~loc (Type.Param t) ty (add_ty_expansion ~loc t ty constraints)

  | (ty, Type.Param t) ->
      add_ty_constraint ~loc ty (Type.Param t) (add_ty_expansion ~loc t ty constraints)

  | (Type.Arrow (ty1, drty1), Type.Arrow (ty2, drty2)) ->
      add_ty_constraint ~loc ty2 ty1 (add_dirty_constraint ~loc drty1 drty2 constraints)

  | (Type.Tuple tys1, Type.Tuple tys2)
      when List.length tys1 = List.length tys2 ->
      List.fold_right2 (add_ty_constraint ~loc) tys1 tys2 constraints

  | (Type.Apply (ty_name1, args1), Type.Apply (ty_name2, args2)) when ty_name1 = ty_name2 ->
      begin match Tctx.lookup_params ty_name1 with
      | None -> Error.typing ~loc "Undefined type %s" ty_name1
      | Some params -> add_args_constraint ~loc params args1 args2 constraints
      end

  (* The following two cases cannot be merged into one, as the whole matching
     fails if both types are Apply, but only the second one is transparent. *)
  | (Type.Apply (ty_name, args), ty) when Tctx.transparent ~loc ty_name ->
      begin match Tctx.ty_apply ~loc ty_name args with
      | Tctx.Inline ty' -> add_ty_constraint ~loc ty' ty constraints
      | Tctx.Sum _ | Tctx.Record _ -> assert false (* None of these are transparent *)
      end

  | (ty, Type.Apply (ty_name, args)) when Tctx.transparent ~loc ty_name ->
      begin match Tctx.ty_apply ~loc ty_name args with
      | Tctx.Inline ty' -> add_ty_constraint ~loc ty ty' constraints
      | Tctx.Sum _ | Tctx.Record _ -> assert false (* None of these are transparent *)
      end

  | (Type.Handler (drty_in1, drty_out1), Type.Handler (drty_in2, drty_out2)) ->
      add_dirty_constraint ~loc drty_in2 drty_in1 (add_dirty_constraint ~loc drty_out1 drty_out2 constraints)

  | (ty1, ty2) ->
      let skeletons = skeletons constraints in
      Error.typing ~loc "This expression has type %t but it should have type %t." (Type.print skeletons ty1) (Type.print skeletons ty2)

and add_args_constraint ~loc (ts, ds, rs) (tys1, drts1, rs1) (tys2, drts2, rs2) constraints =
  (* NB: it is assumed here that
     List.length tys1 = List.length tys2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
  let for_parameters add ps lst1 lst2 constraints =
    List.fold_right2 (fun (_, (cov, contra)) (ty1, ty2) constraints ->
                        let constraints = if cov then add ty1 ty2 constraints else constraints in
                        if contra then add ty2 ty1 constraints else constraints) ps (List.combine lst1 lst2) constraints
  in
  let constraints = for_parameters (add_ty_constraint ~loc) ts tys1 tys2 constraints in
  let constraints = for_parameters (add_dirt_constraint) ds drts1 drts2 constraints in
  for_parameters add_region_param_constraint rs rs1 rs2 constraints

and add_dirty_constraint ~loc (ty1, drt1) (ty2, drt2) constraints =
  add_ty_constraint ~loc ty1 ty2 (add_dirt_constraint drt1 drt2 constraints)

and add_ty_expansion ~loc t ty constraints =
  (* XXX OCCUR-CHECK *)
  let ty_expansion = TyMap.map (expand_ty (TyMap.singleton t ty) DirtMap.empty) constraints.ty_expansion
  and smaller, greater, constraints = remove_ty_param t constraints in
  let constraints = {constraints with ty_expansion = TyMap.add t ty ty_expansion} in
  let constraints = List.fold_right (fun t' -> add_ty_constraint ~loc (Type.Param t') ty) smaller constraints in
  List.fold_right (fun t' -> add_ty_constraint ~loc ty (Type.Param t')) greater constraints

and add_dirt_constraint drt1 drt2 constraints =
  let {Type.ops = ops1; Type.rest = rest1} = expand_dirt constraints.dirt_expansion drt1
  and {Type.ops = ops2; Type.rest = rest2} = expand_dirt constraints.dirt_expansion drt2 in
  let new_ops ops1 ops2 =
    let ops2 = List.map fst ops2 in
    let add_op (op, _) news =
      if List.mem op ops2 then news else (op, Type.fresh_region_param ()) :: news
    in
    List.fold_right add_op ops1 []
  in
  let new_ops1 = new_ops ops2 ops1
  and new_ops2 = new_ops ops1 ops2 in
  let constraints, rest1 = match new_ops1 with
    | [] -> constraints, rest1
    | _ :: _ ->
      let r = Type.fresh_dirt_param () in
      (add_dirt_expansion rest1 {Type.ops = new_ops1; Type.rest = r} constraints), r in
  let constraints, rest2 = match new_ops2 with
    | [] -> constraints, rest2
    | _ :: _ ->
      let r = Type.fresh_dirt_param () in
      (add_dirt_expansion rest2 {Type.ops = new_ops2; Type.rest = r} constraints), r in
  let ops1 = new_ops1 @ ops1
  and ops2 = new_ops2 @ ops2 in
  let op_less (op, dt1) constraints =
    begin match Common.lookup op ops2 with
    | Some dt2 -> add_region_param_constraint dt1 dt2 constraints
    | None -> assert false
  end
  in
  List.fold_right op_less ops1 (add_dirt_param_constraint rest1 rest2 constraints)

and add_dirt_expansion d drt constraints =
  let ty_expansion = TyMap.map (expand_ty TyMap.empty (DirtMap.singleton d drt)) constraints.ty_expansion
  and dirt_expansion = DirtMap.map (expand_dirt (DirtMap.singleton d drt)) constraints.dirt_expansion
  and smaller, greater, constraints = remove_dirt_param d constraints in
  let constraints = {constraints with ty_expansion; dirt_expansion = DirtMap.add d drt dirt_expansion} in
  let constraints = List.fold_right (fun d' -> add_dirt_constraint (Type.simple_dirt d') drt) smaller constraints in
  List.fold_right (fun d' -> add_dirt_constraint drt (Type.simple_dirt d')) greater constraints

let empty = {
  ty_poset = TyPoset.empty;
  dirt_poset = DirtPoset.empty;
  region_poset = RegionPoset.empty;
  full_regions = FullRegions.empty;
  ty_expansion = TyMap.empty;
  dirt_expansion = DirtMap.empty;
}

let union constraints1 constraints2 =
  let constraints = TyMap.fold (add_ty_expansion ~loc:Location.unknown) constraints1.ty_expansion constraints2 in
  let constraints = DirtMap.fold add_dirt_expansion constraints1.dirt_expansion constraints in
  {
    constraints with
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
  ty_expansion = TyMap.map (Type.subst_ty sbst) constraints.ty_expansion;
  dirt_expansion = DirtMap.map (Type.subst_dirt sbst) constraints.dirt_expansion;
}

let expand_ty constraints = expand_ty constraints.ty_expansion constraints.dirt_expansion

let garbage_collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) constraints = {
  ty_poset = TyPoset.filter (fun x y -> List.mem x neg_ts && List.mem y pos_ts) constraints.ty_poset;
  dirt_poset = DirtPoset.filter (fun x y -> List.mem x neg_ds && List.mem y pos_ds) constraints.dirt_poset;
  region_poset = RegionPoset.filter (fun x y -> List.mem x neg_rs && List.mem y pos_rs && not (FullRegions.mem y constraints.full_regions)) constraints.region_poset;
  full_regions = FullRegions.filter (fun r -> List.mem r pos_rs) constraints.full_regions;
  ty_expansion = TyMap.empty;
  dirt_expansion = DirtMap.empty;
}

let print ~non_poly constraints ppf =
  TyPoset.print constraints.ty_poset ppf;
  if not (TyPoset.is_empty constraints.ty_poset) then Format.pp_print_string ppf "; ";
  DirtPoset.print constraints.dirt_poset ppf;
  if not (DirtPoset.is_empty constraints.dirt_poset) then Format.pp_print_string ppf "; ";
  RegionPoset.print constraints.region_poset ppf;
  if not (RegionPoset.is_empty constraints.region_poset) then Format.pp_print_string ppf "; ";
  Print.sequence "," (fun x ppf -> Format.fprintf ppf "%t = %s" (Type.print_region_param ~non_poly x) (Symbols.top ())) (FullRegions.elements constraints.full_regions) ppf
