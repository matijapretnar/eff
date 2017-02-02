module TyPoset = Poset.Make(struct
    type t = Params.ty_param
    let compare = Pervasives.compare
    let print = Params.print_ty_param ~non_poly:Params.empty
  end)

module DirtPoset = Poset.Make(struct
    type t = Params.dirt_param
    let compare = Pervasives.compare
    let print = Params.print_dirt_param ~non_poly:Params.empty
  end)

module RegionPoset = Poset.Make(struct
    type t = Params.region_param
    let compare = Pervasives.compare
    let print = Params.print_region_param ~non_poly:Params.empty
  end)

module FullRegions = Set.Make(struct
    type t = Params.region_param
    let compare = Pervasives.compare
  end)

module TyMap = Map.Make(struct
    type t = Params.ty_param
    let compare = Pervasives.compare
  end)

module DirtMap = Map.Make(struct
    type t = Params.dirt_param
    let compare = Pervasives.compare
  end)

type t = {
  ty_poset : TyPoset.t;
  dirt_poset: DirtPoset.t;
  region_poset: RegionPoset.t;
  full_regions: FullRegions.t;
}

let is_pure { dirt_poset; region_poset; full_regions } { Type.ops; Type.rest } =
  let check_region r =
    RegionPoset.get_prec r region_poset = [] &&
    not (FullRegions.mem r full_regions) in
  List.for_all (fun (_, r) -> check_region r) ops &&
  DirtPoset.get_prec rest dirt_poset = []

let is_surely_pure { dirt_poset; region_poset; full_regions } { Type.ops; Type.rest } =
  let check_region r =
    RegionPoset.get_prec r region_poset = [] &&
    RegionPoset.get_succ r region_poset = [] &&
    not (FullRegions.mem r full_regions) in
  List.for_all (fun (_, r) -> check_region r) ops &&
  DirtPoset.get_prec rest dirt_poset = [] &&
  DirtPoset.get_succ rest dirt_poset = []

type param_expansion = {
  mutable ty_expansion : Type.ty TyMap.t;
  mutable dirt_expansion : Type.dirt DirtMap.t;
}

let param_expansion = {
  ty_expansion = TyMap.empty;
  dirt_expansion = DirtMap.empty;
}

let global_add_ty p ty = 
  param_expansion.ty_expansion <- TyMap.add p ty param_expansion.ty_expansion

let global_add_dirt d drt =
  param_expansion.dirt_expansion <- DirtMap.add d drt param_expansion.dirt_expansion

let rec lookup_ty_param p =
  try
    let ty = expand_ty (TyMap.find p param_expansion.ty_expansion) in
    global_add_ty p ty;
    Some ty
  with
    Not_found -> None

and lookup_dirt_param d =
  try
    let drt = expand_dirt (DirtMap.find d param_expansion.dirt_expansion) in
    global_add_dirt d drt;
    Some drt
  with
    Not_found -> None

and expand_ty ty = match ty with
  | Type.Apply (ty_name, args) -> Type.Apply (ty_name, expand_args args)
  | Type.Param t ->
    begin match lookup_ty_param t with
      | Some ty' -> ty'
      | None -> ty
    end
  | Type.Basic _ -> ty
  | Type.Tuple tys -> Type.Tuple (Common.map expand_ty tys)
  | Type.Arrow (ty, drty) -> Type.Arrow (expand_ty ty, expand_dirty drty)
  | Type.Handler (drty1, drty2) -> Type.Handler (expand_dirty drty1, expand_dirty drty2)

and expand_dirty (ty, drt) = (expand_ty ty, expand_dirt drt)

and expand_dirt ({Type.ops=ops; Type.rest=rest} as drt) =
  match lookup_dirt_param rest with
  | Some {Type.ops=new_ops; Type.rest=new_rest} ->
    {Type.ops = new_ops @ ops; Type.rest = new_rest }
  | None -> drt

and expand_args (tys, drts, rs) =
  (Common.map expand_ty tys, Common.map expand_dirt drts, rs)

let is_pure_for_handler { dirt_poset; region_poset; full_regions } { Type.ops; Type.rest } effect_clauses =
  (* full_regions = unhandled effects in the computation *)
  let check_effect eff r =
    (* check if 'eff' is present in the eff_clause, otherwise we don't care *)
    let rec effect_is_ignored = function
      | [] -> true
      | ((eff_name,(_,_)),_)::tail when eff_name = eff ->
        RegionPoset.get_prec r region_poset = [] &&
        not (FullRegions.mem r full_regions)
      | _ :: tail -> effect_is_ignored tail
    in
    effect_is_ignored effect_clauses
  in
  (* for all 'ops' check the region *)
  List.for_all (fun (eff, r) -> check_effect eff r) ops &&
  (* check the rest *)
  DirtPoset.get_prec rest dirt_poset = []

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

let non_empty_dirts constraints =
  [] |>
  DirtPoset.fold (fun d1 d2 non_empty -> d1 :: d2 :: non_empty) constraints.dirt_poset

let non_empty_regions constraints =
  FullRegions.elements constraints.full_regions |>
  RegionPoset.fold (fun r1 r2 non_empty -> r1 :: r2 :: non_empty) constraints.region_poset

let rec add_ty_constraint ~loc ty1 ty2 constraints =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  let ty1 = expand_ty ty1
  and ty2 = expand_ty ty2 in
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
    Error.typing ~loc "This expression has type %t but it should have type %t." (Type.print_ty ty1) (Type.print_ty ty2)

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
  global_add_ty t ty;
  (* XXX OCCUR-CHECK *)
  let smaller, greater, constraints = remove_ty_param t constraints in
  let constraints = List.fold_right (fun t' -> add_ty_constraint ~loc (Type.Param t') ty) smaller constraints in
  List.fold_right (fun t' -> add_ty_constraint ~loc ty (Type.Param t')) greater constraints

and add_dirt_constraint drt1 drt2 constraints =
  let {Type.ops = ops1; Type.rest = rest1} = expand_dirt drt1
  and {Type.ops = ops2; Type.rest = rest2} = expand_dirt drt2 in
  let new_ops ops1 ops2 =
    let ops2 = List.map fst ops2 in
    let add_op (op, _) news =
      if List.mem op ops2 then news else (op, Params.fresh_region_param ()) :: news
    in
    List.fold_right add_op ops1 []
  in
  let new_ops1 = new_ops ops2 ops1
  and new_ops2 = new_ops ops1 ops2 in
  let constraints, rest1 = match new_ops1 with
    | [] -> constraints, rest1
    | _ :: _ ->
      let r = Params.fresh_dirt_param () in
      (add_dirt_expansion rest1 {Type.ops = new_ops1; Type.rest = r} constraints), r in
  let constraints, rest2 = match new_ops2 with
    | [] -> constraints, rest2
    | _ :: _ ->
      let r = Params.fresh_dirt_param () in
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
  global_add_dirt d drt;
  let smaller, greater, constraints = remove_dirt_param d constraints in
  let constraints = List.fold_right (fun d' -> add_dirt_constraint (Type.simple_dirt d') drt) smaller constraints in
  List.fold_right (fun d' -> add_dirt_constraint drt (Type.simple_dirt d')) greater constraints

let empty = {
  ty_poset = TyPoset.empty;
  dirt_poset = DirtPoset.empty;
  region_poset = RegionPoset.empty;
  full_regions = FullRegions.empty;
}

let union constraints1 constraints2 =
  {
    ty_poset = TyPoset.merge constraints1.ty_poset constraints2.ty_poset;
    dirt_poset = DirtPoset.merge constraints1.dirt_poset constraints2.dirt_poset;
    region_poset = RegionPoset.merge constraints1.region_poset constraints2.region_poset;
    full_regions = constraints1.full_regions;
  }
  |> FullRegions.fold add_full_region constraints1.full_regions
  |> FullRegions.fold add_full_region constraints2.full_regions

let list_union = function
  | [] -> empty
  | [constraints] -> constraints
  | constraints :: constraints_lst -> List.fold_right union constraints_lst constraints

let subst sbst constraints = {
  ty_poset = TyPoset.map sbst.Params.ty_param constraints.ty_poset;
  dirt_poset = DirtPoset.map sbst.Params.dirt_param constraints.dirt_poset;
  region_poset = RegionPoset.map sbst.Params.region_param constraints.region_poset;
  full_regions = FullRegions.fold (fun r s -> FullRegions.add (sbst.Params.region_param r) s) constraints.full_regions FullRegions.empty;
}

let garbage_collect pos neg constraints = {
  ty_poset = TyPoset.filter (fun x y -> Params.ty_param_mem x neg && Params.ty_param_mem y pos) constraints.ty_poset;
  dirt_poset = DirtPoset.filter (fun x y -> Params.dirt_param_mem x neg && Params.dirt_param_mem y pos) constraints.dirt_poset;
  region_poset = RegionPoset.filter (fun x y -> Params.region_param_mem x neg && Params.region_param_mem y pos && not (FullRegions.mem y constraints.full_regions)) constraints.region_poset;
  full_regions = FullRegions.filter (fun r -> Params.region_param_mem r pos) constraints.full_regions;
}

let print constraints ppf =
  TyPoset.print constraints.ty_poset ppf;
  if not (TyPoset.is_empty constraints.ty_poset) then Format.pp_print_string ppf "; ";
  DirtPoset.print constraints.dirt_poset ppf;
  if not (DirtPoset.is_empty constraints.dirt_poset) then Format.pp_print_string ppf "; ";
  RegionPoset.print constraints.region_poset ppf;
  if not (RegionPoset.is_empty constraints.region_poset) then Format.pp_print_string ppf "; ";
  Print.sequence "," (fun x ppf -> Format.fprintf ppf "%t = %s" (Params.print_region_param x) (Symbols.top ())) (FullRegions.elements constraints.full_regions) ppf
