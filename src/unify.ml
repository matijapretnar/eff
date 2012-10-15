(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)

let ty_param_less p q (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_ty_constraint p q cnstrs, sbst)
and dirt_less ~pos d1 d2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_dirt_constraint d1 d2 cnstrs, sbst)
and dirt_causes_op d r op (ctx, ty, cnstrs, sbst) =
  let cnstrs' = Type.add_dirt_low_bound (r, op) d cnstrs in
  (ctx, ty, cnstrs', sbst)
and dirt_pure d (ctx, ty, cnstrs, sbst) =
  (* ??? *)
  (ctx, ty, cnstrs, sbst)
and region_less ~pos r1 r2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_region_constraint (Type.RegionParam r1) (Type.RegionParam r2) cnstrs, sbst)
and region_covers r i (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_region_constraint (Type.RegionAtom (Type.InstanceParam i)) (Type.RegionParam r) cnstrs, sbst)
and just new_cnstrs (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.join_disjoint_constraints new_cnstrs cnstrs, sbst)

let rec ty_less ~pos ty1 ty2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  match Type.subst_ty sbst ty1, Type.subst_ty sbst ty2 with

  | (ty1, ty2) when ty1 = ty2 -> ty_sch

  | (Type.TyParam p, Type.TyParam q) -> ty_param_less p q ty_sch

  | (Type.TyParam p, ty) ->
      let ty' = Type.refresh ty in
      ty_less ~pos ty' ty (add_substitution ~pos p ty' ty_sch)

  | (ty, Type.TyParam p) ->
      let ty' = Type.refresh ty in
      ty_less ~pos ty ty' (add_substitution ~pos p ty' ty_sch)

  | (Type.Arrow (ty1, drty1), Type.Arrow (ty2, drty2)) ->
      ty_less ~pos ty2 ty1 (dirty_less ~pos drty1 drty2 ty_sch)

  | (Type.Tuple tys1, Type.Tuple tys2)
      when List.length tys1 = List.length tys2 ->
      List.fold_right2 (ty_less ~pos) tys1 tys2 ty_sch

  | (Type.Apply (ty_name1, args1), Type.Apply (ty_name2, args2)) when ty_name1 = ty_name2 ->
      begin match Tctx.lookup_params ty_name1 with
      | None -> Error.typing ~pos "Undefined type %s" ty_name1
      | Some ps -> args_less ~pos ps args1 args2 ty_sch
      end

  | (Type.Effect (ty_name1, args1, rgn1), Type.Effect (ty_name2, args2, rgn2)) when ty_name1 = ty_name2 ->
      begin match Tctx.lookup_params ty_name1 with
      | None -> Error.typing ~pos "Undefined type %s" ty_name1
      | Some ps ->
          region_less ~pos rgn1 rgn2 (
            args_less ~pos ps args1 args2 ty_sch
          )
      end

  (* The following two cases cannot be merged into one, as the whole matching
     fails if both types are Apply, but only the second one is transparent. *)
  | (Type.Apply (ty_name, args), ty) when Tctx.transparent ~pos ty_name ->
      begin match Tctx.ty_apply ~pos ty_name args with
      | Tctx.Inline ty' -> ty_less ~pos ty' ty ty_sch
      | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
      end

  | (ty, Type.Apply (ty_name, args)) when Tctx.transparent ~pos ty_name ->
      begin match Tctx.ty_apply ~pos ty_name args with
      | Tctx.Inline ty' -> ty_less ~pos ty ty' ty_sch
      | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
      end

  | (Type.Handler (tyv1, tyf1), Type.Handler (tyv2, tyf2)) ->
      ty_less ~pos tyv2 tyv1 (ty_less ~pos tyf1 tyf2 ty_sch)

  | (ty1, ty2) ->
      let ty1, ty2 = Type.beautify2 ty1 ty2 in
      Error.typing ~pos "This expression has type %t but it should have type %t." (Print.ty ty1) (Print.ty ty2)

and add_substitution ~pos p ty' (ctx, ty, cnstrs, sbst) =
  let sbst' = {
    Type.identity_subst with 
    Type.ty_param = (fun p' -> if p' = p then ty' else Type.TyParam p')
  } in
  let (pred, succ, new_ty_grph) = Type.remove_ty cnstrs p in
  let cnstrs = {cnstrs with Type.ty_graph = new_ty_grph} in
  let ty_sch = (Common.assoc_map (Type.subst_ty sbst') ctx, Type.subst_ty sbst' ty, cnstrs, Type.compose_subst sbst' sbst) in
  let ty_sch = List.fold_right (fun q ty_sch -> ty_less ~pos (Type.TyParam q) ty' ty_sch) pred ty_sch in
  List.fold_right (fun q ty_sch -> ty_less ~pos ty' (Type.TyParam q) ty_sch) succ ty_sch

and args_less ~pos (ps, ds, rs) (ts1, ds1, rs1) (ts2, ds2, rs2) ty_sch =
  (* NB: it is assumed here that
     List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
  let for_parameters add ps lst1 lst2 ty_sch =
    List.fold_right2 (fun (_, (cov, contra)) (ty1, ty2) ty_sch ->
                        let ty_sch = if cov then add ~pos ty1 ty2 ty_sch else ty_sch in
                        if contra then add ~pos ty2 ty1 ty_sch else ty_sch) ps (List.combine lst1 lst2) ty_sch
  in
  let ty_sch = for_parameters ty_less ps ts1 ts2 ty_sch in
  let ty_sch = for_parameters dirt_less ds ds1 ds2 ty_sch in
  for_parameters region_less rs rs1 rs2 ty_sch

and dirty_less ~pos (nws1, ty1, d1) (nws2, ty2, d2) ty_sch =
  Print.debug ~pos "Unifying freshness constraints %t <= %t." (Print.fresh_instances nws1) (Print.fresh_instances nws2);
  ty_less ~pos ty1 ty2 (dirt_less ~pos d1 d2 ty_sch)

let trim_context ~pos ctx_p (ctx, ty, cnstrs, sbst) =
  let trim (x, t) (ctx, ty, cnstrs, sbst) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs, sbst)
    | Some u -> ty_less ~pos u t (ctx, ty, cnstrs, sbst)
  in
  List.fold_right trim ctx ([], ty, cnstrs, sbst)







let (@@@) = Trio.append

let for_parameters get_params is_pos ps lst =
  List.fold_right2 (fun (_, (cov, contra)) el params ->
                      let params = if cov then get_params is_pos el @@@ params else params in
                      if contra then get_params (not is_pos) el @@@ params else params) ps lst Trio.empty

let pos_neg_params ty =
  let rec pos_ty is_pos = function
  | Type.Apply (ty_name, args) -> pos_args is_pos ty_name args
  | Type.Effect (ty_name, args, rgn) -> pos_args is_pos ty_name args @@@ pos_region_param is_pos rgn
  | Type.TyParam p -> ((if is_pos then [p] else []), [], [])
  | Type.Basic _ -> Trio.empty
  | Type.Tuple tys -> Trio.flatten_map (pos_ty is_pos) tys
  | Type.Arrow (ty1, drty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirty is_pos drty2
  | Type.Handler (ty1, ty2) -> pos_ty (not is_pos) ty1 @@@ pos_ty is_pos ty2
  and pos_dirty is_pos (_, ty, drt) =
    pos_ty is_pos ty @@@ pos_dirt_param is_pos drt
  and pos_dirt_param is_pos p =
    ([], (if is_pos then [p] else []), [])
  and pos_region_param is_pos r =
    ([], [], if is_pos then [r] else [])
  and pos_args is_pos ty_name (tys, drts, rgns) =
    match Tctx.lookup_params ty_name with
    | None -> assert false (* We type-checked before thus all type names are valid. *)
    | Some (ps, ds, rs) ->
        for_parameters pos_ty is_pos ps tys @@@
        for_parameters pos_dirt_param is_pos ds drts @@@
        for_parameters pos_region_param is_pos rs rgns
  in
  Trio.uniq (pos_ty true ty), Trio.uniq (pos_ty false ty)

let pos_neg_constraints (_, pos_ds, _) (_, neg_ds, _) cnstrs =
  let bounds = Type.Dirt.bounds cnstrs.Type.dirt_graph in
  let regions = function
    | None -> []
    | Some r_ops -> List.map fst r_ops
  in
  let pos, neg = List.fold_right (fun (d, inf, sup) (pos, neg) ->
                                    let neg = if List.mem d pos_ds then regions inf @ neg else neg
                                    and pos = if List.mem d neg_ds then regions sup @ pos else pos
                                    in
                                    (pos, neg)
  ) bounds ([], []) in
  ([], [], Common.uniq pos), ([], [], Common.uniq neg)

(*   let pos_vertex d =
    if List.mem d pos_ds then
    let (_, _, inf, _) = cnstrs.Type.dirt_graph.function
 *)

let pos_neg_ty_scheme (ctx, ty, cnstrs, _) =
  let add_ctx_pos_neg (_, ctx_ty) (pos, neg) =
    let pos_ctx_ty, neg_ctx_ty = pos_neg_params ctx_ty in
    neg_ctx_ty @@@ pos, pos_ctx_ty @@@ neg
  in
  let (pos, neg) = List.fold_right add_ctx_pos_neg ctx (pos_neg_params ty) in
  let (posc, negc) = pos_neg_constraints pos neg cnstrs in
  (Trio.uniq (posc @@@ pos), Trio.uniq (negc @@@ neg))

let collect ((pos_ts, pos_ds, pos_rs), (neg_ts, neg_ds, neg_rs)) (ctx, ty, cnstrs, sbst) =
  let ty_p p q = List.mem p neg_ts && List.mem q pos_ts
  and drt_p p q = List.mem p neg_ds && List.mem q pos_ds
  and rgn_p rgn1 rgn2 = match rgn1, rgn2 with
    | Type.RegionParam p, Type.RegionParam q -> List.mem p neg_rs && List.mem q pos_rs
    | _, Type.RegionAtom (Type.InstanceTop) -> false
    | Type.RegionParam p, _ -> List.mem p neg_rs
    | _, Type.RegionParam q -> List.mem q pos_rs
    | _, _ -> true
  in
  let cnstrs' = Type.garbage_collect ty_p drt_p rgn_p cnstrs in
  (ctx, ty, cnstrs')

let normalize_context ~pos (ctx, ty, cstr, sbst) =
  let add (x, ty) (ctx, typ, cnstrs, sbst) =
    match Common.lookup x ctx with
    | None ->
        let ty' = Type.fresh_ty () in
        ty_less ~pos ty' ty ((x, ty') :: ctx, typ, cnstrs, sbst)
    | Some ty' ->
        ty_less ~pos ty' ty (ctx, typ, cnstrs, sbst)
  in
  List.fold_right add ctx ([], ty, cstr, sbst)

let gather_ty_scheme ~pos ctx ty chngs =
  let ty_sch = List.fold_right (fun chng -> chng) chngs (ctx, ty, Type.empty, Type.identity_subst) in
  let ty_sch = normalize_context ~pos ty_sch in
  let pos_neg = pos_neg_ty_scheme ty_sch in
  collect pos_neg ty_sch

let gather_dirty_scheme ~pos ctx drty chngs =
  match gather_ty_scheme ~pos ctx (Type.Arrow (Type.unit_ty, drty)) chngs with
  | ctx, Type.Arrow (_, drty), cstr -> (ctx, drty, cstr)
  | _ -> assert false

let gather_pattern_scheme ~pos ctx ty chngs =
  let ty_sch = List.fold_right (fun chng -> chng) chngs (ctx, ty, Type.empty, Type.identity_subst) in
  (* Note that we change the polarities in pattern types *)
  let (neg, pos) = pos_neg_ty_scheme ty_sch in
  collect (pos, neg) ty_sch
