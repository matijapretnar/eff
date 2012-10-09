(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)

let rec ty_less ~pos ty1 ty2 ((ctx, ty, cnstrs) as ty_sch) =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  match ty1, ty2 with

  | (t1, t2) when t1 = t2 -> ty_sch

  | (Type.TyParam p, Type.TyParam q) ->
      (ctx, ty, Type.add_ty_constraint ~pos p q cnstrs)

  | (Type.TyParam p, t) ->
      let t' = Type.refresh t in
      ty_less ~pos t' t (add_substitution p t' ty_sch)

  | (t, Type.TyParam p) ->
      let t' = Type.refresh t in
      ty_less ~pos t t' (add_substitution p t' ty_sch)

  | (Type.Arrow (ty1, drty1), Type.Arrow (ty2, drty2)) ->
      ty_less ~pos ty2 ty1 (dirty_less ~pos drty1 drty2 ty_sch)

  | (Type.Tuple lst1, Type.Tuple lst2)
      when List.length lst1 = List.length lst2 ->
      List.fold_right2 (ty_less ~pos) lst1 lst2 ty_sch

  | (Type.Apply (t1, args1), Type.Apply (t2, args2)) when t1 = t2 ->
    (* NB: it is assumed here that
       List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
      begin match Tctx.lookup_params t1 with
      | None -> Error.typing ~pos "Undefined type %s" t1
      | Some ps -> args_less ~pos ps args1 args2 ty_sch
      end

  | (Type.Effect (t1, args1, rgn1), Type.Effect (t2, args2, rgn2)) when t1 = t2 ->
      (* NB: it is assumed here that
         && List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
      begin match Tctx.lookup_params t1 with
      | None -> Error.typing ~pos "Undefined type %s" t1
      | Some ps ->
          region_less ~pos rgn1 rgn2 (
            args_less ~pos ps args1 args2 ty_sch
          )
      end

  (* The following two cases cannot be merged into one, as the whole matching
     fails if both types are Apply, but only the second one is transparent. *)
  | (Type.Apply (t1, lst1), t2) when Tctx.transparent ~pos t1 ->
      begin match Tctx.ty_apply ~pos t1 lst1 with
      | Tctx.Inline t -> ty_less ~pos t2 t ty_sch
      | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
      end

  | (t2, Type.Apply (t1, lst1)) when Tctx.transparent ~pos t1 ->
      begin match Tctx.ty_apply ~pos t1 lst1 with
      | Tctx.Inline t -> ty_less ~pos t t2 ty_sch
      | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
      end

  | (Type.Handler (tv1, tf1), Type.Handler (tv2, tf2)) ->
      ty_less ~pos tv2 tv1 (ty_less ~pos tf1 tf2 ty_sch)

  | (t1, t2) ->
        let t1, t2 = Type.beautify2 t1 t2 in
        Error.typing ~pos
          "This expression has type %t but it should have type %t."
          (Print.ty t1)
          (Print.ty t2)

and add_substitution p t (ctx, ty, cnstrs) =
(* When parameter [p] gets substituted by type [t] the vertex
   [p] must be removed from the graph, and each edge becomes
   a constraint in the queue. *)
  let sbst = {
    Type.identity_subst with 
    Type.ty_param = (fun p' -> if p' = p then t else Type.TyParam p')
  } in
  let (pred, succ, new_grph) = Type.remove_ty cnstrs p in
  let cnstrs = { cnstrs with Type.ty_graph = new_grph } in
  let ty_sch = (Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, cnstrs) in
  let ty_sch =
    List.fold_right (fun (q, pos) ty_sch -> ty_less ~pos (Type.TyParam q) (Type.TyParam p) ty_sch) pred ty_sch in
    List.fold_right (fun (q, pos) ty_sch -> ty_less ~pos (Type.TyParam p) (Type.TyParam q) ty_sch) succ ty_sch

and args_less ~pos (ps, ds, rs) (ts1, ds1, rs1) (ts2, ds2, rs2) ty_sch =
  let for_parameters add ps lst1 lst2 ty_sch =
    List.fold_right2 (fun (_, (cov, contra)) (ty1, ty2) ty_sch ->
                        let ty_sch = if cov then add ~pos ty1 ty2 ty_sch else ty_sch in
                        if contra then add ~pos ty2 ty1 ty_sch else ty_sch) ps (List.combine lst1 lst2) ty_sch
  in
  let ty_sch = for_parameters ty_less ps ts1 ts2 ty_sch in
  let ty_sch = for_parameters dirt_less ds ds1 ds2 ty_sch in
  for_parameters region_less rs rs1 rs2 ty_sch

and dirt_less ~pos d1 d2 (ctx, ty, cnstrs) =
  (ctx, ty, Type.add_dirt_constraint ~pos (Type.DirtParam d1) (Type.DirtParam d2) cnstrs)
and dirt_causes_op ~pos d r op (ctx, ty, cnstrs) =
  (ctx, ty, Type.add_dirt_constraint ~pos (Type.DirtAtom (r, op)) (Type.DirtParam d) cnstrs)
and dirt_pure ~pos d (ctx, ty, cnstrs) =
  (ctx, ty, Type.add_dirt_constraint ~pos (Type.DirtParam d) (Type.DirtEmpty) cnstrs)
and region_less ~pos r1 r2 (ctx, ty, cnstrs) =
  (ctx, ty, Type.add_region_constraint ~pos (Type.RegionParam r1) (Type.RegionParam r2) cnstrs)
and region_covers ~pos r i (ctx, ty, cnstrs) =
  (ctx, ty, Type.add_region_constraint ~pos (Type.RegionAtom (Type.InstanceParam i)) (Type.RegionParam r) cnstrs)
and dirty_less ~pos (nws1, ty1, d1) (nws2, ty2, d2) (ctx, ty, cnstrs) =
  Print.debug ~pos "Unifying freshness constraints %t <= %t." (Print.fresh_instances nws1) (Print.fresh_instances nws2);
  ty_less ~pos ty1 ty2 (dirt_less ~pos d1 d2 (ctx, ty, cnstrs))

let just cnstrs1 (ctx, ty, cnstrs2) = (ctx, ty, Type.join_disjoint_constraints cnstrs1 cnstrs2)

let trim_context ~pos ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs)
    | Some u -> ty_less ~pos u t (ctx, ty, cnstrs)
  in
  List.fold_right trim ctx ([], ty, cnstrs)

let (@@@) = Trio.append

let for_parameters get_params is_pos ps lst =
  List.fold_right2 (fun (_, (cov, contra)) el params ->
                      let params = if cov then get_params is_pos el @@@ params else params in
                      if contra then get_params (not is_pos) el @@@ params else params) ps lst Trio.empty

let pos_neg_params ty =
  let pos_params is_pos ty =
    let rec pos_ty is_pos = function
      | Type.Apply (ty_name, args) -> pos_args is_pos ty_name args
      | Type.Effect (ty_name, args, rgn) -> pos_args is_pos ty_name args @@@ pos_region_param is_pos rgn
      | Type.TyParam p -> ((if is_pos then [p] else []), [], [])
      | Type.Basic _ -> Trio.empty
      | Type.Tuple tys -> Trio.flatten_map (pos_ty is_pos) tys
      | Type.Arrow (ty1, dirty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirty is_pos dirty2
      | Type.Handler (ty1, ty2) -> pos_ty (not is_pos) ty1 @@@ pos_ty is_pos ty2
    and pos_dirty is_pos (_, ty, drt) =
      pos_ty is_pos ty @@@ pos_dirt_param is_pos drt
    and pos_dirt_param is_pos p = ([], (if is_pos then [p] else []), [])
    and pos_region_param is_pos r = ([], [], if is_pos then [r] else [])
    and pos_args is_pos ty_name (tys, drts, rgns) =
      begin match Tctx.lookup_params ty_name with
      (* We assume that ty has been type-checked thus all type names are valid. *)
      | None -> assert false
      | Some (ps, ds, rs) ->
          for_parameters pos_ty is_pos ps tys @@@
          for_parameters pos_dirt_param is_pos ds drts @@@
          for_parameters pos_region_param is_pos rs rgns
      end
    in
    Trio.uniq (pos_ty is_pos ty)
  in
  pos_params true ty, pos_params false ty

let collect (pos_ts, pos_ds, pos_rs) (neg_ts, neg_ds, neg_rs) cstr =
  let ty_p p q pos = List.mem p neg_ts && List.mem q pos_ts
  and drt_p drt1 drt2 pos = match drt1, drt2 with
    | Type.DirtEmpty, _ -> false
    | Type.DirtParam p, Type.DirtParam q -> List.mem p neg_ds && List.mem q pos_ds
    | Type.DirtParam p, _ -> List.mem p neg_ds
    | _, Type.DirtParam q -> List.mem q pos_ds
    | _, _ -> true
  and rgn_p rgn1 rgn2 pos = match rgn1, rgn2 with
    | Type.RegionParam p, Type.RegionParam q -> List.mem p neg_rs && List.mem q pos_rs
    | _, Type.RegionAtom (Type.InstanceTop) -> false
    | Type.RegionParam p, _ -> List.mem p neg_rs
    | _, Type.RegionParam q -> List.mem q pos_rs
    | _, _ -> true
  in
  Type.garbage_collect ty_p drt_p rgn_p cstr

let gather_ty_scheme ~pos ctx ty changes =
  let normalize_context ~pos (ctx, ty, cstr) =
    let add (x, ty) (ctx, typ, cnstrs) =
      match Common.lookup x ctx with
      | None ->
          let ty' = Type.fresh_ty () in
          ty_less ~pos ty' ty ((x, ty') :: ctx, typ, cnstrs)
      | Some ty' ->
          ty_less ~pos ty' ty (ctx, typ, cnstrs)
    in
    List.fold_right add ctx ([], ty, cstr)
  in
  let normalize_ty_scheme ~pos ty_sch =
    let ctx, ty, cstr = normalize_context ~pos ty_sch in
    let pos, neg = List.fold_right (fun (_, t) (pos, neg) ->
        let pos_t, neg_t = pos_neg_params t in
        neg_t @@@ pos, pos_t @@@ neg) ctx (pos_neg_params ty) in
    let pos, neg = Trio.uniq pos, Trio.uniq neg in
    (ctx, ty, collect pos neg cstr)
  in
  normalize_ty_scheme ~pos (List.fold_right (fun change ty_sch -> change ty_sch) changes (ctx, ty, Type.empty))

let gather_dirty_scheme ~pos ctx drty changes =
  match gather_ty_scheme ~pos ctx (Type.Arrow (Type.unit_ty, drty)) changes with
  | ctx, Type.Arrow (_, drty), cstr -> (ctx, drty, cstr)
  | _ -> assert false

let gather_pattern_scheme ~pos ctx ty changes =
  let ctx, ty, cstr = List.fold_right (fun change ty_sch -> change ty_sch) changes (ctx, ty, Type.empty) in
  let pos, neg = List.fold_right (fun (_, t) (pos, neg) ->
      let pos_t, neg_t = pos_neg_params t in
      neg_t @@@ pos, pos_t @@@ neg) ctx (pos_neg_params ty) in
  let pos, neg = Trio.uniq pos, Trio.uniq neg in
  (ctx, ty, collect neg pos cstr)

