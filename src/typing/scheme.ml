type context = (CoreSyntax.variable, Type.ty) Common.assoc
type 'a t = context * 'a * Constraints.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t
type abstraction_scheme = (Type.ty * Type.dirty) t
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t
type change = ty_scheme -> ty_scheme

let simple ty = ([], ty, Constraints.empty)

let beautify2 ty1 ty2 cnstrs =
  let sbst = Type.beautifying_subst () in
  let ty1 = Type.subst_ty sbst ty1 in
  let ty2 = Type.subst_ty sbst ty2 in
  let cnstrs = Constraints.subst sbst cnstrs in
  let skeletons = Constraints.skeletons cnstrs in
  (ty1, ty2, skeletons)

let refresh (ctx, ty, cnstrs) =
  let sbst = Type.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Constraints.subst sbst cnstrs

let ty_param_less p q (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_ty_constraint p q cnstrs)
and dirt_param_less d1 d2 (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_dirt_constraint d1 d2 cnstrs)
and just new_cnstrs (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.union new_cnstrs cnstrs)
and region_param_less r1 r2 (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_region_param_constraint r1 r2 cnstrs)
and add_full_region r (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_full_region r cnstrs)
and dirt_less drt1 drt2 (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_dirt_constraint drt1 drt2 cnstrs)
and ty_less ~loc ty1 ty2 (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_ty_constraint ~loc ty1 ty2 cnstrs)
and dirty_less ~loc drty1 drty2 (ctx, ty, cnstrs) =
  (ctx, ty, Constraints.add_dirty_constraint ~loc drty1 drty2 cnstrs)

let remove_context ~loc ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs)
    | Some u -> (ctx, ty, cnstrs)
  in
  List.fold_right trim ctx ([], ty, cnstrs)

let less_context ~loc ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs)
    | Some u -> ty_less ~loc u t ((x, u) :: ctx, ty, cnstrs)
  in
  List.fold_right trim ctx ([], ty, cnstrs)

let trim_context ~loc ctx_p ty_sch =
  let ty_sch = less_context ~loc ctx_p ty_sch in
  let ty_sch = remove_context ~loc ctx_p ty_sch in
  ty_sch

let (@@@) = Common.trio_append

let pos_neg_ty_scheme (ctx, ty, cnstrs) =
  let add_ctx_pos_neg (_, ctx_ty) (pos, neg) =
    let pos_ctx_ty, neg_ctx_ty = Type.pos_neg_params Tctx.get_variances ctx_ty in
    neg_ctx_ty @@@ pos, pos_ctx_ty @@@ neg
  in
  let (((_, _, pos_rs) as pos), ((_, _, neg_rs) as neg)) = List.fold_right add_ctx_pos_neg ctx (Type.pos_neg_params Tctx.get_variances ty) in
  Common.trio_uniq pos, Common.trio_uniq neg

let pos_neg_dirtyscheme (ctx, drty, cnstrs) =
  pos_neg_ty_scheme (ctx, Type.Arrow (Type.unit_ty, drty), cnstrs)

let garbage_collect pos neg (ctx, ty, cnstrs) =
  ctx, ty, Constraints.garbage_collect pos neg cnstrs

let normalize_context ~loc (ctx, ty, cnstrs) =
  let collect (x, ty) ctx =
    match Common.lookup x ctx with
    | None -> (x, ref [ty]) :: ctx
    | Some tys -> tys := ty :: !tys; ctx
  in
  let ctx = List.fold_right collect ctx [] in

  let add (x, tys) (ctx, typ, cnstrs) =
    match !tys with
    | [] -> assert false
    | [ty] -> ((x, ty) :: ctx, typ, cnstrs)
    | tys ->
        let ty' = Type.fresh_ty () in
        let ctx' = (x, ty') :: ctx in
        List.fold_right (fun ty ty_sch -> ty_less ~loc ty' ty ty_sch) tys (ctx', typ, cnstrs)
  in
  List.fold_right add ctx ([], ty, cnstrs)

let subst_ty_scheme sbst (ctx, ty, cnstrs) =
  let ty = Type.subst_ty sbst ty in
  let cnstrs = Constraints.subst sbst cnstrs in
  let ctx = Common.assoc_map (Type.subst_ty sbst) ctx in
  (ctx, ty, cnstrs)

let subst_dirty_scheme sbst (ctx, drty, cnstrs) =
  let drty = Type.subst_dirty sbst drty in
  let cnstrs = Constraints.subst sbst cnstrs in
  let ctx = Common.assoc_map (Type.subst_ty sbst) ctx in
  (ctx, drty, cnstrs)

let finalize ctx ty chngs =
  let ctx, ty, cnstrs = List.fold_right Common.id chngs (ctx, ty, Constraints.empty) in
  (Common.assoc_map (Constraints.expand_ty cnstrs) ctx, Constraints.expand_ty cnstrs ty, cnstrs)

let expand_ty_scheme (ctx, ty, constraints) =
  (Common.assoc_map (Constraints.expand_ty constraints) ctx, Constraints.expand_ty constraints ty, constraints)

let clean_ty_scheme ~loc ty_sch =
  let ty_sch = normalize_context ~loc ty_sch in
  let ty_sch = expand_ty_scheme ty_sch in
  let pos, neg = pos_neg_ty_scheme ty_sch in
  garbage_collect pos neg ty_sch

let clean_dirty_scheme ~loc (ctx, drty, constraints) =
  match clean_ty_scheme ~loc (ctx, (Type.Arrow (Type.unit_ty, drty)), constraints) with
  | ctx, Type.Arrow (_, drty), cnstrs -> (ctx, drty, cnstrs)
  | _ -> assert false

let create_ty_scheme ctx ty changes =
  List.fold_right Common.id changes (ctx, ty, Constraints.empty)

let finalize_ty_scheme ~loc ctx ty changes =
  let ty_sch = create_ty_scheme ctx ty changes in
  clean_ty_scheme ~loc ty_sch

let finalize_dirty_scheme ~loc ctx drty changes =
  match finalize_ty_scheme ~loc ctx (Type.Arrow (Type.unit_ty, drty)) changes with
  | ctx, Type.Arrow (_, drty), cnstrs -> (ctx, drty, cnstrs)
  | _ -> assert false

let finalize_pattern_scheme ~loc ctx ty chngs =
  (* We do not expand the context *)
  let ty_sch = create_ty_scheme ctx ty chngs in
  let ty_sch = expand_ty_scheme ty_sch in
  (* Note that we change the polarities in pattern types *)
  let neg, pos = pos_neg_ty_scheme ty_sch in
  garbage_collect pos neg ty_sch

let add_to_top ~loc ctx cnstrs (ctx_c, drty_c, cnstrs_c) =
  finalize_dirty_scheme ~loc (ctx @ ctx_c) drty_c ([
    just cnstrs_c;
    just cnstrs
  ])

let abstract ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  match finalize_ty_scheme ~loc ctx_c (Type.Arrow (ty_p, drty_c)) [
    trim_context ~loc ctx_p;
    just cnstrs_p;
    just cnstrs_c
  ] with
  | ctx, Type.Arrow (ty_p, drty_c), cnstrs -> ctx, (ty_p, drty_c), cnstrs
  | _ -> assert false

and abstract2 ~loc (ctx_p1, ty_p1, cnstrs_p1) (ctx_p2, ty_p2, cnstrs_p2) (ctx_c, drty_c, cnstrs_c) =
  match finalize_ty_scheme ~loc ctx_c (Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c)) [
    trim_context ~loc (ctx_p1 @ ctx_p2);
    just cnstrs_p1;
    just cnstrs_p2;
    just cnstrs_c
  ] with
  | ctx, Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c), cnstrs -> ctx, (ty_p1, ty_p2, drty_c), cnstrs
  | _ -> assert false

let beautify_ty_scheme ty_sch = 
  let sbst = Type.beautifying_subst () in
  subst_ty_scheme sbst ty_sch

let beautify_dirty_scheme drty_sch = 
  let sbst = Type.beautifying_subst () in
  let _, (_, ds, _) = pos_neg_dirtyscheme drty_sch in
  ignore (Common.map sbst.Type.dirt_param ds);
  subst_dirty_scheme sbst drty_sch

let extend_non_poly (ts, ds, rs) skeletons =
  let add_skel skel new_ts =
    if List.exists (fun t -> List.mem t ts) skel then
    skel @ new_ts else new_ts
  in
  let ts = List.fold_right add_skel skeletons ts in
  (Common.uniq ts, ds, rs)

let skeletons_non_poly_scheme (ctx, _, cnstrs) =
  let skeletons = Constraints.skeletons cnstrs in
  let non_poly = Common.trio_flatten_map (fun (x, t) -> let pos, neg = Type.pos_neg_params Tctx.get_variances t in pos @@@ neg) ctx in
  let non_poly = extend_non_poly non_poly skeletons in
  skeletons, non_poly

let print_context ctx ppf =
  let print_binding (x, t) ppf =
    Print.print ppf "%t : %t" (CoreSyntax.Variable.print x) (Type.print_ty t)
  in
  Print.sequence ", " print_binding ctx ppf

let print_ty_scheme ty_sch ppf =
  let (ctx, ty, cnstrs) = beautify_ty_scheme ty_sch in
  Print.print ppf "%t |- %t | %t"
    (print_context ctx)
    (Type.print_ty ty)
    (Constraints.print cnstrs)

let print_dirty_scheme ty_sch ppf =
  let (ctx, (ty, drt), cnstrs) = beautify_dirty_scheme ty_sch in
  Print.print ppf "%t |- %t ! %t | %t"
    (print_context ctx)
    (Type.print_ty ty)
    (Type.print_dirt drt)
    (Constraints.print cnstrs)

