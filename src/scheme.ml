type substitution = {
  ty_param : (Type.ty_param, Type.ty) Common.assoc;
  dirt_param : (Type.dirt_param, Type.dirt) Common.assoc;
}

type context = (Syntax.variable, Type.ty) Common.assoc
type ty_scheme = context * Type.ty * Constraints.t
type dirty_scheme = context * Type.dirty * Constraints.t
type t = context * Type.ty * Constraints.t * substitution
type change = t -> t

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst = function
  | Type.Apply (ty_name, args) -> Type.Apply (ty_name, subst_args sbst args)
  | Type.Effect (ty_name, args, r) -> Type.Effect (ty_name, subst_args sbst args, r)
  | Type.TyParam p ->
      begin match Common.lookup p sbst.ty_param with
      | Some t -> t
      | None -> Type.TyParam p
      end
  | Type.Basic _ as ty -> ty
  | Type.Tuple tys -> Type.Tuple (Common.map (subst_ty sbst) tys)
  | Type.Arrow (ty1, (ty2, drt)) -> Type.Arrow (subst_ty sbst ty1, (subst_ty sbst ty2, subst_dirt sbst drt))
  | Type.Handler (drty1, drty2) -> Type.Handler (subst_dirty sbst drty1, subst_dirty sbst drty2)

and subst_dirt sbst drt =
  match Common.lookup drt.Type.rest sbst.dirt_param with
  | Some { Type.ops = new_ops; Type.rest = new_rest } -> { Type.ops = new_ops @ drt.Type.ops; Type.rest = new_rest }
  | None -> drt

and subst_dirty sbst (ty, drt) = (subst_ty sbst ty, subst_dirt sbst drt)

and subst_args sbst (tys, drts, rs) =
  (Common.map (subst_ty sbst) tys, Common.map (subst_dirt sbst) drts, rs)

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst =
  {
    ty_param = [];
    dirt_param = []
  }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = sbst1.ty_param @ (Common.assoc_map (subst_ty sbst1) sbst2.ty_param);
    dirt_param = sbst1.dirt_param @ (Common.assoc_map (subst_dirt sbst1) sbst2.dirt_param);
  }

let beautify2 ty1 ty2 cnstrs =
  let sbst = Type.beautifying_subst () in
  let ty1 = Type.subst_ty sbst ty1 in
  let ty2 = Type.subst_ty sbst ty2 in
  let cnstrs = Constraints.subst sbst cnstrs in
  let skeletons = ConstraintsTy.skeletons cnstrs.Constraints.ty in
  (ty1, ty2, skeletons)


let refresh (ctx, ty, cnstrs) =
  let sbst = Type.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Constraints.subst sbst cnstrs

let ty_param_less p q (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_ty_constraint p q cnstrs, sbst)
and dirt_param_less d1 d2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_dirt_constraint d1 d2 cnstrs, sbst)
and just new_cnstrs (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.union new_cnstrs cnstrs, sbst)
and region_param_less r1 r2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_region_constraint r1 r2 [] cnstrs, sbst)
and add_handled_constraint r1 r2 rs (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_region_constraint r1 r2 rs cnstrs, sbst)
and add_instance_constraint iota r (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Constraints.add_instance_constraint iota r [] cnstrs, sbst)

let rec explode_dirt ~pos p ({Type.ops = ops} as drt_new) (ctx, ty, cnstrs, sbst) =
  if ops = [] then (ctx, ty, cnstrs, sbst) else
  let (new_drt_grph, ps, skel) = ConstraintsDirt.remove_skeleton p cnstrs.Constraints.dirt in
  let drts' = List.map (fun p -> (p, Type.subst_dirt (Type.refreshing_subst ()) drt_new)) ps in
  let sbst' = {
    identity_subst with 
    dirt_param = drts'
  } in
  let cnstrs = {cnstrs with Constraints.dirt = new_drt_grph} in
  let ty_sch = (Common.assoc_map (subst_ty sbst') ctx, subst_ty sbst' ty, cnstrs, compose_subst sbst' sbst) in
  List.fold_right (fun (p, q) ty_sch -> dirt_less ~pos (Type.simple_dirt p) (Type.simple_dirt q) ty_sch) skel ty_sch

and dirt_less ~pos drt1 drt2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  let {Type.ops = ops1; Type.rest = rest1} = subst_dirt sbst drt1
  and {Type.ops = ops2; Type.rest = rest2} = subst_dirt sbst drt2 in
  let new_ops ops1 ops2 =
    let ops2 = List.map fst ops2 in
    let add_op (op, _) news =
      if List.mem op ops2 then news else (op, Type.fresh_region_param ()) :: news
    in
    List.fold_right add_op ops1 []
  in
  let new_ops1 = new_ops ops2 ops1
  and new_ops2 = new_ops ops1 ops2 in
  match new_ops1, new_ops2 with
  | [], [] ->
      let op_less (op, dt1) ty_sch =
        begin match Common.lookup op ops2 with
        | Some dt2 -> region_param_less dt1 dt2 ty_sch
        | None -> assert false
      end
      in
      List.fold_right op_less ops1 (dirt_param_less rest1 rest2 ty_sch)
  | _, _ ->
      dirt_less ~pos drt1 drt2 (
      explode_dirt ~pos rest1 {Type.ops = new_ops1; Type.rest = Type.fresh_dirt_param ()}
      (explode_dirt ~pos rest2 {Type.ops = new_ops2; Type.rest = Type.fresh_dirt_param ()} ty_sch))

let rec ty_less ~pos ty1 ty2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  match subst_ty sbst ty1, subst_ty sbst ty2 with

  | (ty1, ty2) when ty1 = ty2 -> ty_sch

  | (Type.TyParam p, Type.TyParam q) -> ty_param_less p q ty_sch

  | (Type.TyParam p, ty) ->
      ty_less ~pos (Type.TyParam p) ty (explode_skeleton ~pos p ty ty_sch)

  | (ty, Type.TyParam p) ->
      ty_less ~pos ty (Type.TyParam p) (explode_skeleton ~pos p ty ty_sch)

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
          region_param_less rgn1 rgn2 (
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

  | (Type.Handler ((tyv1, drt1), tyf1), Type.Handler ((tyv2, drt2), tyf2)) ->
      dirt_less ~pos drt2 drt1 (ty_less ~pos tyv2 tyv1 (dirty_less ~pos tyf1 tyf2 ty_sch))

  | (ty1, ty2) ->
      let ty1, ty2, skeletons = beautify2 ty1 ty2 cnstrs in
      Error.typing ~pos "This expression has type %t but it should have type %t." (Type.print skeletons ty1) (Type.print skeletons ty2)

and explode_skeleton ~pos p ty_new (ctx, ty, cnstrs, sbst) =
  let (new_ty_grph, ps, skel) = ConstraintsTy.remove_skeleton p cnstrs.Constraints.ty in
  let tys' = List.map (fun p -> (p, Type.refresh ty_new)) ps in
  let sbst' = {
    identity_subst with 
    ty_param = tys'
  } in
  let cnstrs = {cnstrs with Constraints.ty = new_ty_grph} in
  let ty_sch = (Common.assoc_map (subst_ty sbst') ctx, subst_ty sbst' ty, cnstrs, compose_subst sbst' sbst) in
  List.fold_right (fun (p, q) ty_sch -> ty_less ~pos (Type.TyParam p) (Type.TyParam q) ty_sch) skel ty_sch

and args_less ~pos (ps, ds, rs) (ts1, ds1, rs1) (ts2, ds2, rs2) ty_sch =
  (* NB: it is assumed here that
     List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
  let for_parameters add ps lst1 lst2 ty_sch =
    List.fold_right2 (fun (_, (cov, contra)) (ty1, ty2) ty_sch ->
                        let ty_sch = if cov then add ty1 ty2 ty_sch else ty_sch in
                        if contra then add ty2 ty1 ty_sch else ty_sch) ps (List.combine lst1 lst2) ty_sch
  in
  let ty_sch = for_parameters (ty_less ~pos) ps ts1 ts2 ty_sch in
  let ty_sch = for_parameters (dirt_less ~pos) ds ds1 ds2 ty_sch in
  for_parameters region_param_less rs rs1 rs2 ty_sch

and dirty_less ~pos (ty1, d1) (ty2, d2) ty_sch =
  ty_less ~pos ty1 ty2 (dirt_less ~pos d1 d2 ty_sch)

let trim_context ~pos ctx_p (ctx, ty, cnstrs, sbst) =
  let trim (x, t) (ctx, ty, cnstrs, sbst) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs, sbst)
    | Some u -> ty_less ~pos u t (ctx, ty, cnstrs, sbst)
  in
  List.fold_right trim ctx ([], ty, cnstrs, sbst)

let remove_context ~pos ctx_p (ctx, ty, cnstrs, sbst) =
  let trim (x, t) (ctx, ty, cnstrs, sbst) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs, sbst)
    | Some u -> (ctx, ty, cnstrs, sbst)
  in
  List.fold_right trim ctx ([], ty, cnstrs, sbst)

let less_context ~pos ctx_p (ctx, ty, cnstrs, sbst) =
  let trim (x, t) (ctx, ty, cnstrs, sbst) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs, sbst)
    | Some u -> ty_less ~pos u t ((x, u) :: ctx, ty, cnstrs, sbst)
  in
  List.fold_right trim ctx ([], ty, cnstrs, sbst)


let (@@@) = Trio.append

let pos_neg_tyscheme (ctx, ty, cnstrs) =
  let add_ctx_pos_neg (_, ctx_ty) (pos, neg) =
    let pos_ctx_ty, neg_ctx_ty = Type.pos_neg_params Tctx.get_variances ctx_ty in
    neg_ctx_ty @@@ pos, pos_ctx_ty @@@ neg
  in
  let (((_, _, pos_rs) as pos), ((_, _, neg_rs) as neg)) = List.fold_right add_ctx_pos_neg ctx (Type.pos_neg_params Tctx.get_variances ty) in
  let pos = ([], [], ConstraintsRegion.pos_handled pos_rs neg_rs cnstrs.Constraints.region) @@@ pos in
  Trio.uniq pos, Trio.uniq neg

let pos_neg_dirtyscheme (ctx, drty, cnstrs) =
  pos_neg_tyscheme (ctx, Type.Arrow (Type.unit_ty, drty), cnstrs)

let garbage_collect pos neg (ctx, ty, cnstrs) =
  ctx, ty, Constraints.garbage_collect pos neg cnstrs

let normalize_context ~pos (ctx, ty, cnstrs, sbst) =
  let collect (x, ty) ctx =
    match Common.lookup x ctx with
    | None -> (x, ref [ty]) :: ctx
    | Some tys -> tys := ty :: !tys; ctx
  in
  let ctx = List.fold_right collect ctx [] in

  let add (x, tys) (ctx, typ, cnstrs, sbst) =
    match !tys with
    | [] -> assert false
    | [ty] -> ((x, ty) :: ctx, typ, cnstrs, sbst)
    | tys ->
        let ty' = Type.fresh_ty () in
        let ctx' = (x, ty') :: ctx in
        List.fold_right (fun ty ty_sch -> ty_less ~pos ty' ty ty_sch) tys (ctx', typ, cnstrs, sbst)
  in
  List.fold_right add ctx ([], ty, cnstrs, sbst)

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
  let ctx, ty, cnstrs, sbst = List.fold_right Common.id chngs (ctx, ty, Constraints.empty, identity_subst) in
  if sbst = identity_subst then
    (ctx, ty, cnstrs)
  else
    let ty = subst_ty sbst ty in
    let ctx = Common.assoc_map (subst_ty sbst) ctx in
    (ctx, ty, cnstrs)

let finalize_ty_scheme ~pos ctx ty chngs =
  let ty_sch = finalize ctx ty (normalize_context ~pos :: chngs) in
  let pos, neg = pos_neg_tyscheme ty_sch in
  garbage_collect pos neg ty_sch

let finalize_dirty_scheme ~pos ctx drty chngs =
  match finalize_ty_scheme ~pos ctx (Type.Arrow (Type.unit_ty, drty)) chngs with
  | ctx, Type.Arrow (_, drty), cnstrs -> (ctx, drty, cnstrs)
  | _ -> assert false

let add_to_top ~pos ctx cnstrs (ctx_c, drty_c, cnstrs_c) =
  finalize_dirty_scheme ~pos (ctx @ ctx_c) drty_c ([
    just cnstrs_c;
    just cnstrs
  ])

let finalize_pattern_scheme ctx ty chngs =
  let ty_sch = finalize ctx ty chngs in
  (* Note that we change the polarities in pattern types *)
  let neg, pos = pos_neg_tyscheme ty_sch in
  garbage_collect pos neg ty_sch


let context skeletons ctx ppf =
  match ctx with
  | [] -> ()
  | _ -> Print.print ppf "(@[%t@]).@ " (Print.sequence ", " (fun (x, t) ppf -> Print.print ppf "%t : %t" (Print.variable x) (Type.print skeletons t)) ctx)

let extend_non_poly (ts, ds, rs) skeletons =
  let add_skel skel new_ts =
    if List.exists (fun t -> List.mem t ts) skel then
    skel @ new_ts else new_ts
  in
  let ts = List.fold_right add_skel skeletons ts in
  (Common.uniq ts, ds, rs)

let show_dirt_param ~non_poly:(_, ds, _) (ctx, ty, cnstrs) =
  let (_, pos, _), (_, neg, _) = pos_neg_tyscheme (ctx, ty, cnstrs) in
  fun ((Type.Dirt_Param k) as p) ->
    if List.mem p neg then
      Some (fun ppf -> (Symbols.dirt_param k (List.mem p ds) ppf))
    else if (List.mem p pos && ConstraintsDirt.get_prec p cnstrs.Constraints.dirt != []) then
      Some (fun ppf -> Print.print ppf "%t" (Print.sequence (Symbols.union ()) (fun (Type.Dirt_Param k) ppf -> (Symbols.dirt_param k (List.mem p ds) ppf)) (ConstraintsDirt.get_prec p cnstrs.Constraints.dirt)))
    else
      None

let print_ty_scheme ty_sch ppf =
  let sbst = Type.beautifying_subst () in
  let _, (_, ds, _) = pos_neg_tyscheme ty_sch in
  ignore (Common.map sbst.Type.dirt_param ds);
  let (ctx, ty, cnstrs) = subst_ty_scheme sbst ty_sch in
  let skeletons = ConstraintsTy.skeletons cnstrs.Constraints.ty in
  let non_poly = Trio.flatten_map (fun (x, t) -> let pos, neg = Type.pos_neg_params Tctx.get_variances t in pos @@@ neg) ctx in
  let non_poly = extend_non_poly non_poly skeletons in
  let show_dirt_param = show_dirt_param (ctx, ty, cnstrs) ~non_poly in
  if !Type.effects then
    Print.print ppf "%t%t"
      (Type.print ~show_dirt_param skeletons ty)
      (ConstraintsRegion.print ~non_poly cnstrs.Constraints.region)
  else
    Type.print ~non_poly skeletons ty ppf

let print_dirty_scheme drty_sch ppf =
  let sbst = Type.beautifying_subst () in
  let _, (_, ds, _) = pos_neg_dirtyscheme drty_sch in
  ignore (Common.map sbst.Type.dirt_param ds);
  let (ctx, (ty, drt), cnstrs) = subst_dirty_scheme sbst drty_sch in
  let skeletons = ConstraintsTy.skeletons cnstrs.Constraints.ty in
  let non_poly = Trio.flatten_map (fun (x, t) -> let pos, neg = Type.pos_neg_params Tctx.get_variances t in pos @@@ neg) ctx in
  let non_poly = extend_non_poly non_poly skeletons in
  let show_dirt_param = show_dirt_param (ctx, (Type.Arrow (Type.unit_ty, (ty, drt))), cnstrs) ~non_poly in
  if !Type.effects then
    if Type.show_dirt show_dirt_param drt then
      Print.print ppf "%t ! %t%t"
        (Type.print ~show_dirt_param skeletons ty)
        (Type.print_dirt ~non_poly ~show_dirt_param drt)
        (ConstraintsRegion.print ~non_poly cnstrs.Constraints.region)
    else
      Print.print ppf "%t%t"
        (Type.print ~show_dirt_param skeletons ty)
        (ConstraintsRegion.print ~non_poly cnstrs.Constraints.region)
  else
    Type.print ~non_poly skeletons ty ppf
