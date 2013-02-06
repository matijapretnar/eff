(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)

let ty_param_less p q (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_ty_constraint p q cnstrs, sbst)
and dirt_param_less ~pos d1 d2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_dirt_constraint d1 d2 cnstrs, sbst)
and region_less ~pos r1 r2 (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_region_constraint r1 r2 cnstrs, sbst)
and region_covers r i (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.add_region_low_bound i r cnstrs, sbst)
and just new_cnstrs (ctx, ty, cnstrs, sbst) =
  (ctx, ty, Type.join_disjoint_constraints new_cnstrs cnstrs, sbst)

let rec add_dirt_substitution ~pos d drt' (ctx, ty, cnstrs, sbst) =
  let drt' = Type.subst_dirt sbst drt' in
  let sbst' = {
    Type.identity_subst with 
    Type.dirt_param = (fun d' -> if d' = d then drt' else Type.simple_dirt d')
  } in
  let (pred, succ, new_dirt_grph) = Type.remove_dirt cnstrs d in
  let cnstrs = {cnstrs with Type.dirt_graph = new_dirt_grph} in
  let ty_sch = (Common.assoc_map (Type.subst_ty sbst') ctx, Type.subst_ty sbst' ty, cnstrs, Type.compose_subst sbst' sbst) in
  let ty_sch = List.fold_right (fun q ty_sch -> dirt_less ~pos (Type.simple_dirt q) drt' ty_sch) pred ty_sch in
  List.fold_right (fun q ty_sch -> dirt_less ~pos drt' (Type.simple_dirt q) ty_sch) succ ty_sch

and presence_less ~pos dt1 dt2 ((ctx, ty, cnstrs, sbst) as ty_sch)  =
  match Type.subst_presence sbst dt1, Type.subst_presence sbst dt2 with
  | (Type.Absent, _ | _, Type.Present) -> ty_sch
  | Type.DirtParam d, Type.Absent ->
      add_dirt_substitution ~pos d { Type.ops = []; Type.rest = Type.Absent} ty_sch 
  | Type.Present, Type.DirtParam d ->
      add_dirt_substitution ~pos d { Type.ops = []; Type.rest = Type.Present} ty_sch 
  | Type.DirtParam d1, Type.DirtParam d2 ->
      dirt_param_less ~pos d1 d2 ty_sch 
  | Type.Present, Type.Absent ->
      Error.typing ~pos "Dirt is present but should be absent."

and dirt_less ~pos drt1 drt2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  let {Type.rest = dt1; Type.ops = ops1} = Type.subst_dirt sbst drt1
  and {Type.rest = dt2; Type.ops = ops2} = Type.subst_dirt sbst drt2 in
  match ops1, ops2 with
  | [], [] -> presence_less ~pos dt1 dt2 ty_sch
  | _, _ ->
      begin
        let add_left (((r, op) as rop), op_dt1) (new_ops2, ty_sch) =
          let op_dt2, new_ops2 =
            match Common.lookup rop ops2 with
            | None ->
              let op_dt2 =
                begin match dt2 with
                | Type.Present -> Type.Present
                | Type.Absent -> Type.Absent
                | Type.DirtParam _ -> Type.DirtParam (Type.fresh_dirt_param ())
                end
                in
                op_dt2, (rop, op_dt2) :: new_ops2
            | Some op_dt2 -> op_dt2, new_ops2
          in
          new_ops2, presence_less ~pos op_dt1 op_dt2 ty_sch
        and add_right (rop, op_dt2) (new_ops1, ty_sch) =
          let op_dt1, new_ops1 =
            match Common.lookup rop ops1 with
            | None ->
              let op_dt1 =
                begin match dt1 with
                | Type.Present -> Type.Present
                | Type.Absent -> Type.Absent
                | Type.DirtParam _ -> Type.DirtParam (Type.fresh_dirt_param ())
                end
                in
                op_dt1, (rop, op_dt1) :: new_ops1
            | Some op_dt1 -> op_dt1, new_ops1
          in
          new_ops1, presence_less ~pos op_dt1 op_dt2 ty_sch
        in
        let new_ops2, ty_sch = List.fold_right add_left ops1 ([], ty_sch) in
        let new_ops1, ((ctx, ty, cnstrs, sbst) as ty_sch) = List.fold_right add_right ops2 ([], ty_sch)
        in
        let ty_sch, dt1 =
          match new_ops1, dt1 with
          | _ :: _, Type.DirtParam d1 ->
              let d1' = Type.fresh_dirt_param () in
              let dt1' = Type.DirtParam d1' in
              let drt1' = { Type.ops = ops1 @ new_ops1; Type.rest = dt1' } in
              add_dirt_substitution ~pos d1 drt1' ty_sch, dt1'
          | _, _ -> ty_sch, dt1
        in
        let ty_sch, dt2 =
          match new_ops2, dt2 with
          | _ :: _, Type.DirtParam d2 ->
              let d2' = Type.fresh_dirt_param () in
              let dt2' = Type.DirtParam d2' in
              let drt2' = { Type.ops = ops2 @ new_ops2; Type.rest = dt2' } in
              add_dirt_substitution ~pos d2 drt2' ty_sch, dt2'
          | _ -> ty_sch, dt2
        in
        presence_less ~pos dt1 dt2 ty_sch
    end

let rec ty_less ~pos ty1 ty2 ((ctx, ty, cnstrs, sbst) as ty_sch) =
  (* XXX Check cyclic types *)
  (* Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
  match Type.subst_ty sbst ty1, Type.subst_ty sbst ty2 with

  | (ty1, ty2) when ty1 = ty2 -> ty_sch

  | (Type.TyParam p, Type.TyParam q) -> ty_param_less p q ty_sch

  | (Type.TyParam p, ty) ->
      let ty' = Type.replace ty in
      ty_less ~pos ty' ty (add_substitution ~pos p ty' ty_sch)

  | (ty, Type.TyParam p) ->
      let ty' = Type.replace ty in
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

  | (Type.Handler ((tyv1, drt1), tyf1), Type.Handler ((tyv2, drt2), tyf2)) ->
      dirt_less ~pos drt2 drt1 (ty_less ~pos tyv2 tyv1 (dirty_less ~pos tyf1 tyf2 ty_sch))

  | (ty1, ty2) ->
      let ty1, ty2 = Type.beautify2 ty1 ty2 in
      Error.typing ~pos "This expression has type %t but it should have type %t." (Print.ty ty1) (Print.ty ty2)

and add_substitution ~pos p ty' (ctx, ty, cnstrs, sbst) =
  let ty' = Type.subst_ty sbst ty' in
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

and dirty_less ~pos (ty1, d1) (ty2, d2) ty_sch =
  (* Print.debug ~pos "Unifying freshness constraints %t <= %t." (Print.fresh_instances nws1) (Print.fresh_instances nws2); *)
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
  | Type.Handler ((ty1, drt1), drty2) -> pos_ty (not is_pos) ty1 @@@ pos_dirt (not is_pos) drt1 @@@ pos_dirty is_pos drty2
  and pos_dirty is_pos (ty, drt) =
    pos_ty is_pos ty @@@ pos_dirt is_pos drt
  and pos_presence is_pos = function
  | Type.Present | Type.Absent -> Trio.empty
  | Type.DirtParam d -> pos_dirt_param is_pos d
  and pos_dirt is_pos drt =
    pos_presence is_pos drt.Type.rest @@@ Trio.flatten_map (fun ((r, _), dt) -> pos_region_param is_pos r @@@ pos_presence is_pos dt) drt.Type.ops
  and pos_dirt_param is_pos p =
    ([], (if is_pos then [p] else []), [])
  and pos_region_param is_pos r =
    ([], [], if is_pos then [r] else [])
  and pos_args is_pos ty_name (tys, drts, rgns) =
    match Tctx.lookup_params ty_name with
    | None -> assert false (* We type-checked before thus all type names are valid. *)
    | Some (ps, ds, rs) ->
        for_parameters pos_ty is_pos ps tys @@@
        for_parameters pos_dirt is_pos ds drts @@@
        for_parameters pos_region_param is_pos rs rgns
  in
  Trio.uniq (pos_ty true ty), Trio.uniq (pos_ty false ty)


let pos_neg_tyscheme (ctx, ty, cnstrs) =
  let add_ctx_pos_neg (_, ctx_ty) (pos, neg) =
    let pos_ctx_ty, neg_ctx_ty = pos_neg_params ctx_ty in
    neg_ctx_ty @@@ pos, pos_ctx_ty @@@ neg
  in
  let (pos, neg) = List.fold_right add_ctx_pos_neg ctx (pos_neg_params ty) in
  let ((_, _, pos_rs) as pos), ((_, _, neg_rs) as neg) = (Trio.uniq pos, Trio.uniq neg) in
  pos, neg

let pos_neg_ty_scheme (ctx, ty, cnstrs, _) =
  pos_neg_tyscheme (ctx, ty, cnstrs)


let collect ((pos_ts, pos_ds, pos_rs), (neg_ts, neg_ds, neg_rs)) (ctx, ty, cnstrs, _) =
  let sbst, cnstrs' = Type.garbage_collect (pos_ts, neg_ts) (pos_ds, neg_ds) (pos_rs, neg_rs) cnstrs in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Type.subst_constraints sbst cnstrs'

let simplify (ctx, drty, cnstrs) =
  let ty = (Type.Arrow (Type.unit_ty, drty)) in
  let ((pos_ts, pos_ds, pos_rs), (neg_ts, neg_ds, neg_rs)) = pos_neg_tyscheme (ctx, ty, cnstrs) in
  let sbst = Type.simplify (pos_ts, neg_ts) (pos_ds, neg_ds) (pos_rs, neg_rs) cnstrs in
  let ty_sch = Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Type.subst_constraints sbst cnstrs in
  match ty_sch with
  | ctx, Type.Arrow (_, drty), cstr -> (ctx, drty, cstr)
  | _ -> assert false


let normalize_context ~pos (ctx, ty, cstr, sbst) =
  let collect (x, ty) ctx =
    match Common.lookup x ctx with
    | None -> (x, ref [ty]) :: ctx
    | Some tys -> tys := ty :: !tys; ctx
  in
  let ctx = List.fold_right collect ctx [] in

  let add (x, tys) (ctx, typ, cnstrs, sbst) =
    match !tys with
    | [] -> assert false
    | [ty] -> ((x, Type.subst_ty sbst ty) :: ctx, typ, cnstrs, sbst)
    | tys ->
        let ty' = Type.fresh_ty () in
        let ctx' = (x, ty') :: ctx in
        List.fold_right (fun ty ty_sch -> ty_less ~pos ty' ty ty_sch) tys (ctx', typ, cnstrs, sbst)
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
