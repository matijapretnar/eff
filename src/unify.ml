(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)

let for_parameters add pos ps lst1 lst2 =
  List.iter2 (fun (_, (cov, contra)) (ty1, ty2) ->
    begin if cov then
      add pos ty1 ty2
    end;
    begin if contra then
      add pos ty2 ty1
    end) ps (List.combine lst1 lst2)


let empty_constraint = []

let constraints_of_graph g =
  let lst = Type.fold_ty (fun p1 p2 pos lst -> (Type.TypeConstraint (p1, p2, pos)) :: lst) g [] in
  let lst = Type.fold_dirt (fun d1 d2 pos lst -> (Type.DirtConstraint (d1, d2, pos)) :: lst) g lst in
  Type.fold_region (fun r1 r2 pos lst -> (Type.RegionConstraint (r1, r2, pos)) :: lst) g lst

let canonize (ctx, ty, initial_grph) =
  let sbst = ref Type.identity_subst in
  (* We keep a list of "final" constraints which are known not to
     generate new constraints, and a list of constraints which still
     need to be resolved. *)
  let grph = ref (Type.empty) in
  let queue = ref (constraints_of_graph initial_grph) in
  let add_constraint = function
    | Type.TypeConstraint (t1, t2, pos) as cnstr ->
      if t1 <> t2 then queue := cnstr :: !queue
    | Type.DirtConstraint (d1, d2, pos) ->
      if d1 <> d2 then grph := Type.add_dirt_constraint ~pos d1 d2 !grph
    | Type.RegionConstraint (r1, r2, pos) ->
      if r1 <> r2 then grph := Type.add_region_constraint ~pos r1 r2 !grph
  in
  let add_ty_constraint pos t1 t2 = add_constraint (Type.TypeConstraint (t1, t2, pos)) in
  let add_region_constraint pos r1 r2 = add_constraint (Type.RegionConstraint (r1, r2, pos)) in
  let add_dirt_constraint pos d1 d2 = add_constraint (Type.DirtConstraint (d1, d2, pos)) in
  let add_substitution p t =
    (* When parameter [p] gets substituted by type [t] the vertex
       [p] must be removed from the graph, and each edge becomes
       a constraint in the queue. *)
    let (pred, succ, new_grph) = Type.remove_ty !grph (Type.TyParam p) in
    grph := {!grph with Type.ty_graph = new_grph};
      List.iter (fun (q, pos) -> add_ty_constraint pos q (Type.TyParam p)) pred ;
      List.iter (fun (q, pos) -> add_ty_constraint pos (Type.TyParam p) q) succ ;
      sbst := Type.compose_subst {
        Type.identity_subst with
        Type.ty_param = (fun p' -> if p' = p then t else Type.TyParam p')
      } !sbst
  in
  let unify pos t1 t2 =
    let t1 = Type.subst_ty !sbst t1 in
    let t2 = Type.subst_ty !sbst t2 in
    match t1, t2 with

    | (t1, t2) when t1 = t2 -> ()

    | (Type.TyParam p, Type.TyParam q) ->
        grph := Type.add_ty_constraint ~pos (Type.TyParam p) (Type.TyParam q) !grph

    | (Type.TyParam p, t) ->
        if false
        (* XXX *)
        (* if Type.occurs_in_ty p t *)
        then
          let t1, t2 = Type.beautify2 t1 t2 in
          Error.typing ~pos
            "This expression has a forbidden cylclic type %t = %t."
            (Print.ty t1)
            (Print.ty t2)
        else
          let t' = Type.refresh t in
          add_substitution p t' ;
          add_ty_constraint pos t' t

    | (t, Type.TyParam p) ->
        (* XXX One should do occurs check on constraints too.
            Consider: [let rec f x = f (x, x)] or [let rec f x = (x, f x)] *)
        if false
        (* XXX *)
        (* if Type.occurs_in_ty p t *)
        then
          let t1, t2 = Type.beautify2 t1 t2 in
          Error.typing ~pos
            "This expression has a forbidden cylclic type %t = %t."
            (Print.ty t1)
            (Print.ty t2)
        else
          let t' = Type.refresh t in
          add_substitution p t' ;
          add_ty_constraint pos t t'

    | (Type.Arrow (u1, (lst1, v1, drt1)), Type.Arrow (u2, (lst2, v2, drt2))) ->
        Print.debug "Unifying %t and %t" (Print.fresh_instances lst1) (Print.fresh_instances lst2);
        (* XXX How do we unify fresh instances? *)
        add_ty_constraint pos v1 v2;
        add_ty_constraint pos u2 u1;
        add_dirt_constraint pos (Type.DirtParam drt1) (Type.DirtParam drt2)

    | (Type.Tuple lst1, Type.Tuple lst2)
        when List.length lst1 = List.length lst2 ->
        List.iter2 (add_ty_constraint pos) lst1 lst2

    | (Type.Apply (t1, (ts1, drts1, rgns1)), Type.Apply (t2, (ts2, drts2, rgns2))) when t1 = t2 ->
      (* NB: it is assumed here that
         List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
        begin match Tctx.lookup_params t1 with
        | None -> Error.typing ~pos "Undefined type %s" t1
        | Some (ps, ds, rs) ->
            for_parameters add_ty_constraint pos ps ts1 ts2;
            for_parameters add_dirt_constraint pos ds (List.map (fun d -> Type.DirtParam d) drts1) (List.map (fun d -> Type.DirtParam d) drts2);
            for_parameters add_region_constraint pos rs (List.map (fun r -> Type.RegionParam r) rgns1) (List.map (fun r -> Type.RegionParam r) rgns2)
        end

    | (Type.Effect (t1, (ts1, drts1, rgns1), rgn1), Type.Effect (t2, (ts2, drts2, rgns2), rgn2)) when t1 = t2 ->
        (* NB: it is assumed here that
           && List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
        begin match Tctx.lookup_params t1 with
        | None -> Error.typing ~pos "Undefined type %s" t1
        | Some (ps, ds, rs) ->
            add_region_constraint pos (Type.RegionParam rgn1) (Type.RegionParam rgn2);
            for_parameters add_ty_constraint pos ps ts1 ts2;
            for_parameters add_dirt_constraint pos ds (List.map (fun d -> Type.DirtParam d) drts1) (List.map (fun d -> Type.DirtParam d) drts2);
            for_parameters add_region_constraint pos rs (List.map (fun r -> Type.RegionParam r) rgns1) (List.map (fun r -> Type.RegionParam r) rgns2)
        end

    (* The following two cases cannot be merged into one, as the whole matching
       fails if both types are Apply, but only the second one is transparent. *)
    | (Type.Apply (t1, lst1), t2) when Tctx.transparent ~pos t1 ->
        begin match Tctx.ty_apply ~pos t1 lst1 with
        | Tctx.Inline t -> add_ty_constraint pos t2 t
        | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
        end

    | (t2, Type.Apply (t1, lst1)) when Tctx.transparent ~pos t1 ->
        begin match Tctx.ty_apply ~pos t1 lst1 with
        | Tctx.Inline t -> add_ty_constraint pos t t2
        | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
        end

    | (Type.Handler (tv1, tf1), Type.Handler (tv2, tf2)) ->
        add_ty_constraint pos tv2 tv1;
        add_ty_constraint pos tf1 tf2

    | (t1, t2) ->
          let t1, t2 = Type.beautify2 t1 t2 in
          Error.typing ~pos
            "This expression has type %t but it should have type %t."
            (Print.ty t1)
            (Print.ty t2)

  and unify_dirt pos drt1 drt2 =
    add_dirt_constraint pos drt1 drt2

  and unify_region pos rgn1 rgn2 =
    add_region_constraint pos rgn1 rgn2

  in

  let rec loop () =
    match !queue with
      | [] -> (Common.assoc_map (Type.subst_ty !sbst) ctx, Type.subst_ty !sbst ty, !grph)
      | cnstr :: cnstrs ->
        queue := cnstrs ;
        begin match cnstr with
          | Type.TypeConstraint (t1, t2, pos) -> unify pos t1 t2
          | Type.DirtConstraint (drt1, drt2, pos) -> unify_dirt pos drt1 drt2;
          | Type.RegionConstraint (rgn1, rgn2, pos) -> unify_region pos rgn1 rgn2
        end ;
        loop ()
  in
    loop ()

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
  let ty_p p q pos = match p, q with
    | Type.TyParam p, Type.TyParam q -> List.mem p neg_ts && List.mem q pos_ts
    | _, _ -> assert false
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

let normalize_context ~pos (ctx, ty, cstr) =
  let add (x, ty) (ctx, cnstrs) =
    match Common.lookup x ctx with
    | None ->
        let ty' = Type.fresh_ty () in
        ((x, ty') :: ctx, Type.add_ty_constraint ~pos ty' ty cnstrs)
    | Some ty' ->
        (ctx, Type.add_ty_constraint ~pos ty' ty cnstrs)
  in
  let ctx, cstr = List.fold_right add ctx ([], cstr) in
  (ctx, ty, cstr)

let normalize_ty_scheme ~pos ty_sch =
  let ctx, ty, cstr = normalize_context ~pos ty_sch in
  let ctx, ty, cstr = canonize (ctx, ty, cstr) in
  let pos, neg = List.fold_right (fun (_, t) (pos, neg) ->
      let pos_t, neg_t = pos_neg_params t in
      neg_t @@@ pos, pos_t @@@ neg) ctx (pos_neg_params ty) in
  let pos, neg = Trio.uniq pos, Trio.uniq neg in
  (ctx, ty, collect pos neg cstr)

let normalize_dirty_scheme ~pos (ctx, drty, cstr) =
  match normalize_ty_scheme ~pos (ctx, Type.Arrow (Type.unit_ty, drty), cstr) with
  | ctx, Type.Arrow (_, drty), cstr -> (ctx, drty, cstr)
  | _ -> assert false
