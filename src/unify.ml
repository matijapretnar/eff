(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)

let empty_constraint = []

let for_parameters add pos ps lst1 lst2 =
  List.iter2 (fun (_, (cov, contra)) (ty1, ty2) ->
    begin if cov then
      add pos ty1 ty2
    end;
    begin if contra then
      add pos ty2 ty1
    end) ps (List.combine lst1 lst2)

let solve initial_cnstrs =
  let sbst = ref Type.identity_subst in
  (* We keep a list of "final" constraints which are known not to
     generate new constraints, and a list of constraints which still
     need to be resolved. *)
  let cnstr_final = ref empty_constraint in
  let cnstr_queue = ref initial_cnstrs in
  let add_constraint = function
    | Type.TypeConstraint (t1, t2, _) as cnstr ->
      if t1 <> t2 then
        begin match t1, t2 with
          | Type.TyParam _, Type.TyParam _ -> cnstr_final := cnstr :: !cnstr_final
          | _, _ -> cnstr_queue := cnstr :: !cnstr_queue
        end
    | Type.DirtConstraint (d1, d2, _) as cnstr ->
      if d1 <> d2 then cnstr_final := cnstr :: !cnstr_final
    | Type.RegionConstraint (r1, r2, _) as cnstr ->
      if r1 <> r2 then cnstr_final := cnstr :: !cnstr_final
  in
  let add_ty_constraint pos t1 t2 = add_constraint (Type.TypeConstraint (t1, t2, pos)) in
  let add_region_constraint pos r1 r2 = add_constraint (Type.RegionConstraint (r1, r2, pos)) in
  let add_dirt_constraint pos d1 d2 = add_constraint (Type.DirtConstraint (d1, d2, pos)) in
  let add_substitution p t =
    let lst = !cnstr_final in
      cnstr_final := [] ;
      List.iter
        (function
          | (Type.DirtConstraint _ | Type.RegionConstraint _) as cnstr -> add_constraint cnstr
          | Type.TypeConstraint (Type.TyParam q1, Type.TyParam q2, pos) as cnstr ->
            if p <> q1 && p <> q2
            then add_constraint cnstr
            else cnstr_queue := cnstr :: !cnstr_queue (* Unify is going to perform the substitution. *)
          | Type.TypeConstraint _ ->
            assert false (* XXX Adapt Type.constraint so that only inequalities between type parameters are expressible. *)
        )
        lst ;
      sbst := Type.compose_subst {Type.identity_subst with Type.subst_ty = [(p, t)]} !sbst
  in
  let unify pos t1 t2 =
    let t1 = Type.subst_ty !sbst t1 in
    let t2 = Type.subst_ty !sbst t2 in
    match t1, t2 with

    | (t1, t2) when t1 = t2 -> ()

    | (Type.TyParam p, Type.TyParam q) -> add_ty_constraint pos t1 t2

    | (Type.TyParam p, t) ->
        if Type.occurs_in_ty p t
        then
          (* XXX Why do we we pass !cntr_final if it does not get printed? *)
          let t1, t2 = Type.beautify2 t1 t2 !cnstr_final in
          Error.typing ~pos
            "This expression has a forbidden cylclic type %t = %t."
            (Print.ty_scheme t1)
            (Print.ty_scheme t2)
        else
          let (_, t', _) = Type.refresh (Type.free_params t []) t [] in
          add_substitution p t' ;
          add_ty_constraint pos t' t

    | (t, Type.TyParam p) ->
        if Type.occurs_in_ty p t
        then
          (* XXX Why do we we pass !cntr_final if it does not get printed? *)
          let t1, t2 = Type.beautify2 t1 t2 !cnstr_final in
          Error.typing ~pos
            "This expression has a forbidden cylclic type %t = %t."
            (Print.ty_scheme t1)
            (Print.ty_scheme t2)
        else
          let (_, t', _) = Type.refresh (Type.free_params t []) t [] in
          add_substitution p t' ;
          add_ty_constraint pos t t'

    | (Type.Arrow (u1, (lst1, v1, drt1)), Type.Arrow (u2, (lst2, v2, drt2))) ->
        Print.debug "Unifying %t and %t" (Print.fresh_instances lst1) (Print.fresh_instances lst2);
        (* XXX How do we unify fresh instances? *)
        add_ty_constraint pos v1 v2;
        add_ty_constraint pos u2 u1;
        add_dirt_constraint pos drt1 drt2

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
            for_parameters add_dirt_constraint pos ds drts1 drts2;
            for_parameters add_region_constraint pos rs rgns1 rgns2
        end

    | (Type.Effect (t1, (ts1, drts1, rgns1), rgn1), Type.Effect (t2, (ts2, drts2, rgns2), rgn2)) when t1 = t2 ->
        (* NB: it is assumed here that
           && List.length ts1 = List.length ts2 && List.length drts1 = List.length drts2 && List.length rgns1 = List.length rgns2 *)
        begin match Tctx.lookup_params t1 with
        | None -> Error.typing ~pos "Undefined type %s" t1
        | Some (ps, ds, rs) ->
            add_region_constraint pos rgn1 rgn2;
            for_parameters add_ty_constraint pos ps ts1 ts2;
            for_parameters add_dirt_constraint pos ds drts1 drts2;
            for_parameters add_region_constraint pos rs rgns1 rgns2
        end

    (* The following two cases cannot be merged into one, as the whole matching
       fails if both types are Apply, but only the second one is transparent. *)
    | (Type.Apply (t1, lst1), t2) when Tctx.transparent ~pos t1 ->
        begin match Tctx.ty_apply ~pos t1 lst1 with
        | Tctx.Inline t -> add_ty_constraint pos t2 t
        | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
        end

    | (t1, (Type.Apply _ as t2)) ->
        add_ty_constraint pos t2 t1

    | (Type.Handler h1, Type.Handler h2) ->
        add_ty_constraint pos h2.Type.value h1.Type.value;
        add_ty_constraint pos h1.Type.finally h2.Type.finally

    | (t1, t2) ->
        (* XXX Why do we pass !cnstr_final if it does not get printed? *)
        let t1, t2 = Type.beautify2 t1 t2 !cnstr_final in
        Error.typing ~pos
          "This expression has type %t but it should have type %t."
          (Print.ty_scheme t1) (Print.ty_scheme t2)

  and unify_dirt pos drt1 drt2 =
    add_dirt_constraint pos drt1 drt2

  and unify_region pos rgn1 rgn2 =
    add_region_constraint pos rgn1 rgn2

  in

  let rec loop () =
    match !cnstr_queue with
      | [] -> !sbst, Common.uniq !cnstr_final
      | cnstr :: cnstrs ->
        cnstr_queue := cnstrs ;
        begin match cnstr with
          | Type.TypeConstraint (t1, t2, pos) -> unify pos t1 t2
          | Type.DirtConstraint (drt1, drt2, pos) -> unify_dirt pos drt1 drt2;
          | Type.RegionConstraint (rgn1, rgn2, pos) -> unify_region pos rgn1 rgn2
        end ;
        loop ()
  in
    loop ()
