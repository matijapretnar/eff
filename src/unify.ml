(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)

let empty_constraint = []

let solve cstr =
  let sbst = ref Type.identity_subst in
  let remaining = ref empty_constraint in
  let rec unify pos t1 t2 =
    let t1 = Type.subst_ty !sbst t1 in
    let t2 = Type.subst_ty !sbst t2 in
    match t1, t2 with

    | (t1, t2) when t1 = t2 -> ()

    | (Type.TyParam p, t) | (t, Type.TyParam p) ->
        if Type.occurs_in_ty p t
        then
          let t1, t2 = Type.beautify2 t1 t2 !remaining in
          Error.typing ~pos
            "This expression has a forbidden cylclic type %t = %t."
            (Print.ty_scheme t1)
            (Print.ty_scheme t2)
        else
          sbst := Type.compose_subst {Type.identity_subst with Type.subst_ty = [(p, t)]} !sbst

    | (Type.Arrow (u1, (v1, drt1)), Type.Arrow (u2, (v2, drt2))) ->
        unify pos v1 v2;
        unify pos u2 u1;
        unify_dirt pos drt1 drt2
        (* XXX Add constraints for dirt *)

    | (Type.Tuple lst1, Type.Tuple lst2)
        when List.length lst1 = List.length lst2 ->
        List.iter2 (unify pos) lst1 lst2

    | ((Type.Apply (t1, (lst1, _, _)), Type.Apply (t2, (lst2, _, _))) |
       (Type.Effect (t1, (lst1, _, _), _), Type.Effect (t2, (lst2, _, _), _)))
        when t1 = t2 && List.length lst1 = List.length lst2  ->
        begin match Tctx.lookup_params t1 with
        | None -> Error.typing ~pos "Undefined type %s" t1
        (* XXX Add constraints for other parameters *)
        | Some (ps, _, _) ->
            List.iter2 (fun (_, (cov, contra)) (ty1, ty2) ->
              begin if cov then
                unify pos ty1 ty2
              end;
              begin if contra then
                unify pos ty2 ty1
              end) ps (List.combine lst1 lst2)
        end

    (* The following two cases cannot be merged into one, as the whole matching
       fails if both types are Apply, but only the second one is transparent. *)
    | (Type.Apply (t1, lst1), t2) when Tctx.transparent ~pos t1 ->
        begin match Tctx.ty_apply ~pos t1 lst1 with
        | Tctx.Inline t -> unify pos t2 t
        | Tctx.Sum _ | Tctx.Record _ | Tctx.Effect _ -> assert false (* None of these are transparent *)
        end

    | (t1, (Type.Apply _ as t2)) ->
        unify pos t2 t1

    | (Type.Handler h1, Type.Handler h2) ->
        unify pos h2.Type.value h1.Type.value;
        unify pos h1.Type.finally h2.Type.finally

    | (t1, t2) ->
        let t1, t2 = Type.beautify2 t1 t2 !remaining in
        Error.typing ~pos
          "This expression has type %t but it should have type %t."
          (Print.ty_scheme t1) (Print.ty_scheme t2)
  and unify_dirt pos drt1 drt2 =
    remaining := Type.DirtConstraint (drt1, drt2, pos) :: !remaining
  and unify_region pos rgn1 rgn2 =
    remaining := Type.RegionConstraint (rgn1, rgn2, pos) :: !remaining
  in
  List.iter (function
    | Type.TypeConstraint (t1, t2, pos) -> unify pos t1 t2
    | Type.DirtConstraint (drt1, drt2, pos) -> unify_dirt pos drt1 drt2;
    | Type.RegionConstraint (rgn1, rgn2, pos) -> unify_region pos rgn1 rgn2)
  (List.rev cstr);
  !sbst, !remaining
