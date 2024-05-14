open Utils
open Language

(* A bag/list of constraints *)
type t = {
  skeleton_equalities : (Skeleton.t * Skeleton.t) list;
  dirt_equalities : (Dirt.t * Dirt.t) list;
  dirt_inequalities : (Type.DirtCoercionParam.t * Type.ct_dirt) list;
  ty_equalities : (Type.ty * Type.ty) list;
  ty_inequalities : (Type.TyCoercionParam.t * Type.ct_ty) list;
  resolved : Constraints.t;
}

let empty =
  {
    skeleton_equalities = [];
    dirt_equalities = [];
    dirt_inequalities = [];
    ty_equalities = [];
    ty_inequalities = [];
    resolved = Constraints.empty;
  }

let from_resolved resolved = { empty with resolved }
let change_resolved f cnstrs = { cnstrs with resolved = f cnstrs.resolved }

let add_skeleton_equality (sk1, sk2) cons =
  {
    cons with
    skeleton_equalities =
      ( Substitution.apply_substitutions_to_skeleton cons.resolved.substitution
          sk1,
        Substitution.apply_substitutions_to_skeleton cons.resolved.substitution
          sk2 )
      :: cons.skeleton_equalities;
  }

let add_dirt_equality (drt1, drt2) cons =
  {
    cons with
    dirt_equalities =
      ( Substitution.apply_substitutions_to_dirt cons.resolved.substitution drt1,
        Substitution.apply_substitutions_to_dirt cons.resolved.substitution drt2
      )
      :: cons.dirt_equalities;
  }

let add_dirt_inequality (w, (drt1, drt2)) cons =
  {
    cons with
    dirt_inequalities =
      ( w,
        ( Substitution.apply_substitutions_to_dirt cons.resolved.substitution
            drt1,
          Substitution.apply_substitutions_to_dirt cons.resolved.substitution
            drt2 ) )
      :: cons.dirt_inequalities;
  }

let add_ty_equality (ty1, ty2) cons =
  {
    cons with
    ty_equalities =
      ( Substitution.apply_substitutions_to_type cons.resolved.substitution ty1,
        Substitution.apply_substitutions_to_type cons.resolved.substitution ty2
      )
      :: cons.ty_equalities;
  }

let add_ty_inequality (w, (ty1, ty2)) cons =
  {
    cons with
    ty_inequalities =
      ( w,
        ( Substitution.apply_substitutions_to_type cons.resolved.substitution ty1,
          Substitution.apply_substitutions_to_type cons.resolved.substitution
            ty2 ) )
      :: cons.ty_inequalities;
  }

let print c =
  let print_skeleton_equality (sk1, sk2) ppf =
    Print.print ppf "%t = %t" (Skeleton.print sk1) (Skeleton.print sk2)
  and print_dirt_equality (drt1, drt2) ppf =
    Print.print ppf "%t = %t" (Dirt.print drt1) (Dirt.print drt2)
  and print_dirt_inequality (p, (ty1, ty2)) ppf =
    Print.print ppf "%t: (%t ≤ %t)"
      (Type.DirtCoercionParam.print p)
      (Dirt.print ty1) (Dirt.print ty2)
  and print_ty_equality (ty1, ty2) ppf =
    Print.print ppf "%t = %t" (Type.print_ty ty1) (Type.print_ty ty2)
  and print_ty_inequality (p, (ty1, ty2)) ppf =
    Print.print ppf "%t: (%t ≤ %t)"
      (Type.TyCoercionParam.print p)
      (Type.print_ty ty1) (Type.print_ty ty2)
  in
  [
    List.map print_skeleton_equality c.skeleton_equalities;
    List.map print_dirt_equality c.dirt_equalities;
    List.map print_dirt_inequality c.dirt_inequalities;
    List.map print_ty_equality c.ty_equalities;
    List.map print_ty_inequality c.ty_inequalities;
  ]
  |> List.concat
  |> Print.printer_sequence ", "

let free_params cons =
  Type.Params.union_map
    (fun (sk1, sk2) ->
      Type.Params.union
        (Type.free_params_skeleton sk1)
        (Type.free_params_skeleton sk2))
    cons.skeleton_equalities
  |> Type.Params.union
       (Type.Params.union_map
          (fun (drt1, drt2) ->
            Type.Params.union
              (Type.free_params_dirt drt1)
              (Type.free_params_dirt drt2))
          cons.dirt_equalities)
  |> Type.Params.union
       (Type.Params.union_map
          (fun (_, ct) -> Type.free_params_ct_dirt ct)
          cons.dirt_inequalities)
  |> Type.Params.union
       (Type.Params.union_map
          (fun (ty1, ty2) ->
            Type.Params.union (Type.free_params_ty ty1)
              (Type.free_params_ty ty2))
          cons.ty_equalities)
  |> Type.Params.union
       (Type.Params.union_map
          (fun (_, ct) -> Type.free_params_ct_ty ct)
          cons.ty_inequalities)

let apply_substitution sub unresolved =
  let add_substituted_ty_constraint s t1 t2 w ty1 ty2 unresolved =
    let ty1', ty2' =
      ( Substitution.apply_substitutions_to_type sub ty1,
        Substitution.apply_substitutions_to_type sub ty2 )
    in
    if Type.equal_ty ty1 ty1' && Type.equal_ty ty2 ty2' then
      change_resolved (Constraints.add_ty_constraint s t1 t2 w) unresolved
    else add_ty_inequality (w, (ty1', ty2')) unresolved
  and add_substituted_dirt_constraint d1 d2 w effs drt1 drt2 unresolved =
    let drt1', drt2' =
      ( Substitution.apply_substitutions_to_dirt sub drt1,
        Substitution.apply_substitutions_to_dirt sub drt2 )
    in
    if Type.equal_dirt drt1 drt1' && Type.equal_dirt drt2 drt2' then
      change_resolved (Constraints.add_dirt_constraint d1 d2 w effs) unresolved
    else add_dirt_inequality (w, (drt1', drt2')) unresolved
  in
  {
    skeleton_equalities =
      List.map
        (fun (skel1, skel2) ->
          ( Substitution.apply_substitutions_to_skeleton sub skel1,
            Substitution.apply_substitutions_to_skeleton sub skel2 ))
        unresolved.skeleton_equalities;
    dirt_equalities =
      List.map
        (fun (drt1, drt2) ->
          ( Substitution.apply_substitutions_to_dirt sub drt1,
            Substitution.apply_substitutions_to_dirt sub drt2 ))
        unresolved.dirt_equalities;
    dirt_inequalities =
      List.map
        (fun (coer_p, (drt1, drt2)) ->
          ( coer_p,
            ( Substitution.apply_substitutions_to_dirt sub drt1,
              Substitution.apply_substitutions_to_dirt sub drt2 ) ))
        unresolved.dirt_inequalities;
    ty_equalities =
      List.map
        (fun (ty1, ty2) ->
          ( Substitution.apply_substitutions_to_type sub ty1,
            Substitution.apply_substitutions_to_type sub ty2 ))
        unresolved.ty_equalities;
    ty_inequalities =
      List.map
        (fun (coer_p, (ty1, ty2)) ->
          ( coer_p,
            ( Substitution.apply_substitutions_to_type sub ty1,
              Substitution.apply_substitutions_to_type sub ty2 ) ))
        unresolved.ty_inequalities;
    resolved =
      {
        Constraints.empty with
        substitution = Substitution.merge sub unresolved.resolved.substitution;
      };
  }
  |> Constraints.TyConstraints.fold_expanded add_substituted_ty_constraint
       unresolved.resolved.Constraints.ty_constraints
  |> Constraints.DirtConstraints.fold_expanded add_substituted_dirt_constraint
       unresolved.resolved.Constraints.dirt_constraints

let change_subst f cnstrs =
  let sub = f cnstrs.resolved.substitution in
  apply_substitution sub cnstrs

let fresh_ty_coer cnstrs cons =
  let param = Type.TyCoercionParam.fresh () in
  ( { term = TyCoercion.TyCoercionVar param; ty = cons },
    add_ty_inequality (param, cons) cnstrs )

let fresh_dirt_coer cnstrs cons =
  let param = Type.DirtCoercionParam.fresh () in
  ( { term = DirtCoercion.DirtCoercionVar param; ty = cons },
    add_dirt_inequality (param, cons) cnstrs )

let fresh_dirty_coer cnstrs ((ty1, drt1), (ty2, drt2)) =
  let ty_coer, cnstrs' = fresh_ty_coer cnstrs (ty1, ty2) in
  let drt_coer, cnstrs'' = fresh_dirt_coer cnstrs' (drt1, drt2) in
  (TyCoercion.bangCoercion (ty_coer, drt_coer), cnstrs'')
