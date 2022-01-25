open Utils
open Language

(* A bag/list of constraints *)
type t = {
  skeleton_equalities : (Skeleton.t * Skeleton.t) list;
  dirt_equalities : (Dirt.t * Dirt.t) list;
  dirt_inequalities : (Type.DirtCoercionParam.t * Type.ct_dirt) list;
  ty_equalities : (Type.ty * Type.ty) list;
  ty_inequalities : (Type.TyCoercionParam.t * Type.ct_ty) list;
}

let empty =
  {
    skeleton_equalities = [];
    dirt_equalities = [];
    dirt_inequalities = [];
    ty_equalities = [];
    ty_inequalities = [];
  }

let add_skeleton_equality con cons =
  { cons with skeleton_equalities = con :: cons.skeleton_equalities }

let add_dirt_equality con cons =
  { cons with dirt_equalities = con :: cons.dirt_equalities }

let add_dirt_inequality con cons =
  { cons with dirt_inequalities = con :: cons.dirt_inequalities }

let add_ty_equality con cons =
  { cons with ty_equalities = con :: cons.ty_equalities }

let add_ty_inequality con cons =
  { cons with ty_inequalities = con :: cons.ty_inequalities }

let union cons1 cons2 =
  {
    skeleton_equalities = cons1.skeleton_equalities @ cons2.skeleton_equalities;
    dirt_equalities = cons1.dirt_equalities @ cons2.dirt_equalities;
    dirt_inequalities = cons1.dirt_inequalities @ cons2.dirt_inequalities;
    ty_equalities = cons1.ty_equalities @ cons2.ty_equalities;
    ty_inequalities = cons1.ty_inequalities @ cons2.ty_inequalities;
  }

let list_union conss = List.fold_left union empty conss

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

let apply_sub subs cons =
  {
    skeleton_equalities =
      List.map
        (fun (skel1, skel2) ->
          ( Substitution.apply_substitutions_to_skeleton subs skel1,
            Substitution.apply_substitutions_to_skeleton subs skel2 ))
        cons.skeleton_equalities;
    dirt_equalities =
      List.map
        (fun (drt1, drt2) ->
          ( Substitution.apply_substitutions_to_dirt subs drt1,
            Substitution.apply_substitutions_to_dirt subs drt2 ))
        cons.dirt_equalities;
    dirt_inequalities =
      List.map
        (fun (coer_p, (drt1, drt2)) ->
          ( coer_p,
            ( Substitution.apply_substitutions_to_dirt subs drt1,
              Substitution.apply_substitutions_to_dirt subs drt2 ) ))
        cons.dirt_inequalities;
    ty_equalities =
      List.map
        (fun (ty1, ty2) ->
          ( Substitution.apply_substitutions_to_type subs ty1,
            Substitution.apply_substitutions_to_type subs ty2 ))
        cons.ty_equalities;
    ty_inequalities =
      List.map
        (fun (coer_p, (ty1, ty2)) ->
          ( coer_p,
            ( Substitution.apply_substitutions_to_type subs ty1,
              Substitution.apply_substitutions_to_type subs ty2 ) ))
        cons.ty_inequalities;
  }

let return_to_unresolved (resolved : Constraints.t) queue =
  queue
  |> Constraints.DirtConstraints.fold_expanded
       (fun _ _ w _ drt1 drt2 -> add_dirt_inequality (w, (drt1, drt2)))
       resolved.dirt_constraints
  |> Constraints.TyConstraints.fold_expanded
       (fun _s _t1 _t2 w ty1 ty2 -> add_ty_inequality (w, (ty1, ty2)))
       resolved.ty_constraints

let unresolve resolved = return_to_unresolved resolved empty

let fresh_ty_coer cons =
  let param = Type.TyCoercionParam.fresh () in
  ( { term = Coercion.TyCoercionVar param; ty = cons },
    { empty with ty_inequalities = [ (param, cons) ] } )

let fresh_dirt_coer cons =
  let param = Type.DirtCoercionParam.fresh () in
  ( { term = Coercion.DirtCoercionVar param; ty = cons },
    { empty with dirt_inequalities = [ (param, cons) ] } )

let fresh_dirty_coer ((ty1, drt1), (ty2, drt2)) =
  let ty_coer, ty_cons = fresh_ty_coer (ty1, ty2)
  and drt_coer, drt_cons = fresh_dirt_coer (drt1, drt2) in
  (Coercion.bangCoercion (ty_coer, drt_coer), union ty_cons drt_cons)

(* ************************************************************************* *)
(*                        FREE PARAMETER COMPUTATION                         *)
(* ************************************************************************* *)

let cast_expression e ty =
  let omega, cons = fresh_ty_coer (e.ty, ty) in
  (Term.castExp (e, omega), cons)

let cast_computation c dirty =
  let omega, cnstrs = fresh_dirty_coer (c.ty, dirty) in
  (Term.castComp (c, omega), cnstrs)

let cast_abstraction { term = pat, cmp; _ } dirty =
  let cmp', cnstrs = cast_computation cmp dirty in
  (Term.abstraction (pat, cmp'), cnstrs)

let full_cast_abstraction { term = pat, cmp; _ } ty_in dirty_out =
  let x_pat, x_var = Term.fresh_variable "x" ty_in in
  let exp', cnstrs1 = cast_expression x_var pat.ty in
  let cmp', cnstrs2 = cast_computation cmp dirty_out in
  ( Term.abstraction (x_pat, Term.letVal (exp', Term.abstraction (pat, cmp'))),
    union cnstrs1 cnstrs2 )
