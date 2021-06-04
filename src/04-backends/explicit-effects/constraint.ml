open Utils
module CoreTypes = Language.CoreTypes

let add_to_constraints con constraints = con :: constraints

let add_list_to_constraints new_constraints old_constraints =
  new_constraints @ old_constraints

type ty_coercion = (ty_coercion', Type.ct_ty) typed

and ty_coercion' =
  | ReflTy
  | ArrowCoercion of ty_coercion * dirty_coercion
  | HandlerCoercion of dirty_coercion * dirty_coercion
  | TyCoercionVar of Type.TyCoercionParam.t
  | ApplyCoercion of CoreTypes.TyName.t * ty_coercion list
  | TupleCoercion of ty_coercion list

and dirt_coercion = (dirt_coercion', Type.ct_dirt) typed

and dirt_coercion' =
  | ReflDirt
  | DirtCoercionVar of Type.DirtCoercionParam.t
  | Empty
  | UnionDirt of (Type.effect_set * dirt_coercion)

and dirty_coercion = (ty_coercion * dirt_coercion, Type.ct_dirty) typed

type omega_ct =
  | TyOmega of (Type.TyCoercionParam.t * Type.ct_ty)
  | DirtOmega of (Type.DirtCoercionParam.t * Type.ct_dirt)
  | SkelEq of Type.skeleton * Type.skeleton

let is_trivial_ty_coercion omega =
  let ty1, ty2 = omega.ty in
  Type.equal_ty ty1 ty2

let is_trivial_dirty_coercion omega =
  let drty1, drty2 = omega.ty in
  Type.equal_dirty drty1 drty2

let reflTy ty = { term = ReflTy; ty = (ty, ty) }

let tyCoercionVar omega ct = { term = TyCoercionVar omega; ty = ct }

let dirtCoercionVar omega cd = { term = DirtCoercionVar omega; ty = cd }

let arrowCoercion (tcoer1, dtcoer2) =
  let ty1, ty1' = tcoer1.ty and drty2, drty2' = dtcoer2.ty in
  {
    term = ArrowCoercion (tcoer1, dtcoer2);
    ty = (Type.Arrow (ty1', drty2), Type.Arrow (ty1, drty2'));
  }

let tupleCoercion tcoers =
  let tys, tys' = tcoers |> List.map (fun tcoer -> tcoer.ty) |> List.split in
  { term = TupleCoercion tcoers; ty = (Type.Tuple tys, Type.Tuple tys') }

let applyCoercion (tyname, tcoers) =
  let tys, tys' = tcoers |> List.map (fun tcoer -> tcoer.ty) |> List.split in
  {
    term = ApplyCoercion (tyname, tcoers);
    ty = (Type.Apply (tyname, tys), Type.Apply (tyname, tys'));
  }

let handlerCoercion (dtcoer1, dtcoer2) =
  let drty1, drty1' = dtcoer1.ty and drty2, drty2' = dtcoer2.ty in
  {
    term = HandlerCoercion (dtcoer1, dtcoer2);
    ty = (Type.Handler (drty1', drty2), Type.Handler (drty1, drty2'));
  }

let bangCoercion ((ty_coer : ty_coercion), (drt_coer : dirt_coercion)) =
  let ty, ty' = ty_coer.ty and drt, drt' = drt_coer.ty in
  { term = (ty_coer, drt_coer); ty = ((ty, drt), (ty', drt')) }

let reflDirt drt = { term = ReflDirt; ty = (drt, drt) }

let reflDirty (ty, drt) = bangCoercion (reflTy ty, reflDirt drt)

let empty drt = { term = Empty; ty = (Type.empty_dirt, drt) }

let unionDirt (effs, dcoer) =
  let drt, drt' = dcoer.ty in
  {
    term = UnionDirt (effs, dcoer);
    ty = (Type.add_effects effs drt, Type.add_effects effs drt');
  }

type resolved = {
  ty_constraints :
    (Type.TyCoercionParam.t
    * CoreTypes.TyParam.t
    * CoreTypes.TyParam.t
    * Type.SkelParam.t)
    list;
  dirt_constraints : (Type.DirtCoercionParam.t * Type.ct_dirt) list;
}

let unresolve resolved =
  List.map
    (fun (omega, a, b, skel) ->
      TyOmega
        ( omega,
          ( Type.TyParam (a, Type.SkelParam skel),
            Type.TyParam (b, Type.SkelParam skel) ) ))
    resolved.ty_constraints
  @ List.map
      (fun (omega, ct) -> DirtOmega (omega, ct))
      resolved.dirt_constraints

let return_resolved resolved queue = unresolve resolved @ queue

let empty_resolved = { ty_constraints = []; dirt_constraints = [] }

let resolve_ty_constraint resolved omega ty1 ty2 skel =
  {
    resolved with
    ty_constraints = (omega, ty1, ty2, skel) :: resolved.ty_constraints;
  }

let resolve_dirt_constraint resolved omega ct =
  { resolved with dirt_constraints = (omega, ct) :: resolved.dirt_constraints }

(* ************************************************************************* *)
(*                         COERCION VARIABLES OF                             *)
(* ************************************************************************* *)

module TyCoercionParamSet = Set.Make (Type.TyCoercionParam)
module DirtCoercionParamSet = Set.Make (Type.DirtCoercionParam)

let rec print_ty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | ReflTy -> print "⟨%t⟩" (Type.print_ty (fst c.ty))
  | ArrowCoercion (tc1, { term = tc2, dc2; _ }) ->
      print ~at_level:3 "%t -{%t}→ %t"
        (print_ty_coercion ~max_level:2 tc1)
        (print_dirt_coercion dc2)
        (print_ty_coercion ~max_level:3 tc2)
  | HandlerCoercion (dc1, dc2) ->
      print "%t ⇛ %t"
        (print_dirty_coercion ~max_level:2 dc1)
        (print_dirty_coercion ~max_level:2 dc2)
  | TyCoercionVar tcp -> print "%t" (Type.TyCoercionParam.print tcp)
  | ApplyCoercion (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | ApplyCoercion (t, [ c ]) ->
      print ~at_level:1 "%t %t"
        (print_ty_coercion ~max_level:1 c)
        (CoreTypes.TyName.print t)
  | ApplyCoercion (t, cs) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty_coercion cs)
        (CoreTypes.TyName.print t)
  | TupleCoercion [] -> print "𝟙"
  | TupleCoercion cos ->
      print ~at_level:2 "%t"
        (Print.sequence "×" (print_ty_coercion ~max_level:1) cos)

and print_dirty_coercion ?max_level { term = tc, dirtc; _ } ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print ~at_level:2 "%t!%t"
    (print_ty_coercion ~max_level:0 tc)
    (print_dirt_coercion ~max_level:0 dirtc)

and print_dirt_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | ReflDirt -> print "⟨%t⟩" (Type.print_dirt (fst c.ty))
  | DirtCoercionVar tcp -> print "%t" (Type.DirtCoercionParam.print tcp)
  | Empty ->
      print ~at_level:1 "∅↪︎%t" (Type.print_dirt ~max_level:0 (snd c.ty))
  | UnionDirt (eset, dc) ->
      print ~at_level:2 "{%t}∪%t"
        (Type.print_effect_set eset)
        (print_dirt_coercion ~max_level:2 dc)

and print_omega_ct ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | TyOmega (p, (ty1, ty2)) ->
      print "%t: (%t ≤ %t)"
        (Type.TyCoercionParam.print p)
        (Type.print_ty ty1) (Type.print_ty ty2)
  | DirtOmega (p, (ty1, ty2)) ->
      print "%t: (%t ≤ %t)"
        (Type.DirtCoercionParam.print p)
        (Type.print_dirt ty1) (Type.print_dirt ty2)
  | SkelEq (sk1, sk2) ->
      print "%t ~ %t" (Type.print_skeleton sk1) (Type.print_skeleton sk2)

let print_constraints cs = Print.sequence ";" print_omega_ct cs

let fresh_skel () =
  let skel_var = Type.SkelParam.fresh () in
  Type.SkelParam skel_var

let fresh_ty_with_skel skel =
  let ty_var = CoreTypes.TyParam.fresh () in
  Type.TyParam (ty_var, skel)

let fresh_dirty_with_skel skel =
  let ty = fresh_ty_with_skel skel in
  Type.make_dirty ty

let fresh_ty_with_fresh_skel () = fresh_ty_with_skel (fresh_skel ())

let fresh_dirty_with_fresh_skel () = fresh_dirty_with_skel (fresh_skel ())

let fresh_ty_coer cons =
  let param = Type.TyCoercionParam.fresh () in
  ({ term = TyCoercionVar param; ty = cons }, TyOmega (param, cons))

let fresh_dirt_coer cons =
  let param = Type.DirtCoercionParam.fresh () in
  ({ term = DirtCoercionVar param; ty = cons }, DirtOmega (param, cons))

let fresh_dirty_coer ((ty1, drt1), (ty2, drt2)) =
  let ty_coer, ty_cons = fresh_ty_coer (ty1, ty2)
  and drt_coer, drt_cons = fresh_dirt_coer (drt1, drt2) in
  (bangCoercion (ty_coer, drt_coer), [ ty_cons; drt_cons ])

(* ************************************************************************* *)
(*                        FREE PARAMETER COMPUTATION                         *)
(* ************************************************************************* *)

let free_params_constraint = function
  | TyOmega (_, ct) -> Type.free_params_ct_ty ct
  | DirtOmega (_, ct) -> Type.free_params_ct_dirt ct
  | SkelEq (sk1, sk2) ->
      Type.FreeParams.union
        (Type.free_params_skeleton sk1)
        (Type.free_params_skeleton sk2)

let free_params_constraints = Type.FreeParams.union_map free_params_constraint

let free_params_resolved (res : resolved) =
  let free_params_ty =
    Type.FreeParams.union_map
      (fun (_, ty1, ty2, skel) ->
        Type.FreeParams.union
          {
            Type.FreeParams.empty with
            ty_params = Type.TyParamSet.of_list [ ty1; ty2 ];
          }
          (Type.FreeParams.skel_singleton skel))
      res.ty_constraints
  and free_params_dirt =
    Type.FreeParams.union_map
      (fun (_, dt) -> Type.free_params_ct_dirt dt)
      res.dirt_constraints
  in
  Type.FreeParams.union free_params_ty free_params_dirt

(* ************************************************************************* *)

(* free variables in target terms *)

let rec free_params_ty_coercion coer =
  Type.FreeParams.union
    (free_params_ty_coercion' coer.term)
    (Type.free_params_ct_ty coer.ty)

and free_params_ty_coercion' = function
  | ReflTy -> Type.FreeParams.empty
  | ArrowCoercion (tc, dc) ->
      Type.FreeParams.union
        (free_params_ty_coercion tc)
        (free_params_dirty_coercion dc)
  | HandlerCoercion (dc1, dc2) ->
      Type.FreeParams.union
        (free_params_dirty_coercion dc1)
        (free_params_dirty_coercion dc2)
  | TyCoercionVar _tcp -> Type.FreeParams.empty
  | TupleCoercion tcs ->
      List.fold_left
        (fun free tc -> Type.FreeParams.union free (free_params_ty_coercion tc))
        Type.FreeParams.empty tcs
  | ApplyCoercion (_ty_name, tcs) ->
      List.fold_left
        (fun free tc -> Type.FreeParams.union free (free_params_ty_coercion tc))
        Type.FreeParams.empty tcs

and free_params_dirt_coercion coer = Type.free_params_ct_dirt coer.ty

and free_params_dirty_coercion { term = tc, dc; _ } =
  Type.FreeParams.union
    (free_params_ty_coercion tc)
    (free_params_dirt_coercion dc)
