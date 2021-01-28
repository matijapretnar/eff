open Utils
module CoreTypes = Language.CoreTypes

let add_to_constraints con constraints = con :: constraints

let add_list_to_constraints new_constraints old_constraints =
  new_constraints @ old_constraints

type ty_coercion = (ty_coercion', Type.ct_ty) typed

and ty_coercion' =
  | ReflTy of Type.ty
  | ArrowCoercion of ty_coercion * dirty_coercion
  | HandlerCoercion of dirty_coercion * dirty_coercion
  | TyCoercionVar of Type.TyCoercionParam.t
  | ApplyCoercion of CoreTypes.TyName.t * ty_coercion list
  | TupleCoercion of ty_coercion list
  | QualTyCoer of Type.ct_ty * ty_coercion
  | QualDirtCoer of Type.ct_dirt * ty_coercion

and dirt_coercion = (dirt_coercion', Type.ct_dirt) typed

and dirt_coercion' =
  | ReflDirt of Type.dirt
  | DirtCoercionVar of Type.DirtCoercionParam.t
  | Empty of Type.dirt
  | UnionDirt of (Type.effect_set * dirt_coercion)

and dirty_coercion = (ty_coercion * dirt_coercion, Type.ct_dirty) typed

type omega_ct =
  | TyOmega of (Type.TyCoercionParam.t * Type.ct_ty)
  | DirtOmega of (Type.DirtCoercionParam.t * Type.ct_dirt)
  | SkelEq of Type.skeleton * Type.skeleton
  | TyParamHasSkel of (CoreTypes.TyParam.t * Type.skeleton)

let is_trivial_ty_coercion omega =
  let ty1, ty2 = omega.ty in
  Type.types_are_equal ty1 ty2

let is_trivial_dirty_coercion omega =
  let drty1, drty2 = omega.ty in
  Type.dirty_types_are_equal drty1 drty2

let reflTy ty = { term = ReflTy ty; ty = (ty, ty) }

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

let applyCoercion (_tyname, _tcoers) = failwith __LOC__

let handlerCoercion (dtcoer1, dtcoer2) =
  let drty1, drty1' = dtcoer1.ty and drty2, drty2' = dtcoer2.ty in
  {
    term = HandlerCoercion (dtcoer1, dtcoer2);
    ty = (Type.Handler (drty1', drty2), Type.Handler (drty1, drty2'));
  }

let bangCoercion ((ty_coer : ty_coercion), (drt_coer : dirt_coercion)) =
  let ty, ty' = ty_coer.ty and drt, drt' = drt_coer.ty in
  { term = (ty_coer, drt_coer); ty = ((ty, drt), (ty', drt')) }

let reflDirt drt = { term = ReflDirt drt; ty = (drt, drt) }

let reflDirty (ty, drt) = bangCoercion (reflTy ty, reflDirt drt)

let empty drt = { term = Empty drt; ty = (Type.empty_dirt, drt) }

let unionDirt (effs, dcoer) =
  let drt, drt' = dcoer.ty in
  {
    term = UnionDirt (effs, dcoer);
    ty = (Type.add_effects effs drt, Type.add_effects effs drt');
  }

(* ************************************************************************* *)
(*                         COERCION VARIABLES OF                             *)
(* ************************************************************************* *)

module TyCoercionParamSet = Set.Make (Type.TyCoercionParam)
module DirtCoercionParamSet = Set.Make (Type.DirtCoercionParam)

let rec print_ty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | ReflTy p -> print "<%t>" (Type.print_ty p)
  | ArrowCoercion (tc, dc) ->
      print "%t -> %t" (print_ty_coercion tc) (print_dirty_coercion dc)
  | HandlerCoercion (dc1, dc2) ->
      print "%t ==> %t" (print_dirty_coercion dc1) (print_dirty_coercion dc2)
  | TyCoercionVar tcp -> print "%t " (Type.TyCoercionParam.print tcp)
  | ApplyCoercion (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | ApplyCoercion (t, [ c ]) ->
      print ~at_level:1 "%t %t"
        (print_ty_coercion ~max_level:1 c)
        (CoreTypes.TyName.print t)
  | ApplyCoercion (t, cs) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty_coercion cs)
        (CoreTypes.TyName.print t)
  | TupleCoercion [] -> print "unit"
  | TupleCoercion cos ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_ty_coercion ~max_level:1) cos)
  | _ -> failwith "Not yet implemented __LOC__"

(* THE FOLLOWING ARE UNEXPECTED. SOMETHING MUST BE WRONG TO GET THEM.
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  | ForallTy of CoreTypes.TyParam.t * ty_coercion
  | ApplyTyCoer of ty_coercion * ty

  | ForallDirt of Type.DirtParam.t * ty_coercion
  | ApplyDirCoer of ty_coercion * dirt

  | QualTyCoer of ct_ty * ty_coercion
  | ApplyQualTyCoer of ty_coercion * ty_coercion

  | QualDirtCoer of ct_dirt * ty_coercion
  | ApplyQualDirtCoer of ty_coercion * dirt_coercion

  | ForallSkel of Type.SkelParam.t * ty_coercion
  | ApplySkelCoer of ty_coercion * skeleton
*)
and print_dirty_coercion ?max_level { term = tc, dirtc; _ } ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print "%t ! %t" (print_ty_coercion tc) (print_dirt_coercion dirtc)

and print_dirt_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | ReflDirt p -> print "<%t>" (Type.print_dirt p)
  | DirtCoercionVar tcp -> print "%t" (Type.DirtCoercionParam.print tcp)
  | Empty d -> print "Empty__(%t)" (Type.print_dirt d)
  | UnionDirt (eset, dc) ->
      print "{%t} U %t" (Type.print_effect_set eset) (print_dirt_coercion dc)

and print_omega_ct ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | TyOmega (p, (ty1, ty2)) ->
      print "%t: (%t =< %t)"
        (Type.TyCoercionParam.print p)
        (Type.print_ty ty1) (Type.print_ty ty2)
  | DirtOmega (p, (ty1, ty2)) ->
      print "%t: (%t =< %t)"
        (Type.DirtCoercionParam.print p)
        (Type.print_dirt ty1) (Type.print_dirt ty2)
  | SkelEq (sk1, sk2) ->
      print "%t ~ %t" (Type.print_skeleton sk1) (Type.print_skeleton sk2)
  | TyParamHasSkel (tp, sk1) ->
      print "%t : %t" (CoreTypes.TyParam.print tp) (Type.print_skeleton sk1)

let print_constraints cs = Print.sequence ";" print_omega_ct cs

let fresh_ty_with_skel skel =
  let ty_var = CoreTypes.TyParam.fresh () in
  (Type.TyParam (ty_var, skel), TyParamHasSkel (ty_var, skel))

let fresh_dirty_with_skel skel =
  let ty, cons = fresh_ty_with_skel skel and drt = Type.fresh_dirt () in
  ((ty, drt), cons)

let fresh_ty_with_fresh_skel () =
  let skel_var = Type.SkelParam.fresh () in
  fresh_ty_with_skel (Type.SkelParam skel_var)

let fresh_dirty_with_fresh_skel () =
  let skel_var = Type.SkelParam.fresh () in
  fresh_dirty_with_skel (Type.SkelParam skel_var)

let fresh_ty_coer cons =
  let param = Type.TyCoercionParam.fresh () in
  ({ term = TyCoercionVar param; ty = cons }, TyOmega (param, cons))

let fresh_dirt_coer cons =
  let param = Type.DirtCoercionParam.fresh () in
  ({ term = DirtCoercionVar param; ty = cons }, DirtOmega (param, cons))

let fresh_dirty_coer ((ty1, drt1), (ty2, drt2)) =
  let ty_coer, ty_cons = fresh_ty_coer (ty1, ty2)
  and drt_coer, drt_cons = fresh_dirt_coer (drt1, drt2) in
  (bangCoercion (ty_coer, drt_coer), ty_cons, drt_cons)

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
  | TyParamHasSkel (_t, sk) -> Type.free_params_skeleton sk

let free_params_constraints = Type.FreeParams.union_map free_params_constraint

(* ************************************************************************* *)

(* free variables in target terms *)

let rec free_params_ty_coercion coer =
  match coer.term with
  | ReflTy ty -> Type.free_params_ty ty
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
  | QualTyCoer (_ctty, tc) -> free_params_ty_coercion tc
  | QualDirtCoer (_ctd, tc) -> free_params_ty_coercion tc
  | ApplyCoercion (_ty_name, tcs) ->
      List.fold_left
        (fun free tc -> Type.FreeParams.union free (free_params_ty_coercion tc))
        Type.FreeParams.empty tcs

and free_params_dirt_coercion coer =
  match coer.term with
  | ReflDirt d -> Type.free_params_dirt d
  | DirtCoercionVar _dcv -> Type.FreeParams.empty
  | Empty d -> Type.free_params_dirt d
  | UnionDirt (_, dc) -> free_params_dirt_coercion dc

and free_params_dirty_coercion { term = tc, dc; _ } =
  Type.FreeParams.union
    (free_params_ty_coercion tc)
    (free_params_dirt_coercion dc)

let rec get_skel_vars_from_constraints = function
  | [] -> []
  | TyParamHasSkel (_, Type.SkelParam sv) :: xs ->
      sv :: get_skel_vars_from_constraints xs
  | _ :: xs -> get_skel_vars_from_constraints xs

(* Get all constraints of the form (alpha : skelvar) from a bag of constraints *)
(* (CoreTypes.TyParam.t, Type.SkelParam.t) *)
let rec getSkelVarAnnotationsFromCs = function
  | [] -> []
  | TyParamHasSkel (alpha, Type.SkelParam sv) :: cs ->
      (alpha, sv) :: getSkelVarAnnotationsFromCs cs
  | _ :: cs -> getSkelVarAnnotationsFromCs cs

(* Get all constraints of the form (alpha : skeleton) from a bag of constraints *)
(* (CoreTypes.TyParam.t, skeleton) *)
let rec getSkelAnnotationsFromCs = function
  | [] -> []
  | TyParamHasSkel (alpha, skeleton) :: cs ->
      (alpha, skeleton) :: getSkelAnnotationsFromCs cs
  | _ :: cs -> getSkelAnnotationsFromCs cs
