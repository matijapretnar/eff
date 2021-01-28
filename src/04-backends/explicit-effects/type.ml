open Utils
module Const = Language.Const
module CoreTypes = Language.CoreTypes
module LangType = Language.Type
module TypeContext = Typechecker.TypeDefinitionContext

(** dirt parameters *)
module DirtParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "drt"

  let utf8_symbol = "\206\180"
end))

(** skeleton parameters *)
module SkelParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "skl"

  let utf8_symbol = "s"
end))

(** type coercion parameters *)
module TyCoercionParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "tycoer"

  let utf8_symbol = "\207\132co"
end))

(** dirt coercion parameters *)
module DirtCoercionParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "dirtcoer"

  let utf8_symbol = "\206\180co"
end))

module EffectSet = Set.Make (CoreTypes.Effect)
module SkelParamSet = Set.Make (SkelParam)
module TyParamSet = Set.Make (CoreTypes.TyParam)
module DirtParamSet = Set.Make (DirtParam)

type effect_set = EffectSet.t

type skeleton =
  | SkelParam of SkelParam.t
  | SkelBasic of Const.ty
  | SkelArrow of skeleton * skeleton
  | SkelApply of CoreTypes.TyName.t * skeleton list
  | SkelHandler of skeleton * skeleton
  | SkelTuple of skeleton list

and ty =
  | TyParam of CoreTypes.TyParam.t * skeleton
  | Apply of CoreTypes.TyName.t * ty list
  | Arrow of abs_ty
  | Tuple of ty list
  | Handler of dirty * dirty
  | TyBasic of Const.ty
  | QualTy of ct_ty * ty
  | QualDirt of ct_dirt * ty

and dirty = ty * dirt

and dirt = { effect_set : effect_set; row : row }

and abs_ty = ty * dirty

and row = ParamRow of DirtParam.t | EmptyRow

and ct_ty = ty * ty

and ct_dirt = dirt * dirt

and ct_dirty = dirty * dirty

let type_const c = TyBasic (Const.infer_ty c)

let is_empty_dirt dirt =
  EffectSet.is_empty dirt.effect_set && dirt.row = EmptyRow

let rec skeleton_of_ty tty =
  match tty with
  | TyParam (_, skel) -> skel
  | Arrow (ty1, drty2) -> SkelArrow (skeleton_of_ty ty1, skeleton_of_dirty drty2)
  | Apply (ty_name, tys) ->
      SkelApply (ty_name, List.map (fun ty -> skeleton_of_ty ty) tys)
  | Tuple tup -> SkelTuple (List.map (fun ty -> skeleton_of_ty ty) tup)
  | Handler (drty1, drty2) ->
      SkelHandler (skeleton_of_dirty drty1, skeleton_of_dirty drty2)
  | TyBasic pt -> SkelBasic pt
  | QualTy (_, ty) -> skeleton_of_ty ty
  | QualDirt (_, ty) -> skeleton_of_ty ty

and skeleton_of_dirty (ty, _) = skeleton_of_ty ty

let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | TyParam (p, _) -> CoreTypes.TyParam.print p ppf
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:5 "@[%t -%t%s@ %t@]" (print_ty ~max_level:4 t1)
        (print_dirt drt) (Symbols.short_arrow ()) (print_ty ~max_level:5 t2)
  | Apply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | Apply (t, [ s ]) ->
      print ~at_level:1 "%t %t" (print_ty ~max_level:1 s)
        (CoreTypes.TyName.print t)
  | Apply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty ts)
        (CoreTypes.TyName.print t)
  | Tuple [] -> print "unit"
  | Tuple tys ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_ty ~max_level:1) tys)
  | Handler ((t1, drt1), (t2, drt2)) ->
      print ~at_level:6 "%t ! %t %s@ %t ! %t" (print_ty ~max_level:4 t1)
        (print_dirt drt1) (Symbols.handler_arrow ()) (print_ty ~max_level:4 t2)
        (print_dirt drt2)
  | TyBasic p -> print "%t" (Const.print_ty p)
  | QualTy (c, tty) -> print "%t => %t" (print_ct_ty c) (print_ty tty)
  | QualDirt (c, tty) -> print "%t => %t" (print_ct_dirt c) (print_ty tty)

and print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sk with
  | SkelParam p -> SkelParam.print p ppf
  | SkelBasic s -> print "prim_skel %t" (Const.print_ty s)
  | SkelArrow (sk1, sk2) ->
      print "%t -sk-> %t" (print_skeleton sk1) (print_skeleton sk2)
  | SkelApply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | SkelApply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_skeleton ~max_level:1 s)
        (CoreTypes.TyName.print t)
  | SkelApply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_skeleton ts)
        (CoreTypes.TyName.print t)
  | SkelTuple [] -> print "unit"
  | SkelTuple sks ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_skeleton ~max_level:1) sks)
  | SkelHandler (sk1, sk2) ->
      print "%t =sk=> %t" (print_skeleton sk1) (print_skeleton sk2)

and print_dirt drt ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, EmptyRow -> print "{%t}" (print_effect_set effect_set)
  | effect_set, ParamRow p when EffectSet.is_empty effect_set ->
      print "%t" (DirtParam.print p)
  | effect_set, ParamRow p ->
      print "{%t} U %t" (print_effect_set effect_set) (DirtParam.print p)

and print_effect_set effect_set =
  Print.sequence "," CoreTypes.Effect.print (EffectSet.elements effect_set)

and print_dirty (t1, drt1) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ! %t" (print_ty t1) (print_dirt drt1)

and print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_ty ty1) (print_ty ty2)

and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_dirt ty1) (print_dirt ty2)

and print_abs_ty (ty1, drty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t -> %t" (print_ty ty1) (print_dirty drty2)

(* ************************************************************************* *)
(*                       PREDICATES ON ty                             *)
(* ************************************************************************* *)

(* Check if a target type is a monotype. That is, no universal quantification
 * and no qualified constraints, at the top-level or in nested positions. *)
let rec isMonoTy : ty -> bool = function
  | TyParam _ -> true
  | Apply (_, tys) -> List.for_all isMonoTy tys
  | Arrow (ty1, (ty2, _)) -> isMonoTy ty1 && isMonoTy ty2
  | Tuple tys -> List.for_all isMonoTy tys
  | Handler ((ty1, _), (ty2, _)) -> isMonoTy ty1 && isMonoTy ty2
  | TyBasic _ -> true
  | QualTy (_, _) -> false (* no qualification *)
  | QualDirt (_, _) -> false

(* no qualification *)

(* Check if a target type is a closed monotype. That is, no type variables, no
 * universal quantification and no qualified constraints, at the top-level or
 * in nested positions. *)
let rec isClosedMonoTy : ty -> bool = function
  | TyParam _ -> false
  | Apply (_, tys) -> List.for_all isClosedMonoTy tys
  | Arrow (vty, cty) -> isClosedMonoTy vty && isClosedDirtyTy cty
  | Tuple tys -> List.for_all isClosedMonoTy tys
  | Handler (cty1, cty2) -> isClosedDirtyTy cty1 && isClosedDirtyTy cty2
  | TyBasic _ -> true
  | QualTy (_, _) -> false (* no qualification *)
  | QualDirt (_, _) -> false

(* no qualification *)

(* Check if a dirt is closed. That is, no dirt variables in it. *)
and isClosedDirt (d : dirt) : bool =
  match d.row with EmptyRow -> true | ParamRow _ -> false

(* Check if a dirty type is closed. That is, if both the dirt and the value
 * type are closed. *)
and isClosedDirtyTy : dirty -> bool = function
  | ty, drt -> isClosedMonoTy ty && isClosedDirt drt

(* ************************************************************************* *)
(*                             VARIABLE RENAMING                             *)
(* ************************************************************************* *)
let rec rnSkelVarInSkel (oldS : SkelParam.t) (newS : SkelParam.t) :
    skeleton -> skeleton = function
  | SkelParam v -> if v = oldS then SkelParam newS else SkelParam v
  | SkelBasic ty -> SkelBasic ty
  | SkelArrow (s1, s2) ->
      SkelArrow (rnSkelVarInSkel oldS newS s1, rnSkelVarInSkel oldS newS s2)
  | SkelApply (tc, ss) -> SkelApply (tc, List.map (rnSkelVarInSkel oldS newS) ss)
  | SkelHandler (s1, s2) ->
      SkelHandler (rnSkelVarInSkel oldS newS s1, rnSkelVarInSkel oldS newS s2)
  | SkelTuple ss -> SkelTuple (List.map (rnSkelVarInSkel oldS newS) ss)

let rec rnSkelVarInValTy (oldS : SkelParam.t) (newS : SkelParam.t) : ty -> ty =
  function
  | TyParam (x, skel) -> TyParam (x, (rnSkelVarInSkel oldS newS) skel)
  | Apply (tc, tys) -> Apply (tc, List.map (rnSkelVarInValTy oldS newS) tys)
  | Arrow (tyA, tyB) ->
      Arrow (rnSkelVarInValTy oldS newS tyA, rnSkelVarInCmpTy oldS newS tyB)
  | Tuple tys -> Tuple (List.map (rnSkelVarInValTy oldS newS) tys)
  | Handler (tyA, tyB) ->
      Handler (rnSkelVarInCmpTy oldS newS tyA, rnSkelVarInCmpTy oldS newS tyB)
  | TyBasic ty -> TyBasic ty
  | QualTy (ct, ty) ->
      QualTy (rnSkelVarInTyCt oldS newS ct, rnSkelVarInValTy oldS newS ty)
  | QualDirt (ct, ty) -> QualDirt (ct, rnSkelVarInValTy oldS newS ty)

(* GEORGE: No skeletons in dirts! :) *)
and rnSkelVarInCmpTy (oldS : SkelParam.t) (newS : SkelParam.t) : dirty -> dirty
    = function
  | ty, drt -> (rnSkelVarInValTy oldS newS ty, drt)

(* GEORGE: No skeletons in dirts! :) *)
and rnSkelVarInTyCt (oldS : SkelParam.t) (newS : SkelParam.t) : ct_ty -> ct_ty =
  function
  | ty1, ty2 -> (rnSkelVarInValTy oldS newS ty1, rnSkelVarInValTy oldS newS ty2)

(* ************************************************************************* *)
(*                             VARIABLE RENAMING                             *)
(* ************************************************************************* *)
let rec rnTyVarInValTy (oldA : CoreTypes.TyParam.t) (newA : CoreTypes.TyParam.t)
    : ty -> ty = function
  | TyParam (a, skel) ->
      if a = oldA then TyParam (newA, skel) else TyParam (a, skel)
  | Apply (tc, tys) -> Apply (tc, List.map (rnTyVarInValTy oldA newA) tys)
  | Arrow (tyA, tyB) ->
      Arrow (rnTyVarInValTy oldA newA tyA, rnTyVarInCmpTy oldA newA tyB)
  | Tuple tys -> Tuple (List.map (rnTyVarInValTy oldA newA) tys)
  | Handler (tyA, tyB) ->
      Handler (rnTyVarInCmpTy oldA newA tyA, rnTyVarInCmpTy oldA newA tyB)
  | TyBasic ty -> TyBasic ty
  | QualTy (ct, ty) ->
      QualTy (rnTyVarInTyCt oldA newA ct, rnTyVarInValTy oldA newA ty)
  | QualDirt (ct, ty) -> QualDirt (ct, rnTyVarInValTy oldA newA ty)

(* GEORGE: No skeletonsin dirts! :) *)
and rnTyVarInCmpTy (oldA : CoreTypes.TyParam.t) (newA : CoreTypes.TyParam.t) :
    dirty -> dirty = function
  | ty, drt -> (rnTyVarInValTy oldA newA ty, drt)

(* GEORGE: No skeletons in dirts! :) *)
and rnTyVarInTyCt (oldA : CoreTypes.TyParam.t) (newA : CoreTypes.TyParam.t) :
    ct_ty -> ct_ty = function
  | ty1, ty2 -> (rnTyVarInValTy oldA newA ty1, rnTyVarInValTy oldA newA ty2)

(* ************************************************************************* *)
(*                             VARIABLE RENAMING                             *)
(* ************************************************************************* *)
let rec rnDirtVarInValTy (oldD : DirtParam.t) (newD : DirtParam.t) : ty -> ty =
  function
  | TyParam (a, skel) -> TyParam (a, skel)
  | Apply (tc, tys) -> Apply (tc, List.map (rnDirtVarInValTy oldD newD) tys)
  | Arrow (tyA, tyB) ->
      Arrow (rnDirtVarInValTy oldD newD tyA, rnDirtVarInCmpTy oldD newD tyB)
  | Tuple tys -> Tuple (List.map (rnDirtVarInValTy oldD newD) tys)
  | Handler (tyA, tyB) ->
      Handler (rnDirtVarInCmpTy oldD newD tyA, rnDirtVarInCmpTy oldD newD tyB)
  | TyBasic ty -> TyBasic ty
  | QualTy (ct, ty) ->
      QualTy (rnDirtVarInTyCt oldD newD ct, rnDirtVarInValTy oldD newD ty)
  | QualDirt (ct, ty) ->
      QualDirt (rnDirtVarInDirtCt oldD newD ct, rnDirtVarInValTy oldD newD ty)

and rnDirtVarInCmpTy (oldD : DirtParam.t) (newD : DirtParam.t) : dirty -> dirty
    = function
  | ty, drt -> (rnDirtVarInValTy oldD newD ty, rnDirtVarInDirt oldD newD drt)

and rnDirtVarInDirt (oldD : DirtParam.t) (newD : DirtParam.t) : dirt -> dirt =
  function
  | { effect_set = eff; row = EmptyRow } -> { effect_set = eff; row = EmptyRow }
  | { effect_set = eff; row = ParamRow d } ->
      if d = oldD then { effect_set = eff; row = ParamRow newD }
      else { effect_set = eff; row = ParamRow d }

and rnDirtVarInTyCt (oldD : DirtParam.t) (newD : DirtParam.t) : ct_ty -> ct_ty =
  function
  | ty1, ty2 -> (rnDirtVarInValTy oldD newD ty1, rnDirtVarInValTy oldD newD ty2)

and rnDirtVarInDirtCt (oldD : DirtParam.t) (newD : DirtParam.t) :
    ct_dirt -> ct_dirt = function
  | d1, d2 -> (rnDirtVarInDirt oldD newD d1, rnDirtVarInDirt oldD newD d2)

(* ************************************************************************* *)

let rec types_are_equal type1 type2 =
  match (type1, type2) with
  | TyParam (tv1, _skel1), TyParam (tv2, _skel2) -> tv1 = tv2
  | Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1) ->
      types_are_equal ttya1 ttyb1 && dirty_types_are_equal dirtya1 dirtyb1
  | Tuple tys1, Tuple tys2 -> List.for_all2 types_are_equal tys1 tys2
  | Apply (ty_name1, tys1), Apply (ty_name2, tys2) ->
      ty_name1 = ty_name2 && List.for_all2 types_are_equal tys1 tys2
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      dirty_types_are_equal dirtya1 dirtyb1
      && dirty_types_are_equal dirtya2 dirtyb2
  | TyBasic ptya, TyBasic ptyb -> ptya = ptyb
  | QualTy (ctty1, ty1), QualTy (ctty2, ty2) ->
      ty_cts_are_equal ctty1 ctty2 && types_are_equal ty1 ty2
  | QualDirt (ctd1, ty1), QualDirt (ctd2, ty2) ->
      dirt_cts_are_equal ctd1 ctd2 && types_are_equal ty1 ty2
  | _ -> false

(*       Error.typing ~loc:Location.unknown "%t <> %t" (print_ty ty1)
        (print_ty ty2)
 *)
and dirty_types_are_equal (ty1, d1) (ty2, d2) =
  types_are_equal ty1 ty2 && dirts_are_equal d1 d2

and dirts_are_equal d1 d2 =
  EffectSet.equal d1.effect_set d2.effect_set && d1.row = d2.row

and ty_cts_are_equal (ty1, ty2) (ty3, ty4) =
  types_are_equal ty1 ty3 && types_are_equal ty2 ty4

and dirt_cts_are_equal (d1, d2) (d3, d4) =
  dirts_are_equal d1 d3 && dirts_are_equal d2 d4

let no_effect_dirt dirt_param =
  { effect_set = EffectSet.empty; row = ParamRow dirt_param }

let fresh_dirt () = no_effect_dirt (DirtParam.fresh ())

let closed_dirt effect_set = { effect_set; row = EmptyRow }

let empty_dirt = closed_dirt EffectSet.empty

let make_dirty ty = (ty, fresh_dirt ())

let add_effects effect_set drt =
  { drt with effect_set = EffectSet.union drt.effect_set effect_set }

let remove_effects effect_set drt =
  { drt with effect_set = EffectSet.diff drt.effect_set effect_set }

(* ************************************************************************* *)
(*                         FREE VARIABLE COMPUTATION                         *)
(* ************************************************************************* *)

module FreeParams = struct
  type t = { dirt_params : DirtParamSet.t; skel_params : SkelParamSet.t }

  let empty =
    { dirt_params = DirtParamSet.empty; skel_params = SkelParamSet.empty }

  let dirt_singleton p = { empty with dirt_params = DirtParamSet.singleton p }

  let skel_singleton p = { empty with skel_params = SkelParamSet.singleton p }

  let union fp1 fp2 =
    {
      dirt_params = DirtParamSet.union fp1.dirt_params fp2.dirt_params;
      skel_params = SkelParamSet.union fp1.skel_params fp2.skel_params;
    }

  let union_map free_params =
    List.fold_left (fun fp x -> union fp (free_params x)) empty

  let is_empty fp =
    DirtParamSet.is_empty fp.dirt_params && SkelParamSet.is_empty fp.skel_params
end

let rec free_params_skeleton = function
  | SkelParam p -> FreeParams.skel_singleton p
  | SkelBasic _ -> FreeParams.empty
  | SkelApply (_, sks) -> FreeParams.union_map free_params_skeleton sks
  | SkelArrow (sk1, sk2) ->
      FreeParams.union (free_params_skeleton sk1) (free_params_skeleton sk2)
  | SkelHandler (sk1, sk2) ->
      FreeParams.union (free_params_skeleton sk1) (free_params_skeleton sk2)
  | SkelTuple sks -> FreeParams.union_map free_params_skeleton sks

(* Compute the free variables of a target value type *)
let rec free_params_ty = function
  | TyParam (_p, skel) -> free_params_skeleton skel
  | Arrow (vty, cty) ->
      FreeParams.union (free_params_ty vty) (free_params_dirty cty)
  | Tuple vtys -> FreeParams.union_map free_params_ty vtys
  | Handler (cty1, cty2) ->
      FreeParams.union (free_params_dirty cty1) (free_params_dirty cty2)
  | TyBasic _prim_ty -> FreeParams.empty
  | Apply (_, vtys) -> FreeParams.union_map free_params_ty vtys
  | QualTy (ct, vty) ->
      FreeParams.union (free_params_ct_ty ct) (free_params_ty vty)
  | QualDirt (ct, vty) ->
      FreeParams.union (free_params_ct_dirt ct) (free_params_ty vty)

(* Compute the free dirt variables of a target computation type *)
and free_params_dirty (ty, dirt) =
  FreeParams.union (free_params_ty ty) (free_params_dirt dirt)

(* Compute the free dirt variables of a target computation type *)
and free_params_abstraction_ty (ty_in, drty_out) =
  FreeParams.union (free_params_ty ty_in) (free_params_dirty drty_out)

(* Compute the free dirt variables of a value type inequality *)
and free_params_ct_ty (vty1, vty2) =
  FreeParams.union (free_params_ty vty1) (free_params_ty vty2)

(* Compute the free dirt variables of a computation type inequality *)
and free_params_ct_dirty (cty1, cty2) =
  FreeParams.union (free_params_dirty cty1) (free_params_dirty cty2)

(* Compute the free dirt variables of a dirt inequality *)
and free_params_ct_dirt (dirt1, dirt2) =
  FreeParams.union (free_params_dirt dirt1) (free_params_dirt dirt2)

(* Compute the free dirt variables of a dirt *)
and free_params_dirt (dirt : dirt) =
  match dirt.row with
  | ParamRow p -> FreeParams.dirt_singleton p
  | EmptyRow -> FreeParams.empty

(* ************************************************************************* *)

let rec source_to_target tctx_st ty =
  let loc = Location.unknown in
  match ty with
  | LangType.Apply (ty_name, _args)
    when TypeContext.transparent ~loc ty_name tctx_st -> (
      match TypeContext.ty_apply ~loc ty_name [] tctx_st with
      (* We currently support only inlined types with no arguments *)
      | LangType.Inline ty -> source_to_target tctx_st ty
      (* Other cases should not be transparent *)
      | LangType.Record _ | LangType.Sum _ -> assert false)
  | LangType.Apply (ty_name, args) ->
      Apply (ty_name, List.map (source_to_target tctx_st) args)
  | LangType.TyParam p -> TyParam (p, SkelParam (SkelParam.fresh ()))
  | LangType.Basic s -> TyBasic s
  | LangType.Tuple l -> Tuple (List.map (source_to_target tctx_st) l)
  | LangType.Arrow (ty, dirty) ->
      Arrow ((source_to_target tctx_st) ty, source_to_dirty tctx_st dirty)
  | LangType.Handler { LangType.value = dirty1; finally = dirty2 } ->
      Handler (source_to_dirty tctx_st dirty1, source_to_dirty tctx_st dirty2)

and source_to_dirty tctx_st ty = (source_to_target tctx_st ty, empty_dirt)

let constructor_signature tctx_st lbl =
  match TypeContext.infer_variant lbl tctx_st with
  | None -> assert false
  | Some (ty_out, ty_in) ->
      let ty_in =
        match ty_in with Some ty_in -> ty_in | None -> LangType.Tuple []
      in
      (source_to_target tctx_st ty_in, source_to_target tctx_st ty_out)

let apply_sub_to_skel _ _ _skel = failwith __LOC__

let rec apply_sub_to_type ty_subs dirt_subs ty =
  match ty with
  | TyParam (p, skel) -> (
      match Assoc.lookup p ty_subs with
      | Some p' -> TyParam (p', apply_sub_to_skel ty_subs dirt_subs skel)
      | None -> ty)
  | Arrow (a, (b, d)) ->
      Arrow
        ( apply_sub_to_type ty_subs dirt_subs a,
          (apply_sub_to_type ty_subs dirt_subs b, apply_sub_to_dirt dirt_subs d)
        )
  | Tuple ty_list ->
      Tuple (List.map (fun x -> apply_sub_to_type ty_subs dirt_subs x) ty_list)
  | Handler ((a, b), (c, d)) ->
      Handler
        ( (apply_sub_to_type ty_subs dirt_subs a, apply_sub_to_dirt dirt_subs b),
          (apply_sub_to_type ty_subs dirt_subs c, apply_sub_to_dirt dirt_subs d)
        )
  | TyBasic _ -> ty
  | Apply (ty_name, tys) ->
      Apply (ty_name, List.map (apply_sub_to_type ty_subs dirt_subs) tys)
  | _ -> failwith __LOC__

and apply_sub_to_dirt dirt_subs drt =
  match drt.row with
  | ParamRow p -> (
      match Assoc.lookup p dirt_subs with
      | Some p' -> { drt with row = ParamRow p' }
      | None -> drt)
  | EmptyRow -> drt
