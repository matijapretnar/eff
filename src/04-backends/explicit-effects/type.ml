open Utils
module Const = Language.Const
module CoreTypes = Language.CoreTypes
module LangType = Language.Type
module TypeContext = Typechecker.TypeDefinitionContext

(** dirt parameters *)
module DirtParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "drt"

  let utf8_symbol = "δ"
end))

(** skeleton parameters *)
module SkelParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "skl"

  let utf8_symbol = "ς"
end))

(** type coercion parameters *)
module TyCoercionParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "tycoer"

  let utf8_symbol = "ω"
end))

(** dirt coercion parameters *)
module DirtCoercionParam = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "dirtcoer"

  let utf8_symbol = "ϖ"
end))

module EffectSet = Set.Make (CoreTypes.Effect)
module SkelParamSet = Set.Make (SkelParam)
module TyParamSet = Set.Make (CoreTypes.TyParam)
module TyParamMap = Map.Make (CoreTypes.TyParam)
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

and skeleton_of_dirty (ty, _) = skeleton_of_ty ty

let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | TyParam (p, skel) ->
      print ~at_level:4 "%t:%t"
        (CoreTypes.TyParam.print p)
        (print_skeleton skel)
  | Arrow (t1, (t2, drt)) when is_empty_dirt drt ->
      print ~at_level:3 "%t → %t" (print_ty ~max_level:2 t1)
        (print_ty ~max_level:3 t2)
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:3 "%t -%t→ %t" (print_ty ~max_level:2 t1)
        (print_dirt drt) (print_ty ~max_level:3 t2)
  | Apply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | Apply (t, [ s ]) ->
      print ~at_level:1 "%t %t" (print_ty ~max_level:1 s)
        (CoreTypes.TyName.print t)
  | Apply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty ts)
        (CoreTypes.TyName.print t)
  | Tuple [] -> print "𝟙"
  | Tuple tys ->
      print ~at_level:2 "%t" (Print.sequence "×" (print_ty ~max_level:1) tys)
  | Handler (drty1, drty2) ->
      print ~at_level:3 "%t ⇛ %t"
        (print_dirty ~max_level:2 drty1)
        (print_dirty ~max_level:2 drty2)
  | TyBasic p -> print "%t" (Const.print_ty p)

and print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sk with
  | SkelParam p -> SkelParam.print p ppf
  | SkelBasic s -> print "%t" (Const.print_ty s)
  | SkelArrow (sk1, sk2) ->
      print "%t → %t" (print_skeleton sk1) (print_skeleton sk2)
  | SkelApply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | SkelApply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_skeleton ~max_level:1 s)
        (CoreTypes.TyName.print t)
  | SkelApply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_skeleton ts)
        (CoreTypes.TyName.print t)
  | SkelTuple [] -> print "𝟙"
  | SkelTuple sks ->
      print ~at_level:2 "%t"
        (Print.sequence "×" (print_skeleton ~max_level:1) sks)
  | SkelHandler (sk1, sk2) ->
      print "%t ⇛ %t" (print_skeleton sk1) (print_skeleton sk2)

and print_dirt ?max_level drt ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, EmptyRow -> print "{%t}" (print_effect_set effect_set)
  | effect_set, ParamRow p when EffectSet.is_empty effect_set ->
      print "%t" (DirtParam.print p)
  | effect_set, ParamRow p ->
      print ~at_level:1 "{%t}∪%t"
        (print_effect_set effect_set)
        (DirtParam.print p)

and print_effect_set effect_set =
  Print.sequence "," CoreTypes.Effect.print (EffectSet.elements effect_set)

and print_dirty ?max_level (t1, drt1) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print ~at_level:2 "%t!%t" (print_ty ~max_level:0 t1)
    (print_dirt ~max_level:0 drt1)

and print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ≤ %t" (print_ty ty1) (print_ty ty2)

and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ≤ %t" (print_dirt ty1) (print_dirt ty2)

and print_abs_ty (ty1, drty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t → %t" (print_ty ty1) (print_dirty drty2)

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

let rec equal_ty type1 type2 =
  match (type1, type2) with
  | TyParam (tv1, _skel1), TyParam (tv2, _skel2) -> tv1 = tv2
  | Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1) ->
      equal_ty ttya1 ttyb1 && equal_dirty dirtya1 dirtyb1
  | Tuple tys1, Tuple tys2 ->
      List.length tys1 = List.length tys2 && List.for_all2 equal_ty tys1 tys2
  | Apply (ty_name1, tys1), Apply (ty_name2, tys2) ->
      ty_name1 = ty_name2
      && List.length tys1 = List.length tys2
      && List.for_all2 equal_ty tys1 tys2
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      equal_dirty dirtya1 dirtyb1 && equal_dirty dirtya2 dirtyb2
  | TyBasic ptya, TyBasic ptyb -> ptya = ptyb
  | _ -> false

(*       Error.typing ~loc:Location.unknown "%t <> %t" (print_ty ty1)
        (print_ty ty2)
 *)
and equal_dirty (ty1, d1) (ty2, d2) = equal_ty ty1 ty2 && equal_dirt d1 d2

and equal_dirt d1 d2 =
  EffectSet.equal d1.effect_set d2.effect_set && d1.row = d2.row

and equal_ty_constraint (ty1, ty2) (ty3, ty4) =
  equal_ty ty1 ty3 && equal_ty ty2 ty4

and equal_dirt_constraint (d1, d2) (d3, d4) =
  equal_dirt d1 d3 && equal_dirt d2 d4

let no_effect_dirt dirt_param =
  { effect_set = EffectSet.empty; row = ParamRow dirt_param }

let fresh_dirt () = no_effect_dirt (DirtParam.fresh ())

let closed_dirt effect_set = { effect_set; row = EmptyRow }

let empty_dirt = closed_dirt EffectSet.empty

let make_dirty ty = (ty, fresh_dirt ())

let pure_ty ty = (ty, empty_dirt)

let add_effects effect_set drt =
  { drt with effect_set = EffectSet.union drt.effect_set effect_set }

(* ************************************************************************* *)
(*                         FREE VARIABLE COMPUTATION                         *)
(* ************************************************************************* *)

module FreeParams = struct
  type t = {
    ty_params : TyParamSet.t;
    dirt_params : DirtParamSet.t;
    skel_params : SkelParamSet.t;
  }

  let empty =
    {
      ty_params = TyParamSet.empty;
      dirt_params = DirtParamSet.empty;
      skel_params = SkelParamSet.empty;
    }

  let ty_singleton p = { empty with ty_params = TyParamSet.singleton p }

  let dirt_singleton p = { empty with dirt_params = DirtParamSet.singleton p }

  let skel_singleton p = { empty with skel_params = SkelParamSet.singleton p }

  let union fp1 fp2 =
    {
      ty_params = TyParamSet.union fp1.ty_params fp2.ty_params;
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
  | TyParam (p, skel) ->
      FreeParams.union (FreeParams.ty_singleton p) (free_params_skeleton skel)
  | Arrow (vty, cty) ->
      FreeParams.union (free_params_ty vty) (free_params_dirty cty)
  | Tuple vtys -> FreeParams.union_map free_params_ty vtys
  | Handler (cty1, cty2) ->
      FreeParams.union (free_params_dirty cty1) (free_params_dirty cty2)
  | TyBasic _prim_ty -> FreeParams.empty
  | Apply (_, vtys) -> FreeParams.union_map free_params_ty vtys

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
