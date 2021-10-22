open Utils

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
module SkelParamMap = Map.Make (SkelParam)
module TyParamSet = Set.Make (CoreTypes.TyParam)
module TyParamMap = Map.Make (CoreTypes.TyParam)
module DirtParamSet = Set.Make (DirtParam)
module DirtParamMap = Map.Make (DirtParam)
module TyCoercionParamMap = Map.Make (TyCoercionParam)
module DirtCoercionParamMap = Map.Make (DirtCoercionParam)

type effect_set = EffectSet.t

type skeleton =
  | SkelParam of SkelParam.t
  | SkelBasic of Const.ty
  | SkelArrow of skeleton * skeleton
  | SkelApply of CoreTypes.TyName.t * skeleton list
  | SkelHandler of skeleton * skeleton
  | SkelTuple of skeleton list

type ty = (ty', skeleton) typed

and ty' =
  | TyParam of CoreTypes.TyParam.t
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

let skeleton_of_ty ty = ty.ty

let skeleton_of_dirty (ty, _) = skeleton_of_ty ty

let tyParam t skel = { term = TyParam t; ty = skel }

let arrow (ty1, drty2) =
  {
    term = Arrow (ty1, drty2);
    ty = SkelArrow (skeleton_of_ty ty1, skeleton_of_dirty drty2);
  }

let apply (ty_name, tys) =
  {
    term = Apply (ty_name, tys);
    ty = SkelApply (ty_name, List.map (fun ty -> skeleton_of_ty ty) tys);
  }

let tuple tup =
  {
    term = Tuple tup;
    ty = SkelTuple (List.map (fun ty -> skeleton_of_ty ty) tup);
  }

let handler (drty1, drty2) =
  {
    term = Handler (drty1, drty2);
    ty = SkelHandler (skeleton_of_dirty drty1, skeleton_of_dirty drty2);
  }

let tyBasic pt = { term = TyBasic pt; ty = SkelBasic pt }

let unit_ty = tuple []

let empty_ty = apply (CoreTypes.empty_tyname, [])

let int_ty = tyBasic Const.IntegerTy

let float_ty = tyBasic Const.FloatTy

let bool_ty = tyBasic Const.BooleanTy

let string_ty = tyBasic Const.StringTy

and skeleton_of_dirty (ty, _) = skeleton_of_ty ty

type parameters = {
  skeleton_params : SkelParam.t list;
  dirt_params : DirtParam.t list;
  ty_params : (CoreTypes.TyParam.t * skeleton) list;
  ty_constraints : (TyCoercionParam.t * ct_ty) list;
  dirt_constraints : (DirtCoercionParam.t * ct_dirt) list;
}

let empty_parameters =
  {
    skeleton_params = [];
    dirt_params = [];
    ty_params = [];
    ty_constraints = [];
    dirt_constraints = [];
  }

type ty_scheme = { parameters : parameters; monotype : ty }

let monotype ty = { parameters = empty_parameters; monotype = ty }

let type_const c = tyBasic (Const.infer_ty c)

let is_empty_dirt dirt =
  EffectSet.is_empty dirt.effect_set && dirt.row = EmptyRow

let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty.term with
  | TyParam p ->
      print ~at_level:4 "%t:%t"
        (CoreTypes.TyParam.print p)
        (print_skeleton ty.ty)
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

let rec equal_ty type1 type2 =
  match (type1.term, type2.term) with
  | TyParam tv1, TyParam tv2 -> tv1 = tv2
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

and equal_dirty (ty1, d1) (ty2, d2) = equal_ty ty1 ty2 && equal_dirt d1 d2

and equal_dirt d1 d2 =
  EffectSet.equal d1.effect_set d2.effect_set && d1.row = d2.row

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
    ty_params : skeleton list TyParamMap.t;
    dirt_params : DirtParamSet.t;
    skel_params : SkelParamSet.t;
  }

  let empty =
    {
      ty_params = TyParamMap.empty;
      dirt_params = DirtParamSet.empty;
      skel_params = SkelParamSet.empty;
    }

  let subset fp1 fp2 =
    TyParamMap.for_all
      (fun p1 _ -> TyParamMap.mem p1 fp2.ty_params)
      fp1.ty_params
    && DirtParamSet.subset fp1.dirt_params fp2.dirt_params
    && SkelParamSet.subset fp1.skel_params fp2.skel_params

  let ty_singleton p skel =
    { empty with ty_params = TyParamMap.singleton p [ skel ] }

  let dirt_singleton p = { empty with dirt_params = DirtParamSet.singleton p }

  let skel_singleton p = { empty with skel_params = SkelParamSet.singleton p }

  let union fp1 fp2 =
    {
      ty_params =
        TyParamMap.union
          (fun _ skels1 skels2 -> Some (skels1 @ skels2))
          fp1.ty_params fp2.ty_params;
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

let rec free_params_ty ty =
  match ty.term with
  | TyParam p -> FreeParams.ty_singleton p ty.ty
  | Arrow (vty, cty) ->
      FreeParams.union (free_params_ty vty) (free_params_dirty cty)
  | Tuple vtys -> FreeParams.union_map free_params_ty vtys
  | Handler (cty1, cty2) ->
      FreeParams.union (free_params_dirty cty1) (free_params_dirty cty2)
  | TyBasic _prim_ty -> FreeParams.empty
  | Apply (_, vtys) -> FreeParams.union_map free_params_ty vtys

and free_params_dirty (ty, dirt) =
  FreeParams.union (free_params_ty ty) (free_params_dirt dirt)

and free_params_abstraction_ty (ty_in, drty_out) =
  FreeParams.union (free_params_ty ty_in) (free_params_dirty drty_out)

and free_params_ct_ty (vty1, vty2) =
  FreeParams.union (free_params_ty vty1) (free_params_ty vty2)

and free_params_ct_dirty (cty1, cty2) =
  FreeParams.union (free_params_dirty cty1) (free_params_dirty cty2)

and free_params_ct_dirt (dirt1, dirt2) =
  FreeParams.union (free_params_dirt dirt1) (free_params_dirt dirt2)

and free_params_dirt (dirt : dirt) =
  match dirt.row with
  | ParamRow p -> FreeParams.dirt_singleton p
  | EmptyRow -> FreeParams.empty

(* ************************************************************************* *)

module Renaming = struct
  type t = {
    ty_params : CoreTypes.TyParam.t TyParamMap.t;
    dirt_params : DirtParam.t DirtParamMap.t;
    skel_params : SkelParam.t SkelParamMap.t;
    ty_coercion_params : TyCoercionParam.t TyCoercionParamMap.t;
    dirt_coercion_params : DirtCoercionParam.t DirtCoercionParamMap.t;
  }

  let empty =
    {
      ty_params = TyParamMap.empty;
      dirt_params = DirtParamMap.empty;
      skel_params = SkelParamMap.empty;
      ty_coercion_params = TyCoercionParamMap.empty;
      dirt_coercion_params = DirtCoercionParamMap.empty;
    }
end

let parameters_renaming parameters : Renaming.t =
  {
    skel_params =
      parameters.skeleton_params
      |> List.map (fun p -> (p, SkelParam.refresh p))
      |> List.to_seq |> SkelParamMap.of_seq;
    ty_params =
      parameters.ty_params
      |> List.map (fun (p, _skel) -> (p, CoreTypes.TyParam.refresh p))
      |> List.to_seq |> TyParamMap.of_seq;
    dirt_params =
      parameters.dirt_params
      |> List.map (fun p -> (p, DirtParam.refresh p))
      |> List.to_seq |> DirtParamMap.of_seq;
    ty_coercion_params =
      parameters.ty_constraints
      |> List.map (fun (p, _) -> (p, TyCoercionParam.refresh p))
      |> List.to_seq |> TyCoercionParamMap.of_seq;
    dirt_coercion_params =
      parameters.dirt_constraints
      |> List.map (fun (p, _) -> (p, DirtCoercionParam.refresh p))
      |> List.to_seq |> DirtCoercionParamMap.of_seq;
  }

let rec rename_skeleton (sbst : Renaming.t) = function
  | SkelParam p ->
      SkelParam
        (SkelParamMap.find_opt p sbst.skel_params |> Option.value ~default:p)
  | SkelBasic _ as skel -> skel
  | SkelApply (ty_name, sks) ->
      SkelApply (ty_name, List.map (rename_skeleton sbst) sks)
  | SkelArrow (sk1, sk2) ->
      SkelArrow (rename_skeleton sbst sk1, rename_skeleton sbst sk2)
  | SkelHandler (sk1, sk2) ->
      SkelHandler (rename_skeleton sbst sk1, rename_skeleton sbst sk2)
  | SkelTuple sks -> SkelTuple (List.map (rename_skeleton sbst) sks)

let rec rename_ty (sbst : Renaming.t) ty =
  { term = rename_ty' sbst ty.term; ty = rename_skeleton sbst ty.ty }

and rename_ty' sbst = function
  | TyParam p ->
      TyParam (TyParamMap.find_opt p sbst.ty_params |> Option.value ~default:p)
  | Arrow (vty, cty) -> Arrow (rename_ty sbst vty, rename_dirty sbst cty)
  | Tuple vtys -> Tuple (List.map (rename_ty sbst) vtys)
  | Handler (cty1, cty2) ->
      Handler (rename_dirty sbst cty1, rename_dirty sbst cty2)
  | TyBasic _ as ty -> ty
  | Apply (ty_name, vtys) -> Apply (ty_name, List.map (rename_ty sbst) vtys)

and rename_dirty sbst (ty, dirt) = (rename_ty sbst ty, rename_dirt sbst dirt)

and rename_abstraction_ty sbst (ty_in, drty_out) =
  (rename_ty sbst ty_in, rename_dirty sbst drty_out)

and rename_ct_ty sbst (vty1, vty2) = (rename_ty sbst vty1, rename_ty sbst vty2)

and rename_ct_dirty sbst (cty1, cty2) =
  (rename_dirty sbst cty1, rename_dirty sbst cty2)

and rename_ct_dirt sbst (dirt1, dirt2) =
  (rename_dirt sbst dirt1, rename_dirt sbst dirt2)

and rename_dirt (sbst : Renaming.t) dirt =
  match dirt.row with
  | EmptyRow -> dirt
  | ParamRow p ->
      {
        dirt with
        row =
          ParamRow
            (DirtParamMap.find_opt p sbst.dirt_params |> Option.value ~default:p);
      }

let rename_parameters (sbst : Renaming.t) parameters =
  {
    skeleton_params =
      List.map
        (fun p ->
          SkelParamMap.find_opt p sbst.skel_params |> Option.value ~default:p)
        parameters.skeleton_params;
    ty_params =
      List.map
        (fun (p, skel) ->
          ( TyParamMap.find_opt p sbst.ty_params |> Option.value ~default:p,
            rename_skeleton sbst skel ))
        parameters.ty_params;
    dirt_params =
      List.map
        (fun p ->
          DirtParamMap.find_opt p sbst.dirt_params |> Option.value ~default:p)
        parameters.dirt_params;
    ty_constraints =
      List.map
        (fun (p, ct) ->
          ( TyCoercionParamMap.find_opt p sbst.ty_coercion_params
            |> Option.value ~default:p,
            rename_ct_ty sbst ct ))
        parameters.ty_constraints;
    dirt_constraints =
      List.map
        (fun (p, dt) ->
          ( DirtCoercionParamMap.find_opt p sbst.dirt_coercion_params
            |> Option.value ~default:p,
            rename_ct_dirt sbst dt ))
        parameters.dirt_constraints;
  }

let rename_ty_scheme sbst ty_scheme =
  {
    parameters = rename_parameters sbst ty_scheme.parameters;
    monotype = rename_ty sbst ty_scheme.monotype;
  }

let refresh_ty_scheme ty_scheme =
  let sbst = parameters_renaming ty_scheme.parameters in
  rename_ty_scheme sbst ty_scheme
