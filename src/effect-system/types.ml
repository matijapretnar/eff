module EffectSet = Set.Make (CoreTypes.Effect)
module SkelParamSet = Set.Make (CoreTypes.SkelParam)
module TyParamSet = Set.Make (CoreTypes.TyParam)
module DirtParamSet = Set.Make (CoreTypes.DirtParam)

type effect_set = EffectSet.t

type skeleton =
  | SkelParam of CoreTypes.SkelParam.t
  | SkelBasic of Const.ty
  | SkelArrow of skeleton * skeleton
  | SkelApply of CoreTypes.TyName.t * skeleton list
  | SkelHandler of skeleton * skeleton
  | SkelTuple of skeleton list

and target_ty =
  | TyParam of CoreTypes.TyParam.t
  | Apply of CoreTypes.TyName.t * target_ty list
  | Arrow of target_ty * target_dirty
  | Tuple of target_ty list
  | Handler of target_dirty * target_dirty
  | TyBasic of Const.ty
  | QualTy of ct_ty * target_ty
  | QualDirt of ct_dirt * target_ty

and target_dirty = target_ty * dirt

and dirt = { effect_set : effect_set; row : row }

and row = ParamRow of CoreTypes.DirtParam.t | EmptyRow

and ct_ty = target_ty * target_ty

and ct_dirt = dirt * dirt

and ct_dirty = target_dirty * target_dirty

let type_const c = TyBasic (Const.infer_ty c)

let is_empty_dirt dirt =
  EffectSet.is_empty dirt.effect_set && dirt.row = EmptyRow

let rec print_target_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | TyParam p -> CoreTypes.TyParam.print p ppf
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:5 "@[%t -%t%s@ %t@]"
        (print_target_ty ~max_level:4 t1)
        (print_target_dirt drt) (Symbols.short_arrow ())
        (print_target_ty ~max_level:5 t2)
  | Apply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | Apply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_target_ty ~max_level:1 s)
        (CoreTypes.TyName.print t)
  | Apply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_target_ty ts)
        (CoreTypes.TyName.print t)
  | Tuple [] -> print "unit"
  | Tuple tys ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_target_ty ~max_level:1) tys)
  | Handler ((t1, drt1), (t2, drt2)) ->
      print ~at_level:6 "%t ! %t %s@ %t ! %t"
        (print_target_ty ~max_level:4 t1)
        (print_target_dirt drt1) (Symbols.handler_arrow ())
        (print_target_ty ~max_level:4 t2)
        (print_target_dirt drt2)
  | TyBasic p -> print "%t" (Const.print_ty p)
  | QualTy (c, tty) -> print "%t => %t" (print_ct_ty c) (print_target_ty tty)
  | QualDirt (c, tty) ->
      print "%t => %t" (print_ct_dirt c) (print_target_ty tty)

and print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sk with
  | SkelParam p -> CoreTypes.SkelParam.print p ppf
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

and print_target_dirt drt ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, EmptyRow -> print "{%t}" (print_effect_set effect_set)
  | effect_set, ParamRow p when EffectSet.is_empty effect_set ->
      print "%t" (CoreTypes.DirtParam.print p)
  | effect_set, ParamRow p ->
      print "{%t} U %t"
        (print_effect_set effect_set)
        (CoreTypes.DirtParam.print p)

and print_effect_set effect_set =
  Print.sequence "," CoreTypes.Effect.print (EffectSet.elements effect_set)

and print_target_dirty (t1, drt1) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ! %t" (print_target_ty t1) (print_target_dirt drt1)

and print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_target_ty ty1) (print_target_ty ty2)

and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t <= %t" (print_target_dirt ty1) (print_target_dirt ty2)

(* ************************************************************************* *)
(*                       PREDICATES ON target_ty                             *)
(* ************************************************************************* *)

(* Check if a target type is a monotype. That is, no universal quantification
 * and no qualified constraints, at the top-level or in nested positions. *)
let rec isMonoTy : target_ty -> bool = function
  | TyParam _ -> true
  | Apply (tyCon, tys) -> List.for_all isMonoTy tys
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
let rec isClosedMonoTy : target_ty -> bool = function
  | TyParam _ -> false
  | Apply (tyCon, tys) -> List.for_all isClosedMonoTy tys
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
and isClosedDirtyTy : target_dirty -> bool = function
  | ty, drt -> isClosedMonoTy ty && isClosedDirt drt

(* ************************************************************************* *)
(*                             VARIABLE RENAMING                             *)
(* ************************************************************************* *)
let rec rnSkelVarInSkel (oldS : CoreTypes.SkelParam.t)
    (newS : CoreTypes.SkelParam.t) : skeleton -> skeleton = function
  | SkelParam v -> if v = oldS then SkelParam newS else SkelParam v
  | SkelBasic ty -> SkelBasic ty
  | SkelArrow (s1, s2) ->
      SkelArrow (rnSkelVarInSkel oldS newS s1, rnSkelVarInSkel oldS newS s2)
  | SkelApply (tc, ss) -> SkelApply (tc, List.map (rnSkelVarInSkel oldS newS) ss)
  | SkelHandler (s1, s2) ->
      SkelHandler (rnSkelVarInSkel oldS newS s1, rnSkelVarInSkel oldS newS s2)
  | SkelTuple ss -> SkelTuple (List.map (rnSkelVarInSkel oldS newS) ss)

let rec rnSkelVarInValTy (oldS : CoreTypes.SkelParam.t)
    (newS : CoreTypes.SkelParam.t) : target_ty -> target_ty = function
  | TyParam x -> TyParam x
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
and rnSkelVarInCmpTy (oldS : CoreTypes.SkelParam.t)
    (newS : CoreTypes.SkelParam.t) : target_dirty -> target_dirty = function
  | ty, drt -> (rnSkelVarInValTy oldS newS ty, drt)

(* GEORGE: No skeletons in dirts! :) *)
and rnSkelVarInTyCt (oldS : CoreTypes.SkelParam.t)
    (newS : CoreTypes.SkelParam.t) : ct_ty -> ct_ty = function
  | ty1, ty2 -> (rnSkelVarInValTy oldS newS ty1, rnSkelVarInValTy oldS newS ty2)

(* ************************************************************************* *)
(*                             VARIABLE RENAMING                             *)
(* ************************************************************************* *)
let rec rnTyVarInValTy (oldA : CoreTypes.TyParam.t) (newA : CoreTypes.TyParam.t)
    : target_ty -> target_ty = function
  | TyParam a -> if a = oldA then TyParam newA else TyParam a
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
    target_dirty -> target_dirty = function
  | ty, drt -> (rnTyVarInValTy oldA newA ty, drt)

(* GEORGE: No skeletons in dirts! :) *)
and rnTyVarInTyCt (oldA : CoreTypes.TyParam.t) (newA : CoreTypes.TyParam.t) :
    ct_ty -> ct_ty = function
  | ty1, ty2 -> (rnTyVarInValTy oldA newA ty1, rnTyVarInValTy oldA newA ty2)

(* ************************************************************************* *)
(*                             VARIABLE RENAMING                             *)
(* ************************************************************************* *)
let rec rnDirtVarInValTy (oldD : CoreTypes.DirtParam.t)
    (newD : CoreTypes.DirtParam.t) : target_ty -> target_ty = function
  | TyParam a -> TyParam a
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

and rnDirtVarInCmpTy (oldD : CoreTypes.DirtParam.t)
    (newD : CoreTypes.DirtParam.t) : target_dirty -> target_dirty = function
  | ty, drt -> (rnDirtVarInValTy oldD newD ty, rnDirtVarInDirt oldD newD drt)

and rnDirtVarInDirt (oldD : CoreTypes.DirtParam.t)
    (newD : CoreTypes.DirtParam.t) : dirt -> dirt = function
  | { effect_set = eff; row = EmptyRow } -> { effect_set = eff; row = EmptyRow }
  | { effect_set = eff; row = ParamRow d } ->
      if d = oldD then { effect_set = eff; row = ParamRow newD }
      else { effect_set = eff; row = ParamRow d }

and rnDirtVarInTyCt (oldD : CoreTypes.DirtParam.t)
    (newD : CoreTypes.DirtParam.t) : ct_ty -> ct_ty = function
  | ty1, ty2 -> (rnDirtVarInValTy oldD newD ty1, rnDirtVarInValTy oldD newD ty2)

and rnDirtVarInDirtCt (oldD : CoreTypes.DirtParam.t)
    (newD : CoreTypes.DirtParam.t) : ct_dirt -> ct_dirt = function
  | d1, d2 -> (rnDirtVarInDirt oldD newD d1, rnDirtVarInDirt oldD newD d2)

(* ************************************************************************* *)

let rec types_are_equal type1 type2 =
  match (type1, type2) with
  | TyParam tv1, TyParam tv2 -> tv1 = tv2
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

(*       Error.typing ~loc:Location.unknown "%t <> %t" (print_target_ty ty1)
        (print_target_ty ty2)
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

let fresh_dirt () = no_effect_dirt (CoreTypes.DirtParam.fresh ())

let closed_dirt effect_set = { effect_set; row = EmptyRow }

let empty_dirt = closed_dirt EffectSet.empty

let make_dirty ty = (ty, fresh_dirt ())

let add_effects effect_set drt =
  { drt with effect_set = EffectSet.union drt.effect_set effect_set }

let remove_effects effect_set drt =
  { drt with effect_set = EffectSet.diff drt.effect_set effect_set }

let rec free_skeleton sk =
  let rec go = function
    | SkelParam p -> [ p ]
    | SkelBasic _ -> []
    | SkelApply (_, sks) -> List.concat (List.map free_skeleton sks)
    | SkelArrow (sk1, sk2) -> free_skeleton sk1 @ free_skeleton sk2
    | SkelHandler (sk1, sk2) -> free_skeleton sk1 @ free_skeleton sk2
    | SkelTuple sks -> List.concat (List.map free_skeleton sks)
  in
  let rec nub = function
    | [] -> []
    | [ x ] -> [ x ]
    | x :: xs ->
        let rest = List.filter (fun y -> y <> x) xs in
        let others = nub xs in
        x :: others
  in
  nub (go sk)

(* ************************************************************************* *)
(*                      FREE DIRT VARIABLE COMPUTATION                       *)
(* ************************************************************************* *)

(* Compute the free dirt variables of a target value type *)
let rec fdvsOfTargetValTy : target_ty -> DirtParamSet.t = function
  | TyParam a -> DirtParamSet.empty
  | Arrow (vty, cty) ->
      DirtParamSet.union (fdvsOfTargetValTy vty) (fdvsOfTargetCmpTy cty)
  | Tuple vtys -> fdvsOfTargetValTys vtys
  | Handler (cty1, cty2) ->
      DirtParamSet.union (fdvsOfTargetCmpTy cty1) (fdvsOfTargetCmpTy cty2)
  | TyBasic _prim_ty -> DirtParamSet.empty
  | Apply (_, vtys) -> fdvsOfTargetValTys vtys
  | QualTy (ct, vty) ->
      DirtParamSet.union (fdvsOfValTyCt ct) (fdvsOfTargetValTy vty)
  | QualDirt (ct, vty) ->
      DirtParamSet.union (fdvsOfDirtCt ct) (fdvsOfTargetValTy vty)

(* Compute the free dirt variables of a list of target value types *)
and fdvsOfTargetValTys : target_ty list -> DirtParamSet.t = function
  | [] -> DirtParamSet.empty
  | vty :: vtys ->
      DirtParamSet.union (fdvsOfTargetValTy vty) (fdvsOfTargetValTys vtys)

(* Compute the free dirt variables of a target computation type *)
and fdvsOfTargetCmpTy : target_dirty -> DirtParamSet.t = function
  | vty, dirt -> DirtParamSet.union (fdvsOfTargetValTy vty) (fdvsOfDirt dirt)

(* Compute the free dirt variables of a list of computation value types *)
and fdvsOfTargetCmpTys : target_dirty list -> DirtParamSet.t = function
  | [] -> DirtParamSet.empty
  | cty :: ctys ->
      DirtParamSet.union (fdvsOfTargetCmpTy cty) (fdvsOfTargetCmpTys ctys)

(* Compute the free dirt variables of a value type inequality *)
and fdvsOfValTyCt : ct_ty -> DirtParamSet.t = function
  | vty1, vty2 ->
      DirtParamSet.union (fdvsOfTargetValTy vty1) (fdvsOfTargetValTy vty2)

(* Compute the free dirt variables of a computation type inequality *)
and fdvsOfCmpTyCt : ct_dirty -> DirtParamSet.t = function
  | cty1, cty2 ->
      DirtParamSet.union (fdvsOfTargetCmpTy cty1) (fdvsOfTargetCmpTy cty2)

(* Compute the free dirt variables of a dirt inequality *)
and fdvsOfDirtCt : ct_dirt -> DirtParamSet.t = function
  | dirt1, dirt2 -> DirtParamSet.union (fdvsOfDirt dirt1) (fdvsOfDirt dirt2)

(* Compute the free dirt variables of a dirt *)
and fdvsOfDirt (dirt : dirt) : DirtParamSet.t =
  match dirt.row with
  | ParamRow p -> DirtParamSet.singleton p
  | EmptyRow -> DirtParamSet.empty

(* ************************************************************************* *)
(*                      FREE TYPE VARIABLE COMPUTATION                       *)
(* ************************************************************************* *)

(* Compute the free type variables of a target value type *)
let rec ftvsOfTargetValTy : target_ty -> TyParamSet.t = function
  | TyParam a -> TyParamSet.singleton a
  | Arrow (vty, cty) ->
      TyParamSet.union (ftvsOfTargetValTy vty) (ftvsOfTargetCmpTy cty)
  | Tuple vtys -> ftvsOfTargetValTys vtys
  | Handler (cty1, cty2) ->
      TyParamSet.union (ftvsOfTargetCmpTy cty1) (ftvsOfTargetCmpTy cty2)
  | TyBasic _prim_ty -> TyParamSet.empty
  | Apply (_, vtys) -> ftvsOfTargetValTys vtys
  | QualTy (ct, vty) ->
      TyParamSet.union (ftvsOfValTyCt ct) (ftvsOfTargetValTy vty)
  | QualDirt (_, vty) -> ftvsOfTargetValTy vty

(* Compute the free type variables of a list of target value types *)
and ftvsOfTargetValTys : target_ty list -> TyParamSet.t = function
  | [] -> TyParamSet.empty
  | vty :: vtys ->
      TyParamSet.union (ftvsOfTargetValTy vty) (ftvsOfTargetValTys vtys)

(* Compute the free type variables of a target computation type *)
and ftvsOfTargetCmpTy : target_dirty -> TyParamSet.t = function
  | ty, _dirt -> ftvsOfTargetValTy ty

(* Compute the free type variables of a list of computation value types *)
and ftvsOfTargetCmpTys : target_dirty list -> TyParamSet.t = function
  | [] -> TyParamSet.empty
  | cty :: ctys ->
      TyParamSet.union (ftvsOfTargetCmpTy cty) (ftvsOfTargetCmpTys ctys)

(* Compute the free type variables of a value type inequality *)
and ftvsOfValTyCt : ct_ty -> TyParamSet.t = function
  | vty1, vty2 ->
      TyParamSet.union (ftvsOfTargetValTy vty1) (ftvsOfTargetValTy vty2)

(* Compute the free type variables of a computation type inequality *)
and ftvsOfCmpTyCt : ct_dirty -> TyParamSet.t = function
  | cty1, cty2 ->
      TyParamSet.union (ftvsOfTargetCmpTy cty1) (ftvsOfTargetCmpTy cty2)

(* ************************************************************************* *)

let rec refresh_target_ty (ty_sbst, dirt_sbst) t =
  match t with
  | TyParam x -> (
      match Assoc.lookup x ty_sbst with
      | Some x' -> ((ty_sbst, dirt_sbst), TyParam x')
      | None ->
          let y = CoreTypes.TyParam.fresh () in
          ((Assoc.update x y ty_sbst, dirt_sbst), TyParam y))
  | Arrow (a, c) ->
      let (a_ty_sbst, a_dirt_sbst), a' =
        refresh_target_ty (ty_sbst, dirt_sbst) a
      in
      let temp_ty_sbst = Assoc.concat a_ty_sbst ty_sbst in
      let temp_dirt_sbst = Assoc.concat a_dirt_sbst dirt_sbst in
      let (c_ty_sbst, c_dirt_sbst), c' =
        refresh_target_dirty (temp_ty_sbst, temp_dirt_sbst) c
      in
      ((c_ty_sbst, c_dirt_sbst), Arrow (a', c'))
  | Tuple tup -> ((ty_sbst, dirt_sbst), t)
  | Handler (c1, c2) ->
      let (c1_ty_sbst, c1_dirt_sbst), c1' =
        refresh_target_dirty (ty_sbst, dirt_sbst) c1
      in
      let temp_ty_sbst = Assoc.concat c1_ty_sbst ty_sbst in
      let temp_dirt_sbst = Assoc.concat c1_dirt_sbst dirt_sbst in
      let (c2_ty_sbst, c2_dirt_sbst), c2' =
        refresh_target_dirty (temp_ty_sbst, temp_dirt_sbst) c2
      in
      ((c2_ty_sbst, c2_dirt_sbst), Handler (c1', c2'))
  | TyBasic x -> ((ty_sbst, dirt_sbst), TyBasic x)
  | QualTy (_, a) -> failwith __LOC__
  | QualDirt (_, a) -> failwith __LOC__

and refresh_target_dirty (ty_sbst, dirt_sbst) (t, d) =
  let (t_ty_sbst, t_dirt_sbst), t' = refresh_target_ty (ty_sbst, dirt_sbst) t in
  let temp_ty_sbst = Assoc.concat t_ty_sbst ty_sbst in
  let temp_dirt_sbst = Assoc.concat t_dirt_sbst dirt_sbst in
  let (d_ty_sbst, d_dirt_sbst), d' =
    refresh_target_dirt (temp_ty_sbst, temp_dirt_sbst) d
  in
  ((d_ty_sbst, d_dirt_sbst), (t', d'))

and refresh_target_dirt (ty_sbst, dirt_sbst) drt =
  match drt.row with
  | ParamRow x -> (
      match Assoc.lookup x dirt_sbst with
      | Some x' -> ((ty_sbst, dirt_sbst), { drt with row = ParamRow x' })
      | None ->
          let y = CoreTypes.DirtParam.fresh () in
          ((ty_sbst, Assoc.update x y dirt_sbst), { drt with row = ParamRow y })
      )
  | EmptyRow -> ((ty_sbst, dirt_sbst), drt)

let rec source_to_target ty =
  let loc = Location.unknown in
  match ty with
  | Type.Apply (ty_name, args) when Tctx.transparent ~loc ty_name -> (
      match Tctx.lookup_tydef ~loc ty_name with
      | [], Tctx.Inline ty -> source_to_target ty
      | _, Tctx.Sum _ | _, Tctx.Record _ ->
          assert false (* None of these are transparent *))
  | Type.Apply (ty_name, args) -> Apply (ty_name, List.map source_to_target args)
  | Type.TyParam p -> TyParam p
  | Type.Basic s -> TyBasic s
  | Type.Tuple l -> Tuple (List.map source_to_target l)
  | Type.Arrow (ty, dirty) ->
      Arrow (source_to_target ty, source_to_target_dirty dirty)
  | Type.Handler { value = dirty1; finally = dirty2 } ->
      Handler (source_to_target_dirty dirty1, source_to_target_dirty dirty2)

and source_to_target_dirty ty = (source_to_target ty, empty_dirt)

let constructor_signature lbl =
  match Tctx.infer_variant lbl with
  | None -> assert false
  | Some (ty_out, ty_in) ->
      let ty_in =
        match ty_in with Some ty_in -> ty_in | None -> Type.Tuple []
      in
      (source_to_target ty_in, source_to_target ty_out)
