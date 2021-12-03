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

module TyParam = CoreTypes.TyParam
module Effect = CoreTypes.Effect

type effect_set = Effect.Set.t

type skeleton =
  | SkelParam of SkelParam.t
  | SkelBasic of Const.ty
  | SkelArrow of skeleton * skeleton
  | SkelApply of CoreTypes.TyName.t * skeleton list
  | SkelHandler of skeleton * skeleton
  | SkelTuple of skeleton list

let rec print_skeleton ?max_level sk ppf =
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

type ty = (ty', skeleton) typed

and ty' =
  | TyParam of CoreTypes.TyParam.t
  | Apply of { ty_name : CoreTypes.TyName.t; ty_args : ty list }
  | Arrow of abs_ty
  | Tuple of ty list
  | Handler of dirty * dirty
  | TyBasic of Const.ty

and dirty = ty * dirt

and dirt = { effect_set : effect_set; row : row }

and abs_ty = ty * dirty

and row = ParamRow of DirtParam.t | EmptyRow

let is_empty_dirt dirt =
  Effect.Set.is_empty dirt.effect_set && dirt.row = EmptyRow

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
  | Apply { ty_name; ty_args = [] } ->
      print "%t" (CoreTypes.TyName.print ty_name)
  | Apply { ty_name; ty_args = [ s ] } ->
      print ~at_level:1 "%t %t" (print_ty ~max_level:1 s)
        (CoreTypes.TyName.print ty_name)
  | Apply { ty_name; ty_args } ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty ty_args)
        (CoreTypes.TyName.print ty_name)
  | Tuple [] -> print "𝟙"
  | Tuple tys ->
      print ~at_level:2 "%t" (Print.sequence "×" (print_ty ~max_level:1) tys)
  | Handler (drty1, drty2) ->
      print ~at_level:3 "%t ⇛ %t"
        (print_dirty ~max_level:2 drty1)
        (print_dirty ~max_level:2 drty2)
  | TyBasic p -> print "%t" (Const.print_ty p)

and print_dirt ?max_level drt ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, EmptyRow -> print "{%t}" (print_effect_set effect_set)
  | effect_set, ParamRow p when Effect.Set.is_empty effect_set ->
      print "%t" (DirtParam.print p)
  | effect_set, ParamRow p ->
      print ~at_level:1 "{%t}∪%t"
        (print_effect_set effect_set)
        (DirtParam.print p)

and print_effect_set effect_set =
  Print.sequence "," CoreTypes.Effect.print (Effect.Set.elements effect_set)

and print_dirty ?max_level (t1, drt1) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print ~at_level:2 "%t!%t" (print_ty ~max_level:0 t1)
    (print_dirt ~max_level:0 drt1)

type ct_ty = ty * ty

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

let apply (ty_name, ty_args) =
  {
    term = Apply { ty_name; ty_args };
    ty = SkelApply (ty_name, List.map (fun ty -> skeleton_of_ty ty) ty_args);
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

module Params = struct
  type t = {
    ty_params : skeleton TyParam.Map.t;
    dirt_params : DirtParam.Set.t;
    skel_params : SkelParam.Set.t;
  }

  let empty =
    {
      ty_params = TyParam.Map.empty;
      dirt_params = DirtParam.Set.empty;
      skel_params = SkelParam.Set.empty;
    }

  let subset fp1 fp2 =
    TyParam.Map.for_all
      (fun p1 _ -> TyParam.Map.mem p1 fp2.ty_params)
      fp1.ty_params
    && DirtParam.Set.subset fp1.dirt_params fp2.dirt_params
    && SkelParam.Set.subset fp1.skel_params fp2.skel_params

  let ty_singleton p skel =
    { empty with ty_params = TyParam.Map.singleton p skel }

  let dirt_singleton p = { empty with dirt_params = DirtParam.Set.singleton p }

  let skel_singleton p = { empty with skel_params = SkelParam.Set.singleton p }

  let union fp1 fp2 =
    {
      ty_params =
        TyParam.Map.union
          (fun _ skel1 skel2 ->
            (* Print.debug "%t %t = %t"
               (CoreTypes.TyParam.print t)
               (print_skeleton skel1) (print_skeleton skel2); *)
            assert (skel1 = skel2);
            Some skel1)
          fp1.ty_params fp2.ty_params;
      dirt_params = DirtParam.Set.union fp1.dirt_params fp2.dirt_params;
      skel_params = SkelParam.Set.union fp1.skel_params fp2.skel_params;
    }

  let union_map free_params =
    List.fold_left (fun fp x -> union fp (free_params x)) empty

  let is_empty fp =
    DirtParam.Set.is_empty fp.dirt_params
    && SkelParam.Set.is_empty fp.skel_params
end

let rec free_params_skeleton = function
  | SkelParam p -> Params.skel_singleton p
  | SkelBasic _ -> Params.empty
  | SkelApply (_, sks) -> Params.union_map free_params_skeleton sks
  | SkelArrow (sk1, sk2) ->
      Params.union (free_params_skeleton sk1) (free_params_skeleton sk2)
  | SkelHandler (sk1, sk2) ->
      Params.union (free_params_skeleton sk1) (free_params_skeleton sk2)
  | SkelTuple sks -> Params.union_map free_params_skeleton sks

let rec free_params_ty ty =
  match ty.term with
  | TyParam p -> Params.ty_singleton p ty.ty
  | Arrow (vty, cty) ->
      Params.union (free_params_ty vty) (free_params_dirty cty)
  | Tuple vtys -> Params.union_map free_params_ty vtys
  | Handler (cty1, cty2) ->
      Params.union (free_params_dirty cty1) (free_params_dirty cty2)
  | TyBasic _prim_ty -> Params.empty
  | Apply { ty_args; _ } -> Params.union_map free_params_ty ty_args

and free_params_dirty (ty, dirt) =
  Params.union (free_params_ty ty) (free_params_dirt dirt)

and free_params_abstraction_ty (ty_in, drty_out) =
  Params.union (free_params_ty ty_in) (free_params_dirty drty_out)

and free_params_ct_ty (vty1, vty2) =
  Params.union (free_params_ty vty1) (free_params_ty vty2)

and free_params_ct_dirty (cty1, cty2) =
  Params.union (free_params_dirty cty1) (free_params_dirty cty2)

and free_params_ct_dirt (dirt1, dirt2) =
  Params.union (free_params_dirt dirt1) (free_params_dirt dirt2)

and free_params_dirt (dirt : dirt) =
  match dirt.row with
  | ParamRow p -> Params.dirt_singleton p
  | EmptyRow -> Params.empty

type tydef =
  | Record of (CoreTypes.Field.t, ty) Assoc.t
  | Sum of (CoreTypes.Label.t, ty option) Assoc.t
  | Inline of ty

type type_data = { params : Params.t; type_def : tydef }

let print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ≤ %t" (print_ty ty1) (print_ty ty2)

and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ≤ %t" (print_dirt ty1) (print_dirt ty2)

and print_abs_ty (ty1, drty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t → %t" (print_ty ty1) (print_dirty drty2)

module Constraints = struct
  type t = {
    ty_constraints :
      (TyCoercionParam.t
      * CoreTypes.TyParam.t
      * CoreTypes.TyParam.t
      * SkelParam.t)
      list;
    dirt_constraints : (DirtCoercionParam.t * ct_dirt) list;
  }

  let empty = { ty_constraints = []; dirt_constraints = [] }

  let add_ty_constraint resolved omega ty1 ty2 skel =
    {
      resolved with
      ty_constraints = (omega, ty1, ty2, skel) :: resolved.ty_constraints;
    }

  let add_dirt_constraint resolved omega ct =
    {
      resolved with
      dirt_constraints = (omega, ct) :: resolved.dirt_constraints;
    }

  let free_params res =
    let free_params_ty =
      Params.union_map
        (fun (_, ty1, ty2, skel) ->
          Params.union
            {
              Params.empty with
              ty_params =
                TyParam.Map.of_seq
                  (List.to_seq [ (ty1, SkelParam skel); (ty2, SkelParam skel) ]);
            }
            (Params.skel_singleton skel))
        res.ty_constraints
    and free_params_dirt =
      Params.union_map
        (fun (_, dt) -> free_params_ct_dirt dt)
        res.dirt_constraints
    in
    Params.union free_params_ty free_params_dirt

  let print c ppf =
    let print_dirt_constraint (p, (ty1, ty2)) ppf =
      Print.print ppf "%t: (%t ≤ %t)"
        (DirtCoercionParam.print p)
        (print_dirt ty1) (print_dirt ty2)
    and print_ty_constraint (p, ty1, ty2, s) ppf =
      Print.print ppf "%t: (%t ≤ %t) : %t" (TyCoercionParam.print p)
        (CoreTypes.TyParam.print ty1)
        (CoreTypes.TyParam.print ty2)
        (SkelParam.print s)
    in
    Print.print ppf "{ %t / %t }"
      (Print.sequence ";" print_dirt_constraint c.dirt_constraints)
      (Print.sequence ";" print_ty_constraint c.ty_constraints)
end

let type_const c = tyBasic (Const.infer_ty c)

type ty_scheme = { params : Params.t; constraints : Constraints.t; ty : ty }

let monotype ty = { params = Params.empty; constraints = Constraints.empty; ty }

(* ************************************************************************* *)
(*                       PREDICATES ON ty                             *)
(* ************************************************************************* *)
let rec equal_skeleton skel1 skel2 =
  match (skel1, skel2) with
  | SkelParam tv1, SkelParam tv2 -> tv1 = tv2
  | SkelArrow (ttya1, dirtya1), SkelArrow (ttyb1, dirtyb1) ->
      equal_skeleton ttya1 ttyb1 && equal_skeleton dirtya1 dirtyb1
  | SkelTuple tys1, SkelTuple tys2 ->
      List.length tys1 = List.length tys2
      && List.for_all2 equal_skeleton tys1 tys2
  | SkelApply (ty_name1, tys1), SkelApply (ty_name2, tys2) ->
      ty_name1 = ty_name2
      && List.length tys1 = List.length tys2
      && List.for_all2 equal_skeleton tys1 tys2
  | SkelHandler (dirtya1, dirtya2), SkelHandler (dirtyb1, dirtyb2) ->
      equal_skeleton dirtya1 dirtyb1 && equal_skeleton dirtya2 dirtyb2
  | SkelBasic ptya, SkelBasic ptyb -> ptya = ptyb
  | _, _ -> false

let rec equal_ty (ty1 : ty) (ty2 : ty) =
  equal_skeleton ty1.ty ty2.ty && equal_ty' ty1.term ty2.term

and equal_ty' ty1' ty2' =
  match (ty1', ty2') with
  | TyParam tv1, TyParam tv2 -> tv1 = tv2
  | Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1) ->
      equal_ty ttya1 ttyb1 && equal_dirty dirtya1 dirtyb1
  | Tuple tys1, Tuple tys2 ->
      List.length tys1 = List.length tys2 && List.for_all2 equal_ty tys1 tys2
  | ( Apply { ty_name = ty_name1; ty_args = tys1 },
      Apply { ty_name = ty_name2; ty_args = tys2 } ) ->
      ty_name1 = ty_name2
      && List.length tys1 = List.length tys2
      && List.for_all2 equal_ty tys1 tys2
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      equal_dirty dirtya1 dirtyb1 && equal_dirty dirtya2 dirtyb2
  | TyBasic ptya, TyBasic ptyb -> ptya = ptyb
  | _ -> false

and equal_dirty (ty1, d1) (ty2, d2) = equal_ty ty1 ty2 && equal_dirt d1 d2

and equal_dirt d1 d2 =
  Effect.Set.equal d1.effect_set d2.effect_set && d1.row = d2.row

let no_effect_dirt dirt_param =
  { effect_set = Effect.Set.empty; row = ParamRow dirt_param }

let fresh_dirt () = no_effect_dirt (DirtParam.fresh ())

let closed_dirt effect_set = { effect_set; row = EmptyRow }

let empty_dirt = closed_dirt Effect.Set.empty

let make_dirty ty = (ty, fresh_dirt ())

let pure_ty ty = (ty, empty_dirt)

let add_effects effect_set drt =
  { drt with effect_set = Effect.Set.union drt.effect_set effect_set }

let fresh_skel () =
  let skel_var = SkelParam.fresh () in
  SkelParam skel_var

let fresh_ty_param () =
  let ty_param = CoreTypes.TyParam.fresh () and skel = SkelParam.fresh () in
  (ty_param, skel)

let fresh_ty_with_skel skel =
  let ty_var = CoreTypes.TyParam.fresh () in
  tyParam ty_var skel

let fresh_dirty_param_with_skel skel =
  let ty = fresh_ty_with_skel skel in
  make_dirty ty

let fresh_ty_with_fresh_skel () = fresh_ty_with_skel (fresh_skel ())

let fresh_dirty_with_fresh_skel () = fresh_dirty_param_with_skel (fresh_skel ())

let fresh_ty_with_skel skel =
  match skel with
  (* α : ς *)
  | SkelParam _ -> assert false
  (* α : int *)
  | SkelBasic ps -> tyBasic ps
  (* α : τ₁ -> τ₂ *)
  | SkelArrow (sk1, sk2) ->
      let tvar1 = fresh_ty_with_skel sk1
      and dtvar2 = fresh_dirty_param_with_skel sk2 in
      arrow (tvar1, dtvar2)
  (* α : τ₁ x τ₂ ... *)
  | SkelTuple sks ->
      let tvars = List.map fresh_ty_with_skel sks in
      tuple tvars
  (* α : ty_name (τ₁, τ₂, ...) *)
  | SkelApply (ty_name, sks) ->
      let tvars = List.map fresh_ty_with_skel sks in
      apply (ty_name, tvars)
  (* α : τ₁ => τ₂ *)
  | SkelHandler (sk1, sk2) ->
      let dtvar1 = fresh_dirty_param_with_skel sk1
      and dtvar2 = fresh_dirty_param_with_skel sk2 in
      handler (dtvar1, dtvar2)

let rec print_pretty_skel ?max_level params skel ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match skel with
  | SkelParam s ->
      let symb =
        match Assoc.lookup s !params with
        | Some symb -> symb
        | None ->
            let next_index = Assoc.length !params in
            let symb = "abcdefghijklmnopqrstuvwxyz".[next_index] in
            params := Assoc.update s symb !params;
            symb
      in
      print "'%c" symb
  | SkelArrow (skel1, skel2) ->
      print ~at_level:3 "%t -> %t"
        (print_pretty_skel ~max_level:2 params skel1)
        (print_pretty_skel ~max_level:3 params skel2)
  | SkelApply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | SkelApply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_pretty_skel ~max_level:1 params s)
        (CoreTypes.TyName.print t)
  | SkelApply (t, skels) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " (print_pretty_skel params) skels)
        (CoreTypes.TyName.print t)
  | SkelTuple [] -> print "unit"
  | SkelTuple skels ->
      print ~at_level:2 "%t"
        (Print.sequence " * " (print_pretty_skel ~max_level:1 params) skels)
  | SkelHandler (skel1, skel2) ->
      print ~at_level:3 "%t => %t"
        (print_pretty_skel ~max_level:2 params skel1)
        (print_pretty_skel ~max_level:2 params skel2)
  | SkelBasic p -> print "%t" (Const.print_ty p)

let print_pretty () = print_pretty_skel (ref Assoc.empty)

(* ************************************************************************* *)
(*                         FREE VARIABLE COMPUTATION                         *)
(* ************************************************************************* *)

(* ************************************************************************* *)

module Renaming = struct
  type t = {
    ty_params : CoreTypes.TyParam.t TyParam.Map.t;
    dirt_params : DirtParam.t DirtParam.Map.t;
    skel_params : SkelParam.t SkelParam.Map.t;
  }

  let empty =
    {
      ty_params = TyParam.Map.empty;
      dirt_params = DirtParam.Map.empty;
      skel_params = SkelParam.Map.empty;
    }
end

let params_renaming (params : Params.t) : Renaming.t =
  {
    skel_params =
      SkelParam.Set.fold
        (fun p -> SkelParam.Map.add p (SkelParam.refresh p))
        params.skel_params SkelParam.Map.empty;
    ty_params =
      TyParam.Map.mapi
        (fun p _skel -> CoreTypes.TyParam.refresh p)
        params.ty_params;
    dirt_params =
      DirtParam.Set.fold
        (fun d -> DirtParam.Map.add d (DirtParam.refresh d))
        params.dirt_params DirtParam.Map.empty;
  }

let rename_skel_param (sbst : Renaming.t) p =
  SkelParam.Map.find_opt p sbst.skel_params |> Option.value ~default:p

let rename_ty_param (sbst : Renaming.t) t =
  TyParam.Map.find_opt t sbst.ty_params |> Option.value ~default:t

let rename_dirt_param (sbst : Renaming.t) d =
  DirtParam.Map.find_opt d sbst.dirt_params |> Option.value ~default:d

let rec rename_skeleton (sbst : Renaming.t) = function
  | SkelParam p -> SkelParam (rename_skel_param sbst p)
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
  | TyParam p -> TyParam (rename_ty_param sbst p)
  | Arrow (vty, cty) -> Arrow (rename_ty sbst vty, rename_dirty sbst cty)
  | Tuple vtys -> Tuple (List.map (rename_ty sbst) vtys)
  | Handler (cty1, cty2) ->
      Handler (rename_dirty sbst cty1, rename_dirty sbst cty2)
  | TyBasic _ as ty -> ty
  | Apply { ty_name; ty_args } ->
      Apply { ty_name; ty_args = List.map (rename_ty sbst) ty_args }

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
  | ParamRow p -> { dirt with row = ParamRow (rename_dirt_param sbst p) }

let rename_params (sbst : Renaming.t) (params : Params.t) =
  {
    Params.skel_params =
      SkelParam.Set.map (rename_skel_param sbst) params.skel_params;
    ty_params =
      params.ty_params |> TyParam.Map.to_seq
      |> Seq.map (fun (p, skel) ->
             (rename_ty_param sbst p, rename_skeleton sbst skel))
      |> TyParam.Map.of_seq;
    dirt_params = DirtParam.Set.map (rename_dirt_param sbst) params.dirt_params;
  }

let rename_constraints (sbst : Renaming.t) (constraints : Constraints.t) =
  {
    Constraints.ty_constraints =
      List.map
        (fun (p, ty1, ty2, skel) ->
          ( p,
            rename_ty_param sbst ty1,
            rename_ty_param sbst ty2,
            rename_skel_param sbst skel ))
        constraints.ty_constraints;
    dirt_constraints =
      List.map
        (fun (p, dt) -> (p, rename_ct_dirt sbst dt))
        constraints.dirt_constraints;
  }

let rename_ty_scheme sbst ty_scheme =
  {
    params = rename_params sbst ty_scheme.params;
    constraints = rename_constraints sbst ty_scheme.constraints;
    ty = rename_ty sbst ty_scheme.ty;
  }

let refresh_ty_scheme ty_scheme =
  let sbst = params_renaming ty_scheme.params in
  rename_ty_scheme sbst ty_scheme
