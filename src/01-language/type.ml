open Utils

(** effect symbols *)

module Label = Symbol.Make (Symbol.String)
module TyParam = TyParam.TyParam

(** variant labels *)

(** Variants for the built-in list type *)
let nil_annot = "$0nil"

let nil = Label.fresh nil_annot
let cons_annot = "$1cons"
let cons = Label.fresh cons_annot

module Field = Symbol.Make (Symbol.String)
(** record fields *)

let bool_tyname = TyName.fresh "bool"
let int_tyname = TyName.fresh "int"
let unit_tyname = TyName.fresh "unit"
let string_tyname = TyName.fresh "string"
let float_tyname = TyName.fresh "float"
let list_tyname = TyName.fresh "list"
let empty_tyname = TyName.fresh "empty"

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

type ty = (ty', Skeleton.t) typed

and ty' =
  | TyParam of TyParam.t
  (* TODO: variance should be read from ty_name parameter *)
  | Apply of { ty_name : TyName.t; ty_args : (ty * variance) TyParam.Map.t }
  | Arrow of abs_ty
  | Tuple of ty list
  | Handler of dirty * dirty
  | TyBasic of Const.ty

and dirty = ty * Dirt.t
and abs_ty = ty * dirty

let rec print_ty ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty.term with
  | TyParam p ->
      print ~at_level:4 "%t:%t" (TyParam.print p) (Skeleton.print ty.ty)
  | Arrow (t1, (t2, drt)) when Dirt.is_empty drt ->
      print ~at_level:3 "%t → %t" (print_ty ~max_level:2 t1)
        (print_ty ~max_level:3 t2)
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:3 "%t -%t→ %t" (print_ty ~max_level:2 t1) (Dirt.print drt)
        (print_ty ~max_level:3 t2)
  | Apply { ty_name; ty_args } -> (
      match TyParam.Map.bindings ty_args with
      | [] -> print "%t" (TyName.print ty_name)
      | [ (_, (s, _)) ] ->
          print ~at_level:1 "%t %t" (print_ty ~max_level:1 s)
            (TyName.print ty_name)
      | ty_args ->
          let ty_args = ty_args |> List.map (fun (_, (s, _)) -> s) in
          print ~at_level:1 "(%t) %t"
            (Print.sequence ", " print_ty ty_args)
            (TyName.print ty_name))
  | Tuple [] -> print "𝟙"
  | Tuple tys ->
      print ~at_level:2 "%t" (Print.sequence "×" (print_ty ~max_level:1) tys)
  | Handler (drty1, drty2) ->
      print ~at_level:3 "%t ⇛ %t"
        (print_dirty ~max_level:2 drty1)
        (print_dirty ~max_level:2 drty2)
  | TyBasic p -> print "%t" (Const.print_ty p)

and print_dirty ?max_level (t1, drt1) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print ~at_level:2 "%t!%t" (print_ty ~max_level:0 t1)
    (Dirt.print ~max_level:0 drt1)

type ct_ty = ty * ty
and ct_dirt = Dirt.t * Dirt.t
and ct_dirty = dirty * dirty

let skeleton_of_ty ty = ty.ty
let skeleton_of_dirty (ty, _) = skeleton_of_ty ty
let tyParam t skel = { term = TyParam t; ty = skel }

let arrow (ty1, drty2) =
  {
    term = Arrow (ty1, drty2);
    ty = Skeleton.Arrow (skeleton_of_ty ty1, skeleton_of_dirty drty2);
  }

let apply (ty_name, ty_args) =
  {
    term = Apply { ty_name; ty_args };
    ty =
      Skeleton.Apply
        {
          ty_name;
          skel_args =
            ty_args |> TyParam.Map.map (fun (ty, _) -> skeleton_of_ty ty);
        };
  }

let tuple tup =
  {
    term = Tuple tup;
    ty = Skeleton.Tuple (List.map (fun ty -> skeleton_of_ty ty) tup);
  }

let handler (drty1, drty2) =
  {
    term = Handler (drty1, drty2);
    ty = Skeleton.Handler (skeleton_of_dirty drty1, skeleton_of_dirty drty2);
  }

let tyBasic pt = { term = TyBasic pt; ty = Skeleton.Basic pt }
let unit_ty = tuple []
let empty_ty = apply (empty_tyname, TyParam.Map.empty)
let int_ty = tyBasic Const.IntegerTy
let float_ty = tyBasic Const.FloatTy
let bool_ty = tyBasic Const.BooleanTy

let string_ty = tyBasic Const.StringTy
and skeleton_of_dirty (ty, _) = skeleton_of_ty ty

module Params = struct
  type t = {
    ty_params : Skeleton.t TyParam.Map.t;
    dirt_params : Dirt.Param.Set.t;
    skel_params : Skeleton.Param.Set.t;
  }

  let empty =
    {
      ty_params = TyParam.Map.empty;
      dirt_params = Dirt.Param.Set.empty;
      skel_params = Skeleton.Param.Set.empty;
    }

  let print fp ppf =
    Format.fprintf ppf "{ %t, %t, %t }"
      (Skeleton.Param.Set.print fp.skel_params)
      (Dirt.Param.Set.print fp.dirt_params)
      (TyParam.Map.print Skeleton.print fp.ty_params)

  let subset fp1 fp2 =
    TyParam.Map.for_all
      (fun p1 _ -> TyParam.Map.mem p1 fp2.ty_params)
      fp1.ty_params
    && Dirt.Param.Set.subset fp1.dirt_params fp2.dirt_params
    && Skeleton.Param.Set.subset fp1.skel_params fp2.skel_params

  let ty_singleton p skel =
    { empty with ty_params = TyParam.Map.singleton p skel }

  let dirt_singleton p = { empty with dirt_params = Dirt.Param.Set.singleton p }

  let skel_singleton p =
    { empty with skel_params = Skeleton.Param.Set.singleton p }

  let union fp1 fp2 =
    {
      ty_params =
        TyParam.Map.union
          (fun _ skel1 skel2 ->
            assert (skel1 = skel2);
            Some skel1)
          fp1.ty_params fp2.ty_params;
      dirt_params = Dirt.Param.Set.union fp1.dirt_params fp2.dirt_params;
      skel_params = Skeleton.Param.Set.union fp1.skel_params fp2.skel_params;
    }

  let union_map free_params =
    List.fold_left (fun fp x -> union fp (free_params x)) empty

  let is_empty fp =
    Dirt.Param.Set.is_empty fp.dirt_params
    && Skeleton.Param.Set.is_empty fp.skel_params
end

let rec free_params_skeleton = function
  | Skeleton.Param p -> Params.skel_singleton p
  | Skeleton.Basic _ -> Params.empty
  | Skeleton.Apply { skel_args; _ } ->
      skel_args |> TyParam.Map.values
      |> Params.union_map (fun s -> free_params_skeleton s)
  | Skeleton.Arrow (sk1, sk2) ->
      Params.union (free_params_skeleton sk1) (free_params_skeleton sk2)
  | Skeleton.Handler (sk1, sk2) ->
      Params.union (free_params_skeleton sk1) (free_params_skeleton sk2)
  | Skeleton.Tuple sks -> Params.union_map free_params_skeleton sks

let rec free_params_ty ty =
  Params.union (free_params_ty' ty.ty ty.term) (free_params_skeleton ty.ty)

and free_params_ty' skel = function
  | TyParam p -> Params.ty_singleton p skel
  | Arrow (vty, cty) ->
      Params.union (free_params_ty vty) (free_params_dirty cty)
  | Tuple vtys -> Params.union_map free_params_ty vtys
  | Handler (cty1, cty2) ->
      Params.union (free_params_dirty cty1) (free_params_dirty cty2)
  | TyBasic _prim_ty -> Params.empty
  | Apply { ty_args; _ } ->
      ty_args |> TyParam.Map.values
      |> Params.union_map (fun (ty, _) -> free_params_ty ty)

and free_params_dirty (ty, dirt) =
  Params.union (free_params_ty ty) (free_params_dirt dirt)

and free_params_abstraction_ty (ty_in, drty_out) =
  Params.union (free_params_ty ty_in) (free_params_dirty drty_out)

and free_params_abstraction2_ty (ty_in1, ty_in2, drty_out) =
  Params.union
    (Params.union (free_params_ty ty_in1) (free_params_ty ty_in2))
    (free_params_dirty drty_out)

and free_params_ct_ty (vty1, vty2) =
  Params.union (free_params_ty vty1) (free_params_ty vty2)

and free_params_ct_dirty (cty1, cty2) =
  Params.union (free_params_dirty cty1) (free_params_dirty cty2)

and free_params_ct_dirt (dirt1, dirt2) =
  Params.union (free_params_dirt dirt1) (free_params_dirt dirt2)

and free_params_dirt (dirt : Dirt.t) =
  match dirt.row with
  | Dirt.Row.Param p -> Params.dirt_singleton p
  | Dirt.Row.Empty -> Params.empty

type tydef =
  | Record of ty Field.Map.t
  | Sum of ty option Field.Map.t
  | Inline of ty

type tydef_params = {
  type_params : (Skeleton.t * variance) TyParam.Map.t;
  dirt_params : Dirt.Param.Set.t;
  skel_params : Skeleton.Param.Set.t;
}

let empty_tydef_params =
  {
    type_params = TyParam.Map.empty;
    dirt_params = Dirt.Param.Set.empty;
    skel_params = Skeleton.Param.Set.empty;
  }

type type_data = { params : tydef_params; type_def : tydef }

let print_ct_ty (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ≤ %t" (print_ty ty1) (print_ty ty2)

and print_ct_dirt (ty1, ty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t ≤ %t" (Dirt.print ty1) (Dirt.print ty2)

and print_abs_ty (ty1, drty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t → %t" (print_ty ty1) (print_dirty drty2)

let type_const c = tyBasic (Const.infer_ty c)

(* ************************************************************************* *)
(*                       PREDICATES ON ty                             *)
(* ************************************************************************* *)

let rec equal_ty (ty1 : ty) (ty2 : ty) =
  Skeleton.equal ty1.ty ty2.ty && equal_ty' ty1.term ty2.term

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
      && TyParam.Map.equal (fun (ty1, _) (ty2, _) -> equal_ty ty1 ty2) tys1 tys2
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      equal_dirty dirtya1 dirtyb1 && equal_dirty dirtya2 dirtyb2
  | TyBasic ptya, TyBasic ptyb -> ptya = ptyb
  | _ -> false

and equal_dirty (ty1, d1) (ty2, d2) = equal_ty ty1 ty2 && equal_dirt d1 d2

and equal_dirt d1 d2 =
  Effect.Set.equal d1.effect_set d2.effect_set && d1.row = d2.row

let make_dirty ty = (ty, Dirt.fresh ())
let pure_ty ty = (ty, Dirt.empty)

let fresh_skel () =
  let skel_var = Skeleton.Param.fresh () in
  Skeleton.Param skel_var

let fresh_ty_param () =
  let ty_param = TyParam.fresh () and skel = Skeleton.Param.fresh () in
  (ty_param, skel)

let fresh_ty_with_skel skel =
  let ty_var = TyParam.fresh () in
  tyParam ty_var skel

let fresh_dirty_param_with_skel skel =
  let ty = fresh_ty_with_skel skel in
  make_dirty ty

let fresh_ty_with_fresh_skel () = fresh_ty_with_skel (fresh_skel ())
let fresh_dirty_with_fresh_skel () = fresh_dirty_param_with_skel (fresh_skel ())

let fresh_ty_with_skel type_definitions skel =
  match skel with
  (* α : ς *)
  | Skeleton.Param _ -> assert false
  (* α : int *)
  | Skeleton.Basic ps -> tyBasic ps
  (* α : τ₁ -> τ₂ *)
  | Skeleton.Arrow (sk1, sk2) ->
      let tvar1 = fresh_ty_with_skel sk1
      and dtvar2 = fresh_dirty_param_with_skel sk2 in
      arrow (tvar1, dtvar2)
  (* α : τ₁ x τ₂ ... *)
  | Skeleton.Tuple sks ->
      let tvars = List.map fresh_ty_with_skel sks in
      tuple tvars
  (* α : ty_name (τ₁, τ₂, ...) *)
  | Skeleton.Apply { ty_name; skel_args } ->
      let tvars =
        match Assoc.lookup ty_name type_definitions with
        | Some tydata ->
            TyParam.Map.mapi
              (fun ty_param s ->
                ( fresh_ty_with_skel s,
                  TyParam.Map.find ty_param tydata.params.type_params
                  |> fun (_skel, variance) -> variance ))
              skel_args
        | None -> assert false
        (* Type should be known *)
      in
      apply (ty_name, tvars)
  (* α : τ₁ => τ₂ *)
  | Skeleton.Handler (sk1, sk2) ->
      let dtvar1 = fresh_dirty_param_with_skel sk1
      and dtvar2 = fresh_dirty_param_with_skel sk2 in
      handler (dtvar1, dtvar2)

let rec print_pretty_skel ?max_level free params skel ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match skel with
  | Skeleton.Param s ->
      let symb =
        match Assoc.lookup s !params with
        | Some symb -> symb
        | None ->
            let next_index = Assoc.length !params in
            let symb = "abcdefghijklmnopqrstuvwxyz".[next_index] in
            params := Assoc.update s symb !params;
            symb
      in
      if Skeleton.Param.Set.mem s free then print "'%c" symb
      else print "'_%c" symb
  | Skeleton.Arrow (skel1, skel2) ->
      print ~at_level:3 "%t -> %t"
        (print_pretty_skel ~max_level:2 free params skel1)
        (print_pretty_skel ~max_level:3 free params skel2)
  | Skeleton.Apply { ty_name; skel_args } -> (
      match TyParam.Map.values skel_args with
      | [] -> print "%t" (TyName.print ty_name)
      | [ s ] ->
          print ~at_level:1 "%t %t"
            (print_pretty_skel ~max_level:1 free params s)
            (TyName.print ty_name)
      | skels ->
          print ~at_level:1 "(%t) %t"
            (Print.sequence ", " (print_pretty_skel free params) skels)
            (TyName.print ty_name))
  | Skeleton.Tuple [] -> print "unit"
  | Skeleton.Tuple skels ->
      print ~at_level:2 "%t"
        (Print.sequence " * "
           (print_pretty_skel free ~max_level:1 params)
           skels)
  | Skeleton.Handler (skel1, skel2) ->
      print ~at_level:3 "%t => %t"
        (print_pretty_skel free ~max_level:2 params skel1)
        (print_pretty_skel free ~max_level:2 params skel2)
  | Skeleton.Basic p -> print "%t" (Const.print_ty p)

let print_pretty free = print_pretty_skel free (ref Assoc.empty)
let list_ty_param, list_skel = fresh_ty_param ()
