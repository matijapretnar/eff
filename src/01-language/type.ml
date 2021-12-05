open Utils

module Effect = Symbol.Make (Symbol.String)
(** effect symbols *)

module Label = Symbol.Make (Symbol.String)
(** variant labels *)

(** Variants for the built-in list type *)
let nil_annot = "$0nil"

let nil = Label.fresh nil_annot

let cons_annot = "$1cons"

let cons = Label.fresh cons_annot

module Field = Symbol.Make (Symbol.String)
(** record fields *)

module TyName = Symbol.Make (Symbol.String)
(** type names *)

let bool_tyname = TyName.fresh "bool"

let int_tyname = TyName.fresh "int"

let unit_tyname = TyName.fresh "unit"

let string_tyname = TyName.fresh "string"

let float_tyname = TyName.fresh "float"

let list_tyname = TyName.fresh "list"

let empty_tyname = TyName.fresh "empty"

(** type parameters *)
module TyParam = struct
  include Symbol.Make (Symbol.Parameter (struct
    let ascii_symbol = "ty"

    let utf8_symbol = "\207\132"
  end))

  let print_old ?(poly = []) k ppf =
    let c = if List.mem k poly then "'" else "'_" in
    fold
      (fun _ k ->
        if 0 <= k && k <= 25 then
          Format.fprintf ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
        else Format.fprintf ppf "%sty%i" c (k - 25))
      k
end

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

type effect_set = Effect.Set.t

type skeleton =
  | SkelParam of SkelParam.t
  | SkelBasic of Const.ty
  | SkelArrow of skeleton * skeleton
  | SkelApply of TyName.t * skeleton list
  | SkelHandler of skeleton * skeleton
  | SkelTuple of skeleton list

let rec print_skeleton ?max_level sk ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sk with
  | SkelParam p -> SkelParam.print p ppf
  | SkelBasic s -> print "%t" (Const.print_ty s)
  | SkelArrow (sk1, sk2) ->
      print "%t → %t" (print_skeleton sk1) (print_skeleton sk2)
  | SkelApply (t, []) -> print "%t" (TyName.print t)
  | SkelApply (t, [ s ]) ->
      print ~at_level:1 "%t %t" (print_skeleton ~max_level:1 s) (TyName.print t)
  | SkelApply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_skeleton ts)
        (TyName.print t)
  | SkelTuple [] -> print "𝟙"
  | SkelTuple sks ->
      print ~at_level:2 "%t"
        (Print.sequence "×" (print_skeleton ~max_level:1) sks)
  | SkelHandler (sk1, sk2) ->
      print "%t ⇛ %t" (print_skeleton sk1) (print_skeleton sk2)

type ty = (ty', skeleton) typed

and ty' =
  | TyParam of TyParam.t
  | Apply of { ty_name : TyName.t; ty_args : ty list }
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
      print ~at_level:4 "%t:%t" (TyParam.print p) (print_skeleton ty.ty)
  | Arrow (t1, (t2, drt)) when is_empty_dirt drt ->
      print ~at_level:3 "%t → %t" (print_ty ~max_level:2 t1)
        (print_ty ~max_level:3 t2)
  | Arrow (t1, (t2, drt)) ->
      print ~at_level:3 "%t -%t→ %t" (print_ty ~max_level:2 t1)
        (print_dirt drt) (print_ty ~max_level:3 t2)
  | Apply { ty_name; ty_args = [] } -> print "%t" (TyName.print ty_name)
  | Apply { ty_name; ty_args = [ s ] } ->
      print ~at_level:1 "%t %t" (print_ty ~max_level:1 s) (TyName.print ty_name)
  | Apply { ty_name; ty_args } ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_ty ty_args)
        (TyName.print ty_name)
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
  Print.sequence "," Effect.print (Effect.Set.elements effect_set)

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

let empty_ty = apply (empty_tyname, [])

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
               (TyParam.print t)
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
  | Record of ty Field.Map.t
  | Sum of ty option Field.Map.t
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

module TyConstraints = struct
  module TyParamGraph = Graph.Make (TyParam)

  type t = TyCoercionParam.t TyParamGraph.t SkelParam.Map.t

  let empty = SkelParam.Map.empty

  (* Since we only add and never remove type constraints, the set of constraints
     is empty if and only iff there are no skeleton graphs in it *)
  let is_empty = SkelParam.Map.is_empty

  let get_ty_graph (ty_constraints : t) s =
    SkelParam.Map.find_opt s ty_constraints
    |> Option.value ~default:TyParamGraph.empty

  let add_edge s t1 t2 w (ty_constraints : t) : t =
    let s_graph' =
      get_ty_graph ty_constraints s |> TyParamGraph.add_edge t1 t2 w
    in
    SkelParam.Map.add s s_graph' ty_constraints

  let fold f (ty_constraints : t) acc =
    SkelParam.Map.fold (fun s -> TyParamGraph.fold (f s)) ty_constraints acc

  let fold_expanded f =
    fold (fun s t1 t2 w ->
        let skel = SkelParam s in
        let ty1 = tyParam t1 skel and ty2 = tyParam t2 skel in
        f s t1 t2 w ty1 ty2)

  let free_params (ty_constraints : t) =
    fold
      (fun s t1 t2 _w params ->
        let skel = SkelParam s in
        Params.union
          (Params.union (Params.skel_singleton s)
             (Params.union
                (Params.ty_singleton t1 skel)
                (Params.ty_singleton t2 skel)))
          params)
      ty_constraints Params.empty
end

module Constraints = struct
  type t = {
    ty_constraints : TyConstraints.t;
    dirt_constraints : (DirtCoercionParam.t * ct_dirt) list;
  }

  let empty = { ty_constraints = TyConstraints.empty; dirt_constraints = [] }

  let is_empty constraints =
    TyConstraints.is_empty constraints.ty_constraints
    && constraints.dirt_constraints = []

  let add_ty_constraint s t1 t2 w constraints =
    {
      constraints with
      ty_constraints =
        TyConstraints.add_edge s t1 t2 w constraints.ty_constraints;
    }

  let add_dirt_constraint constraints omega ct =
    {
      constraints with
      dirt_constraints = (omega, ct) :: constraints.dirt_constraints;
    }

  let free_params res =
    let free_params_ty = TyConstraints.free_params res.ty_constraints
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
      (* and print_ty_constraint (p, ty1, ty2, s) ppf =
         Print.print ppf "%t: (%t ≤ %t) : %t" (TyCoercionParam.print p)
           (TyParam.print ty1) (TyParam.print ty2) (SkelParam.print s) *)
    in
    Print.print ppf "{ %t }"
      (Print.sequence ";" print_dirt_constraint c.dirt_constraints)

  (* (Print.sequence ";" print_ty_constraint c.ty_constraints) *)
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
  let ty_param = TyParam.fresh () and skel = SkelParam.fresh () in
  (ty_param, skel)

let fresh_ty_with_skel skel =
  let ty_var = TyParam.fresh () in
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
  | SkelApply (t, []) -> print "%t" (TyName.print t)
  | SkelApply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_pretty_skel ~max_level:1 params s)
        (TyName.print t)
  | SkelApply (t, skels) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " (print_pretty_skel params) skels)
        (TyName.print t)
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
