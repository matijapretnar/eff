open Utils

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
  | Apply of { ty_name : TyName.t; ty_args : ty list }
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
      print ~at_level:3 "%t -%t→ %t" (print_ty ~max_level:2 t1)
        (Dirt.print drt) (print_ty ~max_level:3 t2)
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
    ty = Skeleton.Apply (ty_name, List.map (fun ty -> skeleton_of_ty ty) ty_args);
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

let empty_ty = apply (empty_tyname, [])

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
            (* Print.debug "%t %t = %t"
               (TyParam.print t)
               (print_skeleton skel1) (print_skeleton skel2); *)
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
  | Skeleton.Apply (_, sks) -> Params.union_map free_params_skeleton sks
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

and free_params_dirt (dirt : Dirt.t) =
  match dirt.row with
  | Dirt.Row.Param p -> Params.dirt_singleton p
  | Dirt.Row.Empty -> Params.empty

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
  print "%t ≤ %t" (Dirt.print ty1) (Dirt.print ty2)

and print_abs_ty (ty1, drty2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print "%t → %t" (print_ty ty1) (print_dirty drty2)

module DirtConstraints = struct
  module DirtParamGraph =
    Graph.Make
      (Dirt.Param)
      (struct
        type t = DirtCoercionParam.t * Effect.Set.t

        let[@warning "-27"] print ?(safe = false) (edge, effect_set) ppf =
          let print_effect_set ppf =
            if Effect.Set.is_empty effect_set then Print.print ppf ""
            else Print.print ppf " U {%t}" (Dirt.print_effect_set effect_set)
          in
          Print.print ppf "%t%t" (DirtCoercionParam.print edge) print_effect_set
      end)

  type t = DirtParamGraph.t

  let empty = DirtParamGraph.empty

  (* Since we only add and never remove type constraints, the set of constraints
     is empty if and only iff there are no skeleton graphs in it *)
  let is_empty = DirtParamGraph.is_empty

  let add_edge d1 d2 w effs dirt_constraints : t =
    DirtParamGraph.add_edge d1 d2 (w, effs) dirt_constraints

  let fold f (dirt_constraints : t) acc =
    DirtParamGraph.fold
      (fun d1 d2 (w, effs) -> f d1 d2 w effs)
      dirt_constraints acc

  let fold_expanded f =
    fold (fun d1 d2 w effs ->
        let drt1 = Dirt.no_effect d1
        and drt2 = { Dirt.effect_set = effs; row = Dirt.Row.Param d2 } in
        f d1 d2 w effs drt1 drt2)

  let free_params (dirt_constraints : t) =
    fold
      (fun d1 d2 _w _effs params ->
        Params.union
          (Params.union (Params.dirt_singleton d1) (Params.dirt_singleton d2))
          params)
      dirt_constraints Params.empty
end

module TyConstraints = struct
  module TyParamGraph = Graph.Make (TyParam) (TyCoercionParam)

  type t = TyParamGraph.t Skeleton.Param.Map.t

  let empty = Skeleton.Param.Map.empty

  (* Since we only add and never remove type constraints, the set of constraints
     is empty if and only iff there are no skeleton graphs in it *)
  let is_empty = Skeleton.Param.Map.is_empty

  let get_ty_graph (ty_constraints : t) s =
    Skeleton.Param.Map.find_opt s ty_constraints
    |> Option.value ~default:TyParamGraph.empty

  let add_edge s t1 t2 w (ty_constraints : t) : t =
    let s_graph' =
      get_ty_graph ty_constraints s |> TyParamGraph.add_edge t1 t2 w
    in
    Skeleton.Param.Map.add s s_graph' ty_constraints

  let fold f (ty_constraints : t) acc =
    Skeleton.Param.Map.fold
      (fun s -> TyParamGraph.fold (f s))
      ty_constraints acc

  let fold_expanded f =
    fold (fun s t1 t2 w ->
        let skel = Skeleton.Param s in
        let ty1 = tyParam t1 skel and ty2 = tyParam t2 skel in
        f s t1 t2 w ty1 ty2)

  let free_params (ty_constraints : t) =
    fold
      (fun s t1 t2 _w params ->
        let skel = Skeleton.Param s in
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
    dirt_constraints : DirtConstraints.t;
  }

  let empty =
    {
      ty_constraints = TyConstraints.empty;
      dirt_constraints = DirtConstraints.empty;
    }

  let is_empty constraints =
    TyConstraints.is_empty constraints.ty_constraints
    && DirtConstraints.is_empty constraints.dirt_constraints

  let add_ty_constraint s t1 t2 w constraints =
    {
      constraints with
      ty_constraints =
        TyConstraints.add_edge s t1 t2 w constraints.ty_constraints;
    }

  let add_dirt_constraint constraints d1 d2 w effs =
    {
      constraints with
      dirt_constraints =
        DirtConstraints.add_edge d1 d2 w effs constraints.dirt_constraints;
    }

  let free_params constraints =
    let free_params_ty = TyConstraints.free_params constraints.ty_constraints
    and free_params_dirt =
      DirtConstraints.free_params constraints.dirt_constraints
    in
    Params.union free_params_ty free_params_dirt

  let print_ty_param_vertex ty_param ppf : unit =
    let vertex = TyParam.print ty_param in
    Print.print ppf "node_%t[label=\"%t\"];" vertex vertex

  let print_dirt_param_vertex ty_param ppf : unit =
    let vertex = Dirt.Param.print ty_param in
    Print.print ppf "node_%t[label=\"%t\"];" vertex vertex

  let print_edge (source, edge, sink) ppf : unit =
    Print.print ppf "node_%t -> node_%t [label=\"%t\"]" (TyParam.print source)
      (TyParam.print sink)
      (TyCoercionParam.print edge)

  let print_dirt_edge (source, (edge, effect_set), sink) ppf : unit =
    let print_effect_set ppf =
      if Effect.Set.is_empty effect_set then Print.print ppf ""
      else Print.print ppf " U {%t}" (Dirt.print_effect_set effect_set)
    in
    Print.print ppf "@[<h>node_%t -> node_%t [label=\"%t%t\"]@]"
      (Dirt.Param.print source) (Dirt.Param.print sink)
      (DirtCoercionParam.print edge)
      print_effect_set

  let print_skeleton_graph (skel_param, graph) ppf : unit =
    TyConstraints.TyParamGraph.print_dot graph
      (fun ppf ->
        Print.print ppf "cluster_%t" (Skeleton.Param.print skel_param))
      (fun ppf ->
        Print.print ppf "label=\"Skeleton param: %t\""
          (Skeleton.Param.print skel_param))
      ppf

  let print_dirt_graph graph ppf : unit =
    DirtConstraints.DirtParamGraph.print_dot graph
      (fun ppf -> Print.print ppf "cluster_dirt_graph")
      (fun ppf -> Print.print ppf "label=\"Dirt constraints\"")
      ppf

  let print_dot c ppf =
    let skeleton_graphs = Skeleton.Param.Map.bindings c.ty_constraints in

    Print.print ppf
      "digraph {\n\
       //Type params\n\
      \  subgraph cluster_skeleton {\n\n\
      \  label=\"Type constraints\";\n\
       %t\n\
       }\n\
       // Dirt\n\
      \       %t\n\
      \ }"
      (Print.sequence "\n" print_skeleton_graph skeleton_graphs)
      (print_dirt_graph c.dirt_constraints)

  let print c =
    let print_dirt_constraint w drt1 drt2 ppf =
      Print.print ppf "%t: (%t ≤ %t)"
        (DirtCoercionParam.print w)
        (Dirt.print drt1) (Dirt.print drt2)
    and print_ty_constraint s t1 t2 w ppf =
      Print.print ppf "%t: (%t ≤ %t) : %t" (TyCoercionParam.print w)
        (TyParam.print t1) (TyParam.print t2) (Skeleton.Param.print s)
    in
    []
    |> DirtConstraints.fold_expanded
         (fun _d1 _d2 w _effs drt1 drt2 printouts ->
           print_dirt_constraint w drt1 drt2 :: printouts)
         c.dirt_constraints
    |> TyConstraints.fold
         (fun s t1 t2 w printouts -> print_ty_constraint s t1 t2 w :: printouts)
         c.ty_constraints
    |> Print.printer_sequence ", "
end

let type_const c = tyBasic (Const.infer_ty c)

type ty_scheme = { params : Params.t; constraints : Constraints.t; ty : ty }

let monotype ty = { params = Params.empty; constraints = Constraints.empty; ty }

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
      && List.length tys1 = List.length tys2
      && List.for_all2 equal_ty tys1 tys2
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

let fresh_ty_with_skel skel =
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
  | Skeleton.Apply (ty_name, sks) ->
      let tvars = List.map fresh_ty_with_skel sks in
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
  | Skeleton.Apply (t, []) -> print "%t" (TyName.print t)
  | Skeleton.Apply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_pretty_skel ~max_level:1 free params s)
        (TyName.print t)
  | Skeleton.Apply (t, skels) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " (print_pretty_skel free params) skels)
        (TyName.print t)
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
