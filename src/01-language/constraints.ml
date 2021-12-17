open Utils
open Type

module DirtConstraints = struct
  module DirtParamGraph =
    Graph.Make
      (Dirt.Param)
      (struct
        type t = DirtCoercionParam.t * Effect.Set.t

        let[@warning "-27"] print ?(safe = false) (edge, effect_set) ppf =
          let print_effect_set ppf =
            if Effect.Set.is_empty effect_set then Print.print ppf ""
            else Print.print ppf " U {%t}" (Effect.Set.print effect_set)
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

  let get_ty_graph s (ty_constraints : t) =
    Skeleton.Param.Map.find_opt s ty_constraints
    |> Option.value ~default:TyParamGraph.empty

  let add_edge s t1 t2 w (ty_constraints : t) : t =
    let s_graph' =
      ty_constraints |> get_ty_graph s |> TyParamGraph.add_edge t1 t2 w
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
    ty_constraints = TyConstraints.add_edge s t1 t2 w constraints.ty_constraints;
  }

let add_dirt_constraint d1 d2 w effs constraints =
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
    else Print.print ppf " U {%t}" (Effect.Set.print effect_set)
  in
  Print.print ppf "@[<h>node_%t -> node_%t [label=\"%t%t\"]@]"
    (Dirt.Param.print source) (Dirt.Param.print sink)
    (DirtCoercionParam.print edge)
    print_effect_set

let print_skeleton_graph (skel_param, graph) ppf : unit =
  TyConstraints.TyParamGraph.print_dot graph
    (fun ppf -> Print.print ppf "cluster_%t" (Skeleton.Param.print skel_param))
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
     labelloc=b\n\
     rankdir=BT\n\
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
