open Utils
open Language
open Type
open TyCoercion

(*
Configuration for partial optimizations   
*)

let simplify_type_params = true
let simplify_dirt_params = true
let simplify_dirt_params_full = false

type contraction_mode = Direct | Reverse

let string_of_mode = function Direct -> "Direct" | Reverse -> "Reverse"

type ('a, 'b) reduction_candidate = {
  source_node : 'a;
  sink_node : 'a;
  edge : 'b;
  graph_direction : contraction_mode;
}

let print_reduction_candidate pn pe
    { source_node; sink_node; edge; graph_direction } ppf =
  Format.fprintf ppf "{ %t-[%t]->%t; %s }" (pn source_node) (pe edge)
    (pn sink_node)
    (string_of_mode graph_direction)

(** Add constraints for all suitable cycles in dirt constraints *)
let contract_dirt_cycles (dirt_constraints : Constraints.DirtConstraints.t)
    unresolved =
  let contract_edge dirt_param1 dirt_param2 unresolved =
    UnresolvedConstraints.add_dirt_equality
      (Dirt.no_effect dirt_param1, Dirt.no_effect dirt_param2)
      unresolved
  in

  (* We collapse only the components where all internal dirt coercions
     are of the form d1 <= d2, so without additional effects on
     the right-hand side *)
  let is_collapsible component =
    let check_param param =
      let neighbours =
        Constraints.DirtConstraints.DirtParamGraph.get_edges param
          dirt_constraints
      in
      let trivial_neighbour neighbour (_w, effs) =
        (not (Dirt.Param.Set.mem neighbour component))
        || Effect.Set.is_empty effs
      in
      Dirt.Param.Map.for_all trivial_neighbour neighbours
    in
    Dirt.Param.Set.for_all check_param component
  in

  let contract_component component unresolved =
    let representative = Dirt.Param.Set.choose component in
    Dirt.Param.Set.fold (contract_edge representative) component unresolved
  in

  let components =
    Constraints.DirtConstraints.DirtParamGraph.scc dirt_constraints
    |> List.filter is_collapsible
  in
  List.fold_right contract_component components unresolved

(* Merge a type parameter [gamma] into another type parameter [rho] of the
   same skeleton. Writing [x ~> y] when the constraints give a path, possibly
   empty, from [x] to [y], the merge [gamma |-> rho] is complete if:
   - (L) [pi ~> rho] for every lower bound [pi <= gamma],
   - (U) [rho ~> beta] for every upper bound [gamma <= beta],
   - (P+) [rho ~> gamma] if [gamma] is positive,
   - (P-) [gamma ~> rho] if [gamma] is negative.
   The constraints still hold after the merge because of (L) and (U), and the
   simplified type is a subtype of the original because of (P+) and (P-). The
   rule covers both kinds of bridges: if [alpha <= alpha'] is the only lower
   bound of a non-negative [alpha'], take [gamma = alpha'] and [rho = alpha],
   and dually for the only upper bound of a non-positive parameter. It also
   merges a neutral parameter with any parameter between its bounds.

   It also contracts cycles: if [gamma] and [rho] lie on a common cycle, all
   four conditions hold. A bipolar [gamma] can satisfy both (P+) and (P-) only
   on a cycle, and then its instances are coercible both ways, which is the
   same assumption the paper makes for contracting cycles. Each merge removes
   a node, so the loop ends. *)
let merge_type_params ({ Language.Constraints.ty_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let module G = Language.Constraints.TyConstraints.TyParamGraph in
  let module P = FreeParams.TypeParams in
  let merge gamma rho graph =
    let rename v = if TyParam.compare v gamma = 0 then rho else v in
    G.fold
      (fun v1 v2 edge acc ->
        let v1 = rename v1 and v2 = rename v2 in
        if TyParam.compare v1 v2 = 0 then acc
        else G.add_edge ~allow_duplicate:true v1 v2 edge acc)
      graph G.empty
  in
  let can_merge graph reversed reach type_params gamma rho =
    let reaches x y = TyParam.Set.mem y (TyParam.Map.find x reach) in
    TyParam.compare gamma rho <> 0
    && (P.can_be_negative gamma type_params || reaches rho gamma)
    && (P.can_be_positive gamma type_params || reaches gamma rho)
    && TyParam.Map.for_all
         (fun pi _ -> reaches pi rho)
         (G.get_edges gamma reversed)
    && TyParam.Map.for_all
         (fun beta _ -> reaches rho beta)
         (G.get_edges gamma graph)
  in
  let rec merge_all skel graph type_params constraints =
    let vertices = G.vertices graph |> TyParam.Set.elements in
    let reversed = G.reverse graph in
    let reach =
      List.fold_left
        (fun reach v -> TyParam.Map.add v (G.traverse v graph) reach)
        TyParam.Map.empty vertices
    in
    let candidate =
      List.find_map
        (fun gamma ->
          List.find_opt
            (can_merge graph reversed reach type_params gamma)
            vertices
          |> Option.map (fun rho -> (gamma, rho)))
        vertices
    in
    match candidate with
    | None -> constraints
    | Some (gamma, rho) ->
        Print.debug "Merging %t into %t" (TyParam.print gamma)
          (TyParam.print rho);
        let pack ty_param =
          { term = TyParam ty_param; ty = Skeleton.Param skel }
        in
        merge_all skel (merge gamma rho graph)
          (P.combine_polarity rho gamma type_params)
          (UnresolvedConstraints.add_ty_equality
             (pack gamma, pack rho)
             constraints)
  in
  Skeleton.Param.Map.fold
    (fun skel graph constraints ->
      merge_all skel graph params.type_params constraints)
    ty_constraints
    (UnresolvedConstraints.from_resolved resolved)

let add_empty_constraint p1 =
  UnresolvedConstraints.add_dirt_equality (Dirt.no_effect p1, Dirt.empty)

let contract_source_dirt_nodes
    ({ Language.Constraints.dirt_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let open Language.Constraints in
  let module BaseSym = Dirt.Param in
  let module G = DirtConstraints.DirtParamGraph in
  let components, quotient_graph, representatives =
    Language.Constraints.DirtConstraints.DirtParamGraph.scc_tarjan
      dirt_constraints
  in
  List.iter
    (fun dl ->
      Print.debug "Component:";
      Print.debug "%d %t\n reps:%t" (List.length dl)
        (Print.sequence "," BaseSym.print dl)
        (Print.sequence "," BaseSym.print
           (List.map (fun x -> BaseSym.Map.find x representatives) dl)))
    components;
  Print.debug "Representatives: %t"
    (BaseSym.Map.print BaseSym.print representatives);
  let indegs, _ = G.degrees ~ignore_loops:true quotient_graph in
  let indegs =
    let vs = G.vertices quotient_graph in
    BaseSym.Set.fold
      (fun v ->
        BaseSym.Map.update v (function None -> Some 0 | Some deg -> Some deg))
      vs indegs
  in
  let can_contract_component component =
    List.for_all
      (fun node ->
        Type.FreeParams.DirtParams.can_be_positive node params.dirt_params)
      component
  in
  let _, new_constraints =
    List.fold_left
      (fun (indegs, constraints) component ->
        Print.debug "Indeg: %t"
          (BaseSym.Map.print (fun n ppf -> Print.print ppf "%d" n) indegs);
        let rep =
          match component with
          | [] -> assert false
          | x :: _ -> BaseSym.Map.find x representatives
        in
        if can_contract_component component && BaseSym.Map.find rep indegs = 0
        then (
          Print.debug "Contracting component of %t: %t" (BaseSym.print rep)
            (Print.sequence "," BaseSym.print component);
          let outgoing = BaseSym.Map.find rep quotient_graph in
          let indegs =
            indegs
            |> BaseSym.Map.fold
                 (fun sink _ indegs ->
                   indegs
                   |> BaseSym.Map.update sink (function
                     | Some x -> Some (x - 1)
                     | None -> assert false))
                 outgoing
          in
          (indegs, constraints |> List.fold_right add_empty_constraint component))
        else (indegs, constraints))
      (indegs, UnresolvedConstraints.from_resolved resolved)
      components
  in
  new_constraints

let contract_unreachable_dirt_nodes { Language.Constraints.dirt_constraints; _ }
    (params : FreeParams.params) =
  let open Language.Constraints in
  let module BaseSym = Dirt.Param in
  let module G = DirtConstraints.DirtParamGraph in
  let sources =
    BaseSym.Set.union params.dirt_params.positive params.dirt_params.negative
  in

  let vertices = G.vertices dirt_constraints in

  let rec dfs node visited =
    if BaseSym.Set.mem node visited then visited
    else
      let visited = BaseSym.Set.add node visited in
      let edges = G.get_edges node dirt_constraints in
      G.Edges.fold
        (fun sink _ acc ->
          if BaseSym.Set.mem sink visited then acc else dfs sink acc)
        edges visited
  in
  let visited = BaseSym.Set.fold dfs sources BaseSym.Set.empty in

  let constraints =
    BaseSym.Set.fold add_empty_constraint
      (BaseSym.Set.diff vertices visited)
      UnresolvedConstraints.empty
  in
  constraints

type dirt_graph = Language.Constraints.DirtConstraints.DirtParamGraph.t

type simple_dirt_node_constraction_state = {
  base_graph : dirt_graph;
  reversed_graph : dirt_graph;
  free_parameters : Type.FreeParams.params;
  collected_constraints : UnresolvedConstraints.t;
}

let remove_dirt_bridges
    ({ Language.Constraints.dirt_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let open Language.Constraints in
  let add_constraint source target constraints =
    UnresolvedConstraints.add_dirt_equality
      (Dirt.no_effect source, Dirt.no_effect target)
      constraints
  in
  let join_dirt_component
      (graph :
        (DirtCoercionParam.t * Label.Set.t) Dirt.Param.Map.t Dirt.Param.Map.t)
      new_constr =
    let module BaseSym = Dirt.Param in
    let module EdgeSym = DirtCoercionParam in
    let module D = Label.Set in
    let module G = DirtConstraints.DirtParamGraph in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in

    let process_part_general
        ({ source_node; sink_node; graph_direction; edge } :
          (BaseSym.t, EdgeSym.t) reduction_candidate)
        ({ base_graph; reversed_graph; _ } as state :
          simple_dirt_node_constraction_state) =
      (*
     Imagine a local part of graph of the form:
     (source)-[edge U dirtSet]->(sink)
     where the the source has an outdegree of 1.
     We exiplicitly make the edge reflexive and remove the source node (as it needs fewer rewirings)
     In essence, this methods contracts reduction candidate under the assumption, 
     that is has an outdegree of 1 in base_graph. 

     Every node with an indegree 1 is also a node with an outdegree of 1 in the reversed graph.
     This is handeled by the graph_direction parameter.
  *)
      Print.debug "Removing %t-[%t]->%t %s"
        (BaseSym.print source_node)
        (EdgeSym.print edge) (BaseSym.print sink_node)
        (string_of_mode graph_direction);

      let reversal =
        match graph_direction with
        | Direct -> fun (x, y) -> (x, y)
        | Reverse -> fun (x, y) -> (y, x)
      in
      (* Update according to the direction *)
      let base_graph, reversed_graph = reversal (base_graph, reversed_graph) in

      (* Sanity check for the constraint we are contracting *)
      let connecting_edge = G.get_edges source_node base_graph in
      assert (G.Edges.cardinal connecting_edge = 1);
      let possible_sink, (_, edge_dirt) = G.Vertex.Map.choose connecting_edge in
      assert (BaseSym.compare possible_sink sink_node = 0);
      assert (possible_sink = sink_node);

      let previous = G.get_edges source_node reversed_graph in

      (* We can't contract edges between (+)->(-) nodes *)
      (* We need to take into the account possible reversal *)
      (* As for types: the source, whose only bound is the sink, may take the
         value of the sink if the polarity of the source allows it. The sink
         may take the value of the source only if the source is the only
         bound of the sink, and the polarity of the sink allows it. *)
      let can_collapse =
        let params = state.free_parameters.dirt_params in
        let sink_has_one_edge =
          G.get_edges sink_node reversed_graph |> G.Edges.cardinal = 1
        in
        let polarity_condition =
          match graph_direction with
          | Direct ->
              FreeParams.DirtParams.can_be_negative source_node params
              || sink_has_one_edge
                 && FreeParams.DirtParams.can_be_positive sink_node params
          | Reverse ->
              FreeParams.DirtParams.can_be_positive source_node params
              || sink_has_one_edge
                 && FreeParams.DirtParams.can_be_negative sink_node params
        in
        let is_self_loop = BaseSym.compare source_node sink_node = 0 in
        polarity_condition && Effect.Set.is_empty edge_dirt && not is_self_loop
      in

      if can_collapse then
        (* We need to rewire previous from source to sink *)
        let base_graph =
          base_graph
          |> G.remove_edge source_node sink_node (* remove this edge *)
          |> G.Edges.fold (* remove edges incoming to source *)
               (fun prev e acc ->
                 acc
                 |> G.remove_edge prev source_node
                 |> G.add_edge (* Triangles can produce duplicate edges *)
                      ~allow_duplicate:true prev sink_node e)
               previous
          |> G.remove_vertex_unsafe source_node
        in
        let reversed_graph =
          reversed_graph
          |> G.remove_edge sink_node source_node
          |> G.Edges.fold (* rewire other edges *)
               (fun prev e acc ->
                 acc
                 |> G.remove_edge source_node prev
                 |> G.add_edge ~allow_duplicate:true sink_node prev e)
               previous
          |> G.remove_vertex_unsafe source_node
        in
        let base_graph, reversed_graph =
          reversal (base_graph, reversed_graph)
        in
        ( {
            base_graph;
            reversed_graph;
            collected_constraints =
              add_constraint sink_node source_node state.collected_constraints;
            free_parameters =
              {
                state.free_parameters with
                dirt_params =
                  Type.FreeParams.DirtParams.combine_polarity sink_node
                    source_node state.free_parameters.dirt_params;
              };
          },
          Some source_node )
      else (state, None)
    in
    (* Nodes with exactly one outgoing edge in [core_graph], recomputed from
       the current graphs at each step, because every contraction changes the
       degrees of the neighbouring nodes. *)
    let candidates direction core_graph =
      BaseSym.Map.bindings core_graph
      |> List.filter_map (fun (source_node, edges) ->
          match G.Edges.bindings edges with
          | [ (sink_node, (edge, _)) ] ->
              Some { graph_direction = direction; sink_node; edge; source_node }
          | _ -> None)
    in
    (* Contract the first candidate that can be contracted, and repeat until
       no candidate can be. Each contraction removes a node, so this ends. *)
    let rec process state touched =
      let try_candidate candidate =
        match process_part_general candidate state with
        | state, Some node -> Some (state, node)
        | _, None -> None
      in
      candidates Reverse state.reversed_graph
      @ candidates Direct state.base_graph
      |> List.find_map try_candidate
      |> function
      | Some (state, node) -> process state (node :: touched)
      | None -> (state.collected_constraints, touched)
    in
    process
      {
        base_graph = graph;
        reversed_graph = inverse_graph;
        free_parameters = params;
        collected_constraints = new_constr;
      }
      []
  in
  join_dirt_component dirt_constraints
    (UnresolvedConstraints.from_resolved resolved)

let simplify_type_constraints ~loc type_definitions constraints get_params =
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot
       ~param_polarity:(get_params constraints.Constraints.substitution)
       constraints);
  let constraints = Constraints.remove_loops constraints in
  merge_type_params constraints (get_params constraints.substitution)
  |> Unification.unify ~loc type_definitions

let simplify_dirt_contraints ~loc type_definitions constraints get_params =
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot
       ~param_polarity:(get_params constraints.Constraints.substitution)
       constraints);
  let unresolved = UnresolvedConstraints.from_resolved constraints in
  let new_constraints =
    contract_dirt_cycles constraints.dirt_constraints unresolved
  in
  let constraints = Unification.unify ~loc type_definitions new_constraints in
  let constraints =
    if simplify_dirt_params_full then
      let new_constraints =
        contract_source_dirt_nodes constraints
          (get_params constraints.substitution)
      in
      Unification.unify ~loc type_definitions new_constraints
    else constraints
  in
  Print.debug "Full constraints after source contraction: %t"
    (Language.Constraints.print_dot
       ~param_polarity:(get_params constraints.substitution)
       constraints);
  let rec runner level cons_state =
    Print.debug "Full constraints in runner %d: %t" level
      (Language.Constraints.print_dot
         ~param_polarity:(get_params constraints.substitution)
         constraints);
    let new_constraints, touched =
      remove_dirt_bridges cons_state (get_params cons_state.substitution)
    in
    let cons_state = Unification.unify ~loc type_definitions new_constraints in
    let cons_state = Constraints.remove_loops cons_state in
    Print.debug "Touched: %d %t" (List.length touched)
      (Print.sequence "," Dirt.Param.print touched);
    if List.length touched > 0 then runner (level + 1) cons_state
    else cons_state
  in
  let constraints =
    if simplify_dirt_params_full then runner 0 constraints else constraints
  in

  (* Optimize possible empty dirts  *)
  let new_constraints =
    contract_source_dirt_nodes constraints (get_params constraints.substitution)
  in
  let constraints = Unification.unify ~loc type_definitions new_constraints in
  (* Some parameters are present in the type, but not in constrains *)
  let present =
    Language.Constraints.DirtConstraints.DirtParamGraph.vertices
      constraints.dirt_constraints
  in
  let params = (get_params constraints.substitution).dirt_params in
  let new_constraints =
    Dirt.Param.Set.fold
      (fun p acc ->
        if not (Dirt.Param.Set.mem p present) then
          acc
          |> UnresolvedConstraints.add_dirt_equality
               (Dirt.no_effect p, Dirt.empty)
        else acc)
      (Dirt.Param.Set.diff params.positive params.negative)
      (UnresolvedConstraints.from_resolved constraints)
  in
  let constraints = Unification.unify ~loc type_definitions new_constraints in
  constraints

let simplify_constraints ~loc type_definitions constraints get_params =
  let constraints =
    if simplify_type_params then
      simplify_type_constraints ~loc type_definitions constraints get_params
    else constraints
  in
  let constraints =
    if simplify_dirt_params then
      simplify_dirt_contraints ~loc type_definitions constraints get_params
    else constraints
  in
  constraints

let simplify_computation ~loc type_definitions constraints typ =
  simplify_constraints ~loc type_definitions constraints (fun subs ->
      let polarity =
        calculate_polarity_dirty_ty (Substitution.apply_sub_dirty_ty subs typ)
      in
      polarity)

let simplify_expression ~loc type_definitions constraints typ =
  simplify_constraints ~loc type_definitions constraints (fun subs ->
      let polarity =
        calculate_polarity_type (Substitution.apply_sub_ty subs typ)
      in
      polarity)

let simplify_top_let_rec ~loc type_definitions constraints tys =
  simplify_constraints ~loc type_definitions constraints (fun subs ->
      let tys = List.map (Substitution.apply_sub_abs_ty subs) tys in
      let params =
        List.fold
          (fun acc ty -> FreeParams.union (calculate_polarity_abs_ty ty) acc)
          FreeParams.empty tys
      in
      params)
