open Utils
open Language
open Type
open TyCoercion

(*
Configuration for partial optimizations   
*)

let simplify_type_params = true
let simplify_type_params_full = false
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

let check_polarity_same _fold _fn (_polarities : FreeParams.params) _params =
  (* let _ =
       fold
         (fun param acc ->
           match acc with
           | None -> acc
           | Some p -> (
               let polarity = fn param polarities in
               match (p, polarity) with
               | FreeParams.Negative, Some FreeParams.Positive -> assert false
               | FreeParams.Positive, Some Negative -> assert false
               | p, _ -> Some p))
         params None
     in *)
  ()

let check_polarity_same_ty a =
  check_polarity_same TyParam.Set.fold FreeParams.get_type_polarity a

(* TODO: Find out why this can't be generalized *)
let check_polarity_same_dirt s =
  check_polarity_same Dirt.Param.Set.fold FreeParams.get_dirt_polarity s

(** Add constraints for all cycles in type constraints *)
let contract_type_cycles ty_constraints unresolved =
  let contract_edge skeleton_param ty_param1 ty_param2 unresolved =
    UnresolvedConstraints.add_ty_equality
      ( { term = TyParam ty_param1; ty = Skeleton.Param skeleton_param },
        { term = TyParam ty_param2; ty = Skeleton.Param skeleton_param } )
      unresolved
  in

  let contract_component skeleton_param component unresolved =
    let representative = TyParam.Set.choose component in
    TyParam.Set.fold
      (contract_edge skeleton_param representative)
      component unresolved
  in

  let contract_skeleton skeleton_param skeleton_graph unresolved =
    let components =
      Constraints.TyConstraints.TyParamGraph.scc skeleton_graph
    in
    List.fold_right (contract_component skeleton_param) components unresolved
  in

  Skeleton.Param.Map.fold contract_skeleton ty_constraints unresolved

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

let graph_to_constraints skel_param graph =
  let open Language.Constraints in
  let module BaseSym = TyParam in
  let module EdgeSym = TyCoercionParam in
  let module G = TyConstraints.TyParamGraph in
  let g = G.fold (add_ty_constraint skel_param) graph empty in
  g

type graph = Language.Constraints.TyConstraints.TyParamGraph.t

type simple_node_constraction_state = {
  base_graph : graph;
  reversed_graph : graph;
  free_parameters : Type.FreeParams.params;
  collected_constraints : UnresolvedConstraints.t;
}

(* Joins simple type coercions to a reflexive coercion *)
let remove_type_bridges ({ Language.Constraints.ty_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let open Language.Constraints in
  let join_skeleton_component skel add_constraint graph new_constr =
    Print.debug "Joining simple nodes in %t" (Skeleton.Param.print skel);
    Print.debug "Graph: %t"
      (graph |> graph_to_constraints skel |> Constraints.print_dot);
    let module BaseSym = TyParam in
    let module EdgeSym = TyCoercionParam in
    let module G = TyConstraints.TyParamGraph in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in
    let process_part_general
        ({ source_node; sink_node; graph_direction; edge } :
          (BaseSym.t, EdgeSym.t) reduction_candidate)
        ({ base_graph; reversed_graph; free_parameters; _ } as state) =
      (*
     Imagine a local part of graph of the form:
     (source)-[edge]->(sink)
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
      (* We can't contract edges between (+)->(-) nodes *)
      (* We need to take into the account possible reversal *)
      let can_collapse =
        match graph_direction with
        | Direct ->
            FreeParams.TypeParams.can_be_negative source_node
              free_parameters.type_params
            || G.get_edges sink_node reversed_graph |> G.Edges.cardinal = 1
               && FreeParams.TypeParams.can_be_positive sink_node
                    free_parameters.type_params
        | Reverse ->
            FreeParams.TypeParams.can_be_positive source_node
              free_parameters.type_params
            || G.get_edges sink_node base_graph |> G.Edges.cardinal = 1
               && FreeParams.TypeParams.can_be_negative sink_node
                    free_parameters.type_params
        (* match graph_direction with
           | Direct -> G.get_edges source_node base_graph |> G.Edges.cardinal = 1
           | Reverse ->
               G.get_edges sink_node reversed_graph |> G.Edges.cardinal = 1 *)
        (* FreeParams.TypeParams.can_be_positive sink_node' params.type_params *)
      in
      Print.debug "Can collapse: %b" can_collapse;
      Print.debug "Graph: %t"
        (Language.Constraints.print_dot (graph_to_constraints skel base_graph));
      (* Update according to the direction *)
      let base_graph, reversed_graph = reversal (base_graph, reversed_graph) in
      (* Sanity check for the constraint we are contracting *)
      let connecting_edge = G.get_edges source_node base_graph in
      assert (G.Edges.cardinal connecting_edge = 1);
      let possible_sink, _edge' = G.Vertex.Map.choose connecting_edge in
      assert (BaseSym.compare possible_sink sink_node = 0);
      assert (possible_sink = sink_node);

      let previous = G.get_edges source_node reversed_graph in

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
                free_parameters with
                type_params =
                  Type.FreeParams.TypeParams.combine_polarity sink_node
                    source_node state.free_parameters.type_params;
              };
          },
          can_collapse )
      else (state, can_collapse)
    in
    let indeg, outdeg = G.degrees graph in
    (* Sanity check *)
    let assert_degrees grph line =
      BaseSym.Map.iter
        (fun p n ->
          let sz = G.get_edges p grph |> G.Edges.cardinal in
          assert (n = sz))
        line
    in
    assert_degrees inverse_graph indeg;
    assert_degrees graph outdeg;
    let lst = indeg |> BaseSym.Map.bindings in
    Print.debug "Line: bindings indeg: %t"
      (Print.sequence "," (fun (s, _) -> BaseSym.print s) lst);
    Print.debug "Line: bindings outdeg: %t"
      (Print.sequence ","
         (fun (s, _) -> BaseSym.print s)
         (outdeg |> BaseSym.Map.bindings));

    let rec process (graph, reverse_graph) params visited
        (constr : UnresolvedConstraints.t) =
      (* Choose next one *)

      (* Select the next one that can be removed *)
      let get_ones direction core_graph (source_node, n) =
        Print.debug "Direction: %s" (string_of_mode direction);
        Print.debug "%t" (BaseSym.print source_node);
        assert (n <> 0);
        if n = 1 then
          let sink_node, edge =
            G.get_edges source_node core_graph |> BaseSym.Map.bindings
            |> function
            | [ ((n, e) : BaseSym.t * EdgeSym.t) ] -> (n, e)
            | [] -> assert false
            | _ -> assert false
          in
          Some { graph_direction = direction; sink_node; edge; source_node }
        else None
      in
      let filter direction core_graph line =
        line |> BaseSym.Map.bindings
        |> List.filter_map (get_ones direction core_graph)
      in
      let lst = indeg |> BaseSym.Map.bindings in
      Print.debug "Line: bindings indeg: %t"
        (Print.sequence "," (fun (s, _) -> BaseSym.print s) lst);
      Print.debug "Line: bindings outdeg: %t"
        (Print.sequence ","
           (fun (s, _) -> BaseSym.print s)
           (outdeg |> BaseSym.Map.bindings));
      let indeg_line = filter Reverse inverse_graph indeg in
      let outdeg_line = filter Direct graph outdeg in
      let candidates =
        indeg_line @ outdeg_line
        |> List.filter (fun c -> not (EdgeSym.Set.mem c.edge visited))
      in
      match candidates with
      | top :: _ ->
          Print.debug "Trying: %t %s" (EdgeSym.print top.edge)
            (string_of_mode top.graph_direction);
          Print.debug "Selecting: %t %s" (EdgeSym.print top.edge)
            (string_of_mode top.graph_direction);
          let processing_state =
            {
              base_graph = graph;
              reversed_graph = reverse_graph;
              free_parameters = params;
              collected_constraints = constr;
            }
          in
          let state, collapsed = process_part_general top processing_state in
          let visited =
            if collapsed then EdgeSym.Set.add top.edge visited else visited
          in
          process
            (state.base_graph, state.reversed_graph)
            state.free_parameters visited state.collected_constraints
      | _ -> constr
    in

    process (graph, inverse_graph) params EdgeSym.Set.empty new_constr
  in
  let new_constr =
    Skeleton.Param.Map.fold
      (fun skel graph acc ->
        let pack ty_param =
          { term = TyParam ty_param; ty = Skeleton.Param skel }
        in
        let add_constraint source target constraints =
          UnresolvedConstraints.add_ty_equality
            (pack source, pack target)
            constraints
        in
        join_skeleton_component skel add_constraint graph acc)
      ty_constraints
      (UnresolvedConstraints.from_resolved resolved)
  in
  new_constr

let add_constraint p1 p2 =
  UnresolvedConstraints.add_dirt_equality (Dirt.no_effect p1, Dirt.no_effect p2)

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
    let indeg, outdeg = G.degrees graph in
    let lst = indeg |> BaseSym.Map.bindings in
    Print.debug "Line: bindings indeg: %t"
      (Print.sequence "," (fun (s, _) -> BaseSym.print s) lst);
    Print.debug "Line: bindings outdeg: %t"
      (Print.sequence ","
         (fun (s, _) -> BaseSym.print s)
         (outdeg |> BaseSym.Map.bindings));

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
      let can_collapse =
        let source_node', sink_node' = reversal (source_node, sink_node) in
        let polarity_condition =
          FreeParams.DirtParams.can_be_positive sink_node'
            state.free_parameters.dirt_params
          || FreeParams.DirtParams.can_be_negative source_node'
               state.free_parameters.dirt_params
        in
        let is_self_loop = BaseSym.compare source_node' sink_node' = 0 in
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
    let rec process (graph, reverse_graph) params visited touched
        (constr : UnresolvedConstraints.t) =
      (* Choose next one *)
      let get_ones direction core_graph (source_node, n) =
        assert (n <> 0);
        if n = 1 then
          let sink_node, edge =
            G.get_edges source_node core_graph |> BaseSym.Map.bindings
            |> function
            | [ ((n, (e, _)) : BaseSym.t * (EdgeSym.t * D.t)) ] -> (n, e)
            | [] -> assert false
            | _ -> assert false
          in
          Some { graph_direction = direction; sink_node; edge; source_node }
        else None
      in
      let filter direction core_graph line =
        line |> BaseSym.Map.bindings
        |> List.filter_map (get_ones direction core_graph)
      in
      let lst = indeg |> BaseSym.Map.bindings in
      Print.debug "Line: bindings indeg: %t"
        (Print.sequence "," (fun (s, _) -> BaseSym.print s) lst);
      Print.debug "Line: bindings outdeg: %t"
        (Print.sequence ","
           (fun (s, _) -> BaseSym.print s)
           (outdeg |> BaseSym.Map.bindings));
      let indeg_line = filter Reverse inverse_graph indeg in
      let outdeg_line = filter Direct graph outdeg in
      let candidates =
        indeg_line @ outdeg_line
        |> List.filter (fun c -> not (EdgeSym.Set.mem c.edge visited))
      in
      match candidates with
      | m :: _ ->
          let visited = EdgeSym.Set.add m.edge visited in
          let processing_state =
            {
              base_graph = graph;
              reversed_graph = reverse_graph;
              free_parameters = params;
              collected_constraints = constr;
            }
          in
          let state, touched_node = process_part_general m processing_state in
          let touched =
            match touched_node with
            | Some node -> node :: touched
            | None -> touched
          in
          process
            (state.base_graph, state.reversed_graph)
            state.free_parameters visited touched state.collected_constraints
      | [] -> (constr, touched)
    in
    process (graph, inverse_graph) params EdgeSym.Set.empty [] new_constr
  in
  join_dirt_component dirt_constraints
    (UnresolvedConstraints.from_resolved resolved)

let simplify_type_constraints ~loc type_definitions constraints get_params =
  let unresolved = UnresolvedConstraints.from_resolved constraints in
  let cycle_constraints =
    contract_type_cycles constraints.ty_constraints unresolved
  in
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot
       ~param_polarity:(get_params constraints.substitution)
       constraints);
  (* We don't really need the free parameters yet, as we do another unification pass *)
  let constraints = Unification.unify ~loc type_definitions cycle_constraints in
  let constraints = Constraints.remove_loops constraints in
  let constraints =
    if simplify_type_params_full then
      let simple_one_constraints =
        remove_type_bridges constraints (get_params constraints.substitution)
      in
      let simple_one_constraints' =
        Unification.unify ~loc type_definitions simple_one_constraints
      in
      simple_one_constraints'
    else constraints
  in
  constraints

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
