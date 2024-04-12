open Utils
open Language
open Type
open Coercion

(*
Configuration for partial optimizations   
*)

let simplify_type_params = true
let simplify_type_params_full = false
let simplify_dirt_params = true
let simplify_dirt_params_full = false

type counter = {
  type_coercions : float TyCoercionParam.Map.t;
  dirt_coercions : float DirtCoercionParam.Map.t;
}

type contraction_mode = Direct | Reverse

let string_of_mode = function Direct -> "Direct" | Reverse -> "Reverse"
let reverse_mode = function Direct -> Reverse | Reverse -> Direct

let compare_mode d1 d2 =
  match (d1, d2) with
  | Direct, Direct | Reverse, Reverse -> 0
  | Direct, Reverse -> -1
  | Reverse, Direct -> 1

type dirt_reduction_candidates = {
  incoming : Dirt.Param.Set.t;
  outgoing : Dirt.Param.Set.t;
  sources : Dirt.Param.Set.t;
  sinks : Dirt.Param.Set.t;
}

let empty_candidates =
  {
    incoming = Dirt.Param.Set.empty;
    outgoing = Dirt.Param.Set.empty;
    sources = Dirt.Param.Set.empty;
    sinks = Dirt.Param.Set.empty;
  }

type dirt_contraction_state = {
  graph : Constraints.DirtConstraints.DirtParamGraph.t;
  inverse_graph : Constraints.DirtConstraints.DirtParamGraph.t;
  visited : Dirt.Param.Set.t;
  unavailable : Dirt.Param.Set.t;
  contraction_touched : Dirt.Param.Set.t;
  candidates : dirt_reduction_candidates;
  changed : Dirt.Param.Set.t;
}

let invert_candidates dirt_reduction_candidates =
  {
    incoming = dirt_reduction_candidates.outgoing;
    outgoing = dirt_reduction_candidates.incoming;
    sources = dirt_reduction_candidates.sinks;
    sinks = dirt_reduction_candidates.sources;
  }

let union c1 c2 =
  {
    incoming = Dirt.Param.Set.union c1.incoming c2.incoming;
    outgoing = Dirt.Param.Set.union c1.outgoing c2.outgoing;
    sources = Dirt.Param.Set.union c1.sources c2.sources;
    sinks = Dirt.Param.Set.union c1.sinks c2.sinks;
  }

let remove_candidates visited unavailable contraction_touched candidates =
  {
    incoming =
      Dirt.Param.Set.diff
        (Dirt.Param.Set.diff candidates.incoming visited)
        contraction_touched;
    outgoing =
      Dirt.Param.Set.diff
        (Dirt.Param.Set.diff candidates.outgoing visited)
        contraction_touched;
    sources =
      Dirt.Param.Set.diff
        (Dirt.Param.Set.diff candidates.sources visited)
        unavailable;
    sinks =
      Dirt.Param.Set.diff
        (Dirt.Param.Set.diff candidates.sinks visited)
        unavailable;
  }

let invert ({ graph; inverse_graph; candidates; _ } as data) =
  {
    data with
    graph = inverse_graph;
    inverse_graph = graph;
    candidates = invert_candidates candidates;
  }

let invert_with_dir data = function Direct -> data | Reverse -> invert data

let source_sink_candidate { candidates = { sources; sinks; _ }; _ } =
  match Dirt.Param.Set.choose_opt sources with
  | Some s -> Some (s, Reverse)
  | None -> (
      match Dirt.Param.Set.choose_opt sinks with
      | Some s -> Some (s, Direct)
      | None -> None)

let incoming_outgoing_candidate { candidates = { incoming; outgoing; _ }; _ } =
  match Dirt.Param.Set.choose_opt outgoing with
  | Some s -> Some (s, Reverse)
  | None -> (
      match Dirt.Param.Set.choose_opt incoming with
      | Some s -> Some (s, Direct)
      | None -> None)

let recalculate_dirt_reduction_candidates
    ({
       graph;
       inverse_graph;
       visited;
       candidates;
       unavailable;
       contraction_touched;
       _;
     } as data) new_candidates =
  let module BaseSym = Dirt.Param in
  let module G = Constraints.DirtConstraints.DirtParamGraph in
  (* Calculate sinks and sources *)
  {
    data with
    candidates =
      List.fold_right
        (fun candidate candidates ->
          let outdeg = graph |> G.get_edges candidate |> BaseSym.Map.cardinal in
          let indeg =
            inverse_graph |> G.get_edges candidate |> BaseSym.Map.cardinal
          in
          let add s = BaseSym.Set.add candidate s in
          let remove s = BaseSym.Set.remove candidate s in
          {
            incoming =
              (if outdeg = 1 then add candidates.incoming
               else remove candidates.incoming);
            outgoing =
              (if indeg = 1 then add candidates.outgoing
               else remove candidates.outgoing);
            sources =
              (if indeg = 0 then add candidates.sources
               else remove candidates.sources);
            sinks =
              (if outdeg = 0 then add candidates.sinks
               else remove candidates.sinks);
          })
        new_candidates candidates
      |> remove_candidates visited unavailable contraction_touched;
  }

let empty =
  {
    type_coercions = TyCoercionParam.Map.empty;
    dirt_coercions = DirtCoercionParam.Map.empty;
  }

module EdgeDirection = struct
  type edge_direction = Incoming | Outgoing

  let compare_direction d1 d2 =
    match (d1, d2) with
    | Incoming, Incoming | Outgoing, Outgoing -> 0
    | Incoming, Outgoing -> -1
    | Outgoing, Incoming -> 1

  let reverse_edge_direction = function
    | Incoming -> Outgoing
    | Outgoing -> Incoming

  let string_of_edge_direction = function
    | Incoming -> "Incoming"
    | Outgoing -> "Outgoing"
end

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

module ReductionQueue (Node : Symbol.S) (Edge : Symbol.S) = struct
  (* Bad immutabble priority queue *)

  let uid = ref 0

  type key = float * int
  type elt = (Node.t, Edge.t) reduction_candidate
  type e_dir = Edge.t * contraction_mode

  module EdgeDirectionMap = Map.Make (struct
    type t = e_dir

    let compare (e1, d1) (e2, d2) =
      let c = Edge.compare e1 e2 in
      if c = 0 then compare_mode d1 d2 else c
  end)

  module EdM = EdgeDirectionMap

  module FloatPairMap = Map.Make (struct
    type t = key

    let compare = compare
  end)

  type t = {
    queue : elt FloatPairMap.t;
    keys : key EdM.t;
    endpoints : e_dir list Node.Map.t;
  }

  let empty =
    { queue = FloatPairMap.empty; keys = EdM.empty; endpoints = Node.Map.empty }

  let append_to_map edge = function
    | None -> Some [ edge ]
    | Some x -> Some (edge :: x)

  let insert_new cost ({ edge; source_node; graph_direction; _ } as r_cand)
      ({ queue; keys; endpoints } as pq) =
    let e_dir = (edge, graph_direction) in
    match EdM.find_opt e_dir keys with
    (* Key should have the same cost *)
    | Some ((cost', _) as key) ->
        assert (cost = cost');
        (* We might need to reinsert  *)
        { pq with queue = FloatPairMap.add key r_cand queue }
    | None ->
        incr uid;
        let key = (cost, !uid) in
        {
          queue = FloatPairMap.add key r_cand queue;
          keys = EdM.add e_dir key keys;
          endpoints =
            Node.Map.update source_node (append_to_map e_dir) endpoints;
        }

  let of_list l =
    List.fold (fun acc (cost, cand) -> insert_new cost cand acc) empty l

  let find_min { queue; _ } = FloatPairMap.min_binding_opt queue

  let replace_node_old old new_ ({ endpoints; _ } as q) =
    (* Rethink how this works with e_dir *)
    Print.debug "Replacing node %t with %t" (Node.print old) (Node.print new_);
    let edges = Node.Map.find_opt old endpoints |> Option.value ~default:[] in
    List.fold
      (fun ({ endpoints; keys; _ } as acc) edge ->
        let endpoints =
          endpoints |> Node.Map.remove old
          |> Node.Map.update new_ (append_to_map edge)
        in
        match EdM.find_opt edge keys with
        | Some key ->
            Print.debug "Replaced node %t with %t" (Node.print old)
              (Node.print new_);
            {
              acc with
              queue =
                acc.queue
                |> FloatPairMap.update key (function
                     | None -> assert false
                     | Some r_cand -> Some { r_cand with source_node = new_ });
              endpoints;
            }
        | None -> acc)
      q edges

  let remove edge ({ queue; keys; _ } as q) =
    let key = EdM.find edge keys in
    (* assert (Edge.compare edge (Node.Map.find node endpoints) = 0); *)
    {
      q with
      queue = FloatPairMap.remove key queue;
      keys = EdM.remove edge keys;
    }

  let remove_non_strict edge ({ queue; keys; _ } as q) =
    match EdM.find_opt edge keys with
    | Some key ->
        (* assert (Edge.compare edge (Node.Map.find node endpoints) = 0); *)
        {
          q with
          queue = FloatPairMap.remove key queue;
          keys = EdM.remove edge keys;
        }
    | None -> q

  let remove_node node direction ({ endpoints; _ } as q) =
    Print.debug "Removing node %t" (Node.print node);
    let edges =
      Node.Map.find_opt node endpoints
      |> Option.value ~default:[]
      |> List.filter (fun (_, d) -> d = direction)
    in
    List.fold (fun q edge -> remove_non_strict edge q) q edges

  let print_rc = print_reduction_candidate Node.print Edge.print

  let print { queue; endpoints; _ } ppf =
    Format.fprintf ppf "{ %t;\n %t }"
      (Print.sequence ", "
         (fun ((c, uid), rc) ppf ->
           Format.fprintf ppf "(%f, %d) ↦ %t " c uid (print_rc rc))
         (FloatPairMap.bindings queue))
      (Node.Map.print
         (fun lst ppf ->
           Format.fprintf ppf "[ %t ]"
             (Print.sequence ", "
                (fun (e, dir) ppf ->
                  Format.fprintf ppf "(%t, %s)" (Edge.print e)
                    (string_of_mode dir))
                lst))
         endpoints)

  let iter fn { queue; _ } = FloatPairMap.iter fn queue
end

let print counter ppf =
  Format.fprintf ppf "{tycoerc: %t;\ndirtcoerc: %t}"
    (TyCoercionParam.Map.print
       (fun n ppf -> Print.print ppf "%f" n)
       counter.type_coercions)
    (DirtCoercionParam.Map.print
       (fun n ppf -> Print.print ppf "%f" n)
       counter.dirt_coercions)

let ( ++ ) c1 c2 =
  let combine _ a b = Some (a +. b) in
  {
    type_coercions =
      TyCoercionParam.Map.union combine c1.type_coercions c2.type_coercions;
    dirt_coercions =
      DirtCoercionParam.Map.union combine c1.dirt_coercions c2.dirt_coercions;
  }

let multiply c coercions =
  {
    type_coercions = TyCoercionParam.Map.map (( *. ) c) coercions.type_coercions;
    dirt_coercions =
      DirtCoercionParam.Map.map (( *. ) c) coercions.dirt_coercions;
  }

let combine (coercion_params : Coercion.Params.t) counter =
  let coercion_params =
    {
      type_coercions =
        coercion_params.type_coercion_params |> TyCoercionParam.Set.elements
        |> List.map (fun x -> (x, 1.0))
        |> TyCoercionParam.Map.of_bindings;
      dirt_coercions =
        coercion_params.dirt_coercion_params |> DirtCoercionParam.Set.elements
        |> List.map (fun x -> (x, 1.0))
        |> DirtCoercionParam.Map.of_bindings;
    }
  in
  coercion_params ++ counter

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

let collapse_type_cycles { Language.Constraints.ty_constraints; _ }
    (initial_polarities : FreeParams.params) : Constraint.t * FreeParams.params
    =
  let open Language.Constraints in
  (* Remove type cycles *)
  let garbage_collect_skeleton_component skel graph (new_constr, polarities) =
    let pack ty_param = { term = TyParam ty_param; ty = Skeleton.Param skel } in
    let components = TyConstraints.TyParamGraph.scc graph in
    (* For each component: pick one and add equal constraint  *)
    let new_constr, polarities =
      List.fold
        (fun (new_constr, polarities) component ->
          (* We suspect, that polarities are the same in the cycle *)
          (* Assert that the polarity is the same *)
          (* check_polarity_same_ty polarities component; *)
          match TyParam.Set.elements component with
          (* Can't have an empty cycle *)
          | [] -> assert false
          (* Select the first one as representative *)
          | top :: rest ->
              let new_constr, polarities =
                List.fold
                  (fun ((new_constr, polarities) :
                         Constraint.t * Type.FreeParams.params) param ->
                    ( Constraint.add_ty_equality
                        (pack top, pack param)
                        new_constr,
                      {
                        polarities with
                        type_params =
                          polarities.Type.FreeParams.type_params
                          |> FreeParams.TypeParams.combine_polarity top param;
                      } ))
                  (new_constr, polarities) rest
              in
              (new_constr, polarities))
        (new_constr, polarities) components
    in
    (new_constr, polarities)
  in

  let ty_constraints, polarities =
    Skeleton.Param.Map.fold garbage_collect_skeleton_component ty_constraints
      (Constraint.empty, initial_polarities)
  in
  (ty_constraints, polarities)

let collapse_dirt_cycles { Language.Constraints.dirt_constraints; _ }
    (polarities : FreeParams.params) =
  (* Beware, dirt polarities are not updated on the fly *)
  (* Dirt constraints *)
  let open Language.Constraints in
  let components = DirtConstraints.DirtParamGraph.scc dirt_constraints in
  let ty_constraints =
    List.fold_left
      (fun ty_constraints component ->
        let edge_labels =
          Dirt.Param.Set.fold
            (fun v acc ->
              let outgoing =
                DirtConstraints.DirtParamGraph.get_edges v dirt_constraints
              in
              let outgoing_in_component =
                outgoing
                |> Dirt.Param.Map.filter (fun k _ ->
                       Dirt.Param.Set.mem k component)
              in
              let dirts =
                outgoing_in_component |> Dirt.Param.Map.values |> List.map snd
              in
              dirts :: acc)
            component []
          |> List.flatten
        in
        let should_contract =
          Dirt.Param.Set.cardinal component > 1
          &&
          match edge_labels with
          | [] -> assert false
          | x :: _ ->
              Effect.Set.is_empty x
              && List.for_all (fun y -> Effect.Set.equal x y) edge_labels
        in
        if should_contract then
          (* Pick one and set all other to equal it *)
          let representative = Dirt.Param.Set.choose component in
          let ty_constraints =
            Dirt.Param.Set.fold
              (fun v acc ->
                if Dirt.Param.compare v representative != 0 then
                  Constraint.add_dirt_equality
                    (Dirt.no_effect v, Dirt.no_effect representative)
                    acc
                else acc)
              component ty_constraints
          in
          ty_constraints
        else ty_constraints)
      Constraint.empty components
  in
  (ty_constraints, polarities)

let graph_to_constraints skel_param graph =
  let open Language.Constraints in
  let module BaseSym = TyParam in
  let module EdgeSym = TyCoercionParam in
  let module G = TyConstraints.TyParamGraph in
  let g = G.fold (add_ty_constraint skel_param) graph empty in
  g

type graph = Language.Constraints.TyConstraints.TyParamGraph.t

module Q = ReductionQueue (TyParam) (TyCoercionParam)

type simple_node_constraction_state = {
  base_graph : graph;
  reversed_graph : graph;
  free_parameters : Type.FreeParams.params;
  coercion_queue : Q.t;
  collected_constraints : Constraint.t;
}

(* Joins simple type coercions to a reflexive coercion *)
let remove_type_bridges { Language.Constraints.ty_constraints; _ }
    ({ type_coercions; _ } as cnt) (params : FreeParams.params) =
  Print.debug "Counter: %t" (print cnt);
  let open Language.Constraints in
  let join_skeleton_component skel add_constraint graph new_constr =
    Print.debug "Joining simple nodes in %t" (Skeleton.Param.print skel);
    Print.debug "Graph: %t"
      (graph |> graph_to_constraints skel |> Constraints.print_dot);
    let module BaseSym = TyParam in
    let module EdgeSym = TyCoercionParam in
    let module G = TyConstraints.TyParamGraph in
    let module Q = ReductionQueue (BaseSym) (EdgeSym) in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in
    let increment v m =
      BaseSym.Map.update v
        (function None -> Some 1 | Some x -> Some (x + 1))
        m
    in
    let indeg, outdeg =
      G.fold
        (fun source sink _edge (indeg, outdeg) ->
          (increment sink indeg, increment source outdeg))
        graph
        (BaseSym.Map.empty, BaseSym.Map.empty)
    in
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
    (* Find the node with the least indegree *)
    let get_ones direction core_graph (source_node, n) =
      Print.debug "Direction: %s" (string_of_mode direction);
      Print.debug "%t" (BaseSym.print source_node);
      assert (n <> 0);
      if n = 1 then
        let sink_node, edge =
          G.get_edges source_node core_graph |> BaseSym.Map.bindings |> function
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
    let reduction_heap =
      Q.of_list
        (indeg_line @ outdeg_line
        |> List.map (fun rc ->
               ( type_coercions
                 |> EdgeSym.Map.find_opt rc.edge
                 |> Option.value ~default:Float.infinity,
                 rc )))
    in
    let process_part_general
        ({ source_node; sink_node; graph_direction; edge } :
          (BaseSym.t, EdgeSym.t) reduction_candidate)
        ({ base_graph; reversed_graph; coercion_queue; free_parameters; _ } as
        state) =
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
      (* Sanity check that the contraction still makes sense *)
      Q.iter
        (fun _ { source_node; graph_direction = ed; _ } ->
          (* graphs are not yet reversed here *)
          let g, rg = (base_graph, reversed_graph) in
          match ed with
          | Direct -> assert (G.get_edges source_node g |> G.Edges.cardinal = 1)
          | Reverse ->
              assert (G.get_edges source_node rg |> G.Edges.cardinal = 1))
        coercion_queue;
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
      let remove_current_edge q =
        q
        |> (match graph_direction with
           | Direct -> Q.remove_non_strict (edge, Direct)
           | _ -> fun x -> x)
        |>
        match graph_direction with
        | Reverse -> Q.remove_non_strict (edge, Reverse)
        | _ -> fun x -> x
      in

      (* Sanity check for the constraint we are contracting *)
      let connecting_edge = G.get_edges source_node base_graph in
      assert (G.Edges.cardinal connecting_edge = 1);
      let possible_sink, _edge' = G.Vertex.Map.choose connecting_edge in
      assert (BaseSym.compare possible_sink sink_node = 0);
      assert (possible_sink = sink_node);

      let get_vertices = G.Edges.vertices in

      let next = G.get_edges sink_node base_graph in
      let next_v = next |> get_vertices in

      let uncle = G.get_edges sink_node reversed_graph in
      let uncle_v = uncle |> get_vertices in

      let previous = G.get_edges source_node reversed_graph in
      let previous_v = previous |> get_vertices in

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
        let update_queue base_graph vertices direction queue =
          List.fold
            (fun acc potential_v ->
              let edges =
                base_graph |> G.get_edges potential_v |> G.Edges.bindings
              in
              match edges with
              | [ (sink_node, potential_e) ] ->
                  acc
                  |> Q.insert_new
                       (* If the coercion is not present, we assign it the largest value *)
                       (EdgeSym.Map.find_opt potential_e type_coercions
                       |> Option.value ~default:Float.infinity)
                       {
                         source_node = potential_v;
                         sink_node;
                         edge = potential_e;
                         graph_direction = direction;
                       }
              | _ -> acc |> Q.remove_node potential_v direction)
            queue vertices
        in

        let potential =
          [ sink_node; source_node ] @ previous_v @ uncle_v @ next_v
        in
        let base_graph, reversed_graph =
          reversal (base_graph, reversed_graph)
        in
        let queue =
          coercion_queue |> remove_current_edge
          |> update_queue reversed_graph potential Reverse
          |> update_queue base_graph potential Direct
        in
        ( {
            base_graph;
            reversed_graph;
            coercion_queue = queue;
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
      else
        (* If we can't make the coercion, just remove the edge from queue *)
        ( { state with coercion_queue = coercion_queue |> remove_current_edge },
          can_collapse )
    in
    let rec process (graph, reverse_graph) (queue : Q.t) params visited
        (constr : Constraint.t) =
      (* Choose next one *)
      Print.debug "Queue: %t" (Q.print queue);
      let rec find_next (queue : Q.t) =
        match Q.find_min queue with
        | Some (_, min) ->
            Print.debug "Trying: %t %s" (EdgeSym.print min.edge)
              (string_of_mode min.graph_direction);
            let queue = queue |> Q.remove (min.edge, min.graph_direction) in
            if EdgeSym.Set.mem min.edge visited then find_next queue
            else (
              Print.debug "Selecting: %t %s" (EdgeSym.print min.edge)
                (string_of_mode min.graph_direction);
              Some (min, queue))
        | None -> None
      in
      match find_next queue with
      | Some (m, queue) ->
          let processing_state =
            {
              base_graph = graph;
              reversed_graph = reverse_graph;
              free_parameters = params;
              coercion_queue = queue;
              collected_constraints = constr;
            }
          in
          let state, collapsed = process_part_general m processing_state in
          let visited =
            if collapsed then EdgeSym.Set.add m.edge visited else visited
          in
          process
            (state.base_graph, state.reversed_graph)
            state.coercion_queue state.free_parameters visited
            state.collected_constraints
      | None ->
          Print.debug "No more edges to process";
          constr
    in
    process (graph, inverse_graph) reduction_heap params EdgeSym.Set.empty
      new_constr
  in
  let new_constr =
    Skeleton.Param.Map.fold
      (fun skel graph acc ->
        let pack ty_param =
          { term = TyParam ty_param; ty = Skeleton.Param skel }
        in
        let add_constraint source target constraints =
          Constraint.add_ty_equality (pack source, pack target) constraints
        in
        join_skeleton_component skel add_constraint graph acc)
      ty_constraints Constraint.empty
  in
  new_constr

let add_constraint p1 p2 =
  Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.no_effect p2)

let add_empty_constraint p1 =
  Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.empty)

let contract_source_dirt_nodes { Language.Constraints.dirt_constraints; _ }
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
  let increment v m =
    BaseSym.Map.update v (function None -> Some 1 | Some x -> Some (x + 1)) m
  in
  Print.debug "Representatives: %t"
    (BaseSym.Map.print BaseSym.print representatives);
  let indeg = BaseSym.Map.map (fun _ -> 0) quotient_graph in
  let indegs =
    BaseSym.Map.fold
      (fun source edges indeg ->
        BaseSym.Map.fold
          (fun sink _ indeg ->
            if BaseSym.compare source sink = 0 then indeg
            else (* ignore self cycles *)
              increment sink indeg)
          edges indeg)
      quotient_graph indeg
  in

  let can_contract_component component =
    List.for_all
      (fun node ->
        if Type.FreeParams.DirtParams.can_be_positive node params.dirt_params
        then true
        else false)
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
          ( indegs,
            constraints
            |> List.fold_right
                 (fun node ->
                   Constraint.add_dirt_equality (Dirt.no_effect node, Dirt.empty))
                 component ))
        else (indegs, constraints))
      (indegs, Constraint.empty) components
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
      Constraint.empty
  in
  constraints

type dirt_graph = Language.Constraints.DirtConstraints.DirtParamGraph.t

module QD = ReductionQueue (Dirt.Param) (DirtCoercionParam)

type simple_dirt_node_constraction_state = {
  base_graph : dirt_graph;
  reversed_graph : dirt_graph;
  free_parameters : Type.FreeParams.params;
  coercion_queue : QD.t;
  collected_constraints : Constraint.t;
}

let remove_dirt_bridges { Language.Constraints.dirt_constraints; _ }
    ({ dirt_coercions; _ } as cnt) (params : FreeParams.params) =
  Print.debug "Counter: %t" (print cnt);
  let open Language.Constraints in
  let join_dirt_component add_constraint
      (graph :
        (DirtCoercionParam.t * Label.Set.t) Dirt.Param.Map.t Dirt.Param.Map.t)
      new_constr =
    let module BaseSym = Dirt.Param in
    let module EdgeSym = DirtCoercionParam in
    let module D = Label.Set in
    let module G = DirtConstraints.DirtParamGraph in
    let module Q = QD in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in
    let increment v m =
      BaseSym.Map.update v
        (function None -> Some 1 | Some x -> Some (x + 1))
        m
    in
    let indeg, outdeg =
      G.fold
        (fun source sink _edge (indeg, outdeg) ->
          (increment sink indeg, increment source outdeg))
        graph
        (BaseSym.Map.empty, BaseSym.Map.empty)
    in
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
    (* Find the node with the least indegree *)
    let get_ones direction core_graph (source_node, n) =
      assert (n <> 0);
      if n = 1 then
        let sink_node, edge =
          G.get_edges source_node core_graph |> BaseSym.Map.bindings |> function
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
    let reduction_heap =
      Q.of_list
        (indeg_line @ outdeg_line
        |> List.map (fun rc ->
               ( dirt_coercions
                 |> EdgeSym.Map.find_opt rc.edge
                 |> Option.value ~default:Float.infinity,
                 rc )))
    in
    let process_part_general
        ({ source_node; sink_node; graph_direction; edge } :
          (BaseSym.t, EdgeSym.t) reduction_candidate)
        ({ base_graph; reversed_graph; coercion_queue; _ } as state :
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

      (* Sanity check that the contraction still makes sense *)
      Q.iter
        (fun _ { source_node; graph_direction = ed; _ } ->
          (* graphs are not yet reversed here *)
          let g, rg = (base_graph, reversed_graph) in
          match ed with
          | Direct -> assert (G.get_edges source_node g |> G.Edges.cardinal = 1)
          | Reverse ->
              assert (G.get_edges source_node rg |> G.Edges.cardinal = 1))
        coercion_queue;
      let reversal =
        match graph_direction with
        | Direct -> fun (x, y) -> (x, y)
        | Reverse -> fun (x, y) -> (y, x)
      in
      (* Update according to the direction *)
      let base_graph, reversed_graph = reversal (base_graph, reversed_graph) in
      let remove_current_edge q =
        q
        |> Q.remove_non_strict (edge, Direct)
        |> Q.remove_non_strict (edge, Reverse)
      in

      (* Sanity check for the constraint we are contracting *)
      let connecting_edge = G.get_edges source_node base_graph in
      assert (G.Edges.cardinal connecting_edge = 1);
      let possible_sink, (_, edge_dirt) = G.Vertex.Map.choose connecting_edge in
      assert (BaseSym.compare possible_sink sink_node = 0);
      assert (possible_sink = sink_node);

      let get_vertices = G.Edges.vertices in

      let next = G.get_edges sink_node base_graph in
      let next_v = next |> get_vertices in

      let uncle = G.get_edges sink_node reversed_graph in
      let uncle_v = uncle |> get_vertices in

      let previous = G.get_edges source_node reversed_graph in
      let previous_v = previous |> get_vertices in

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
        let update_queue
            (base_graph : (EdgeSym.t * D.t) BaseSym.Map.t BaseSym.Map.t)
            vertices direction queue =
          List.fold
            (fun acc potential_v ->
              let edges =
                base_graph |> G.get_edges potential_v |> G.Edges.bindings
              in
              match edges with
              | [ (sink_node, (potential_e, _)) ] ->
                  acc
                  |> Q.insert_new
                       (* If the coercion is not present, we assign it the largest value *)
                       (EdgeSym.Map.find_opt potential_e dirt_coercions
                       |> Option.value ~default:Float.infinity)
                       {
                         source_node = potential_v;
                         sink_node;
                         edge = potential_e;
                         graph_direction = direction;
                       }
              | _ -> acc |> Q.remove_node potential_v direction)
            queue vertices
        in
        let potential =
          [ sink_node; source_node ] @ previous_v @ uncle_v @ next_v
        in
        let base_graph, reversed_graph =
          reversal (base_graph, reversed_graph)
        in
        let queue =
          coercion_queue |> remove_current_edge
          |> update_queue reversed_graph potential Reverse
          |> update_queue base_graph potential Direct
        in

        ( {
            base_graph;
            reversed_graph;
            coercion_queue = queue;
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
      else
        (* If we can't make the coercion, just remove the edge from queue *)
        ( { state with coercion_queue = coercion_queue |> remove_current_edge },
          None )
    in
    let rec process (graph, reverse_graph) (queue : Q.t) params visited touched
        (constr : Constraint.t) =
      (* Choose next one *)
      Print.debug "Queue: %t" (Q.print queue);
      let rec find_next (queue : Q.t) =
        match Q.find_min queue with
        | Some (_, min) ->
            Print.debug "Trying: %t" (EdgeSym.print min.edge);
            let queue = queue |> Q.remove (min.edge, min.graph_direction) in
            if EdgeSym.Set.mem min.edge visited then find_next queue
            else Some (min, queue)
        | None -> None
      in
      match find_next queue with
      | Some (m, queue) ->
          let visited = EdgeSym.Set.add m.edge visited in
          let processing_state =
            {
              base_graph = graph;
              reversed_graph = reverse_graph;
              free_parameters = params;
              coercion_queue = queue;
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
            state.coercion_queue state.free_parameters visited touched
            state.collected_constraints
      | None -> (constr, touched)
    in
    process (graph, inverse_graph) reduction_heap params EdgeSym.Set.empty []
      new_constr
  in
  let add_constraint source target constraints =
    Constraint.add_dirt_equality
      (Dirt.no_effect source, Dirt.no_effect target)
      constraints
  in
  join_dirt_component add_constraint dirt_constraints Constraint.empty

let contract_constraints () = ()

let rec score_expression e =
  let cur, cong =
    match e with
    | { term = Term.Var _; _ } -> (Coercion.Params.empty, empty)
    | { term = Term.Const _; _ } -> (Coercion.Params.empty, empty)
    | { term = Term.Tuple lst; _ } ->
        ( Coercion.Params.empty,
          List.fold ( ++ ) empty (List.map score_expression lst) )
    | { term = Term.Record r; _ } ->
        ( Coercion.Params.empty,
          List.fold ( ++ ) empty
            (List.map score_expression (Label.Map.values r)) )
    | { term = Term.Variant (_, e); _ } ->
        (Coercion.Params.empty, Option.default_map empty score_expression e)
    | { term = Term.Lambda abs; _ } ->
        (Coercion.Params.empty, score_abstraction abs)
    | { term = Term.Handler hc; _ } ->
        (Coercion.Params.empty, score_handler_clauses hc)
    | { term = Term.HandlerWithFinally { handler_clauses; finally_clause }; _ }
      ->
        ( Coercion.Params.empty,
          score_handler_clauses handler_clauses
          ++ score_abstraction finally_clause )
    | { term = Term.CastExp (exp, coer); _ } ->
        (Coercion.coercion_params_ty_coercion coer, score_expression exp)
  in
  combine cur (multiply 0.5 cong)

and score_abstraction { term = _, c; _ } = score_computation c

and score_handler_clauses { term = { Term.value_clause; effect_clauses }; _ } =
  score_abstraction value_clause
  ++ (Assoc.values_of effect_clauses.effect_part
     |> List.map (fun { term = _, _, c; _ } -> score_computation c)
     |> List.fold ( ++ ) empty)

and score_computation c =
  let cur, cong =
    match c with
    | { term = Term.Value e; _ } -> (Coercion.Params.empty, score_expression e)
    | { term = Term.LetVal (e, abs); _ } ->
        (Coercion.Params.empty, score_expression e ++ score_abstraction abs)
    | { term = Term.LetRec (lst, c); _ } ->
        ( Coercion.Params.empty,
          Assoc.fold_left
            (fun acc (_, abs) -> acc ++ score_abstraction abs)
            empty lst
          ++ score_computation c )
    | { term = Term.Match (e, lst); _ } ->
        ( Coercion.Params.empty,
          score_expression e
          ++ List.fold_left
               (fun acc abs -> acc ++ score_abstraction abs)
               empty lst )
    | { term = Term.Apply (e1, e2); _ } ->
        (Coercion.Params.empty, score_expression e1 ++ score_expression e2)
    | { term = Term.Handle (e, c); _ } ->
        (Coercion.Params.empty, score_expression e ++ score_computation c)
    | { term = Term.Call (_, e, abs); _ } ->
        (Coercion.Params.empty, score_expression e ++ score_abstraction abs)
    | { term = Term.Bind (c1, abs); _ } ->
        (Coercion.Params.empty, score_computation c1 ++ score_abstraction abs)
    | { term = Term.CastComp (c, coer); _ } ->
        (Coercion.coercion_params_dirty_coercion coer, score_computation c)
    | { term = Term.Check (_, c); _ } ->
        (Coercion.Params.empty, score_computation c)
  in

  combine cur (multiply 0.5 cong)

let simplify_type_constraints ~loc type_definitions subs constraints
    (get_counter, get_params) =
  let cycle_constraints, _free_params =
    collapse_type_cycles constraints (get_params subs)
  in
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot ~param_polarity:(get_params subs)
       constraints);
  (* We don't really need the free parameters yet, as we do another unification pass *)
  let subs, constraints =
    Unification.unify ~loc type_definitions
      (subs, constraints, cycle_constraints)
  in
  let constraints = Constraints.remove_loops constraints in
  let subs, constraints =
    if simplify_type_params_full then
      let simple_one_constraints =
        remove_type_bridges constraints (get_counter subs) (get_params subs)
      in
      let subs', simple_one_constraints' =
        Unification.unify ~loc type_definitions
          (subs, constraints, simple_one_constraints)
      in
      (subs', simple_one_constraints')
    else (subs, constraints)
  in
  (subs, constraints)

let simplify_dirt_contraints ~loc type_definitions subs constraints
    (get_counter, get_params) =
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot ~param_polarity:(get_params subs)
       constraints);
  let new_constraints, _free_params =
    collapse_dirt_cycles constraints (get_params subs)
  in
  let subs, constraints =
    Unification.unify ~loc type_definitions (subs, constraints, new_constraints)
  in
  let subs, constraints =
    if simplify_dirt_params_full then
      let new_constraints =
        contract_source_dirt_nodes constraints (get_params subs)
      in
      Unification.unify ~loc type_definitions
        (subs, constraints, new_constraints)
    else (subs, constraints)
  in
  Print.debug "Full constraints after source contraction: %t"
    (Language.Constraints.print_dot ~param_polarity:(get_params subs)
       constraints);
  let rec runner level subs_state cons_state =
    Print.debug "Full constraints in runner %d: %t" level
      (Language.Constraints.print_dot ~param_polarity:(get_params subs)
         constraints);
    let new_constraints, touched =
      remove_dirt_bridges cons_state (get_counter subs_state)
        (get_params subs_state)
    in
    let subs_state, cons_state =
      Unification.unify ~loc type_definitions
        (subs_state, cons_state, new_constraints)
    in
    let cons_state = Constraints.remove_loops cons_state in
    Print.debug "Touched: %d %t" (List.length touched)
      (Print.sequence "," Dirt.Param.print touched);
    if List.length touched > 0 then runner (level + 1) subs_state cons_state
    else (subs_state, cons_state)
  in
  let subs, constraints =
    if simplify_dirt_params_full then runner 0 subs constraints
    else (subs, constraints)
  in

  let subs, constraints =
    Unification.unify ~loc type_definitions (subs, constraints, Constraint.empty)
  in
  (* Optimize possible empty dirts  *)
  let new_constraints =
    contract_source_dirt_nodes constraints (get_params subs)
  in
  let subs, constraints =
    Unification.unify ~loc type_definitions (subs, constraints, new_constraints)
  in
  (* Some parameters are present in the type, but not in constrains *)
  let present =
    Language.Constraints.DirtConstraints.DirtParamGraph.vertices
      constraints.dirt_constraints
  in
  let params = (get_params subs).dirt_params in
  let new_constraints =
    Dirt.Param.Set.fold
      (fun p acc ->
        if not (Dirt.Param.Set.mem p present) then
          acc |> Constraint.add_dirt_equality (Dirt.no_effect p, Dirt.empty)
        else acc)
      (Dirt.Param.Set.diff params.positive params.negative)
      Constraint.empty
  in
  let subs, constraints =
    Unification.unify ~loc type_definitions (subs, constraints, new_constraints)
  in
  (subs, constraints)

let simplify_constraints ~loc type_definitions subs constraints
    (get_counter, get_params) =
  let subs, constraints =
    if simplify_type_params then
      simplify_type_constraints ~loc type_definitions subs constraints
        (get_counter, get_params)
    else (subs, constraints)
  in
  let subs, constraints =
    if simplify_dirt_params then
      simplify_dirt_contraints ~loc type_definitions subs constraints
        (get_counter, get_params)
    else (subs, constraints)
  in
  (subs, constraints)

let simplify_computation ~loc type_definitions subs constraints cmp =
  Print.debug "cmp: %t" (Term.print_computation cmp);

  simplify_constraints ~loc type_definitions subs constraints
    ( (fun subs ->
        let cmp = Term.apply_sub_comp subs cmp in
        let counter = score_computation cmp in
        let counter = multiply (-1.0) counter in
        counter),
      fun subs ->
        let cmp = Term.apply_sub_comp subs cmp in
        let parity = calculate_polarity_dirty_ty cmp.ty in
        parity )

let simplify_top_let_rec ~loc type_definitions subs constraints defs =
  simplify_constraints ~loc type_definitions subs constraints
    ( (fun subs ->
        let defs = Assoc.map (Term.apply_sub_abs subs) defs in
        let counter =
          List.fold
            (fun acc abs -> score_abstraction abs ++ acc)
            empty (Assoc.values_of defs)
        in
        let counter = multiply (-1.0) counter in
        counter),
      fun subs ->
        let defs = Assoc.map (Term.apply_sub_abs subs) defs in
        let counter =
          List.fold
            (fun acc abs ->
              FreeParams.union (calculate_polarity_abs_ty abs.ty) acc)
            FreeParams.empty (Assoc.values_of defs)
        in
        counter )

let a f g h x =
  if f x then
    (* can be if true, but we remove it to prevent optimizations *)
    (g x, h x)
  else (h x, g x)
