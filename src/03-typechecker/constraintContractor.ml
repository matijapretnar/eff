open Utils
open Language
open Type
open Coercion

type counter = {
  type_coercions : float TyCoercionParam.Map.t;
  dirt_coercion : float DirtCoercionParam.Map.t;
}

type contraction_mode = Incoming | Outgoing

let string_of_mode = function Incoming -> "incoming" | Outgoing -> "outgoing"

let reverse_mode = function Incoming -> Outgoing | Outgoing -> Incoming

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

let invert_with_dir data = function Outgoing -> data | Incoming -> invert data

let source_sink_candidate { candidates = { sources; sinks; _ }; _ } =
  match Dirt.Param.Set.choose_opt sources with
  | Some s -> Some (s, Outgoing)
  | None -> (
      match Dirt.Param.Set.choose_opt sinks with
      | Some s -> Some (s, Incoming)
      | None -> None)

let incoming_outgoing_candidate { candidates = { incoming; outgoing; _ }; _ } =
  match Dirt.Param.Set.choose_opt outgoing with
  | Some s -> Some (s, Outgoing)
  | None -> (
      match Dirt.Param.Set.choose_opt incoming with
      | Some s -> Some (s, Incoming)
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
          let add = BaseSym.Set.add candidate in
          union candidates
            {
              incoming =
                (if outdeg = 1 then add candidates.incoming
                else candidates.incoming);
              outgoing =
                (if indeg = 1 then add candidates.outgoing
                else candidates.outgoing);
              sources =
                (if indeg = 0 then add candidates.sources
                else candidates.sources);
              sinks =
                (if outdeg = 0 then add candidates.sinks else candidates.sinks);
            })
        new_candidates candidates
      |> remove_candidates visited unavailable contraction_touched;
  }

let empty =
  {
    type_coercions = TyCoercionParam.Map.empty;
    dirt_coercion = DirtCoercionParam.Map.empty;
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
  node : 'a;
  edge : 'b;
  edge_direction : EdgeDirection.edge_direction;
}

let print_reduction_candidate pn pe { node; edge; edge_direction } ppf =
  Format.fprintf ppf "{ %t; %t; %s }" (pn node) (pe edge)
    (EdgeDirection.string_of_edge_direction edge_direction)

module ReductionQueue (Node : Symbol.S) (Edge : Symbol.S) = struct
  (* Bad immutabble priority queue *)

  open EdgeDirection

  let uid = ref 0

  type key = float * int

  type elt = (Node.t, Edge.t) reduction_candidate

  type e_dir = Edge.t * edge_direction

  module EdgeDirectionMap = Map.Make (struct
    type t = e_dir

    let compare (e1, d1) (e2, d2) =
      let c = Edge.compare e1 e2 in
      if c = 0 then compare_direction d1 d2 else c
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

  let insert_new cost ({ edge; node; edge_direction } as r_cand)
      ({ queue; keys; endpoints } as pq) =
    let e_dir = (edge, edge_direction) in
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
          endpoints = Node.Map.update node (append_to_map e_dir) endpoints;
        }

  let of_list l =
    List.fold (fun acc (cost, cand) -> insert_new cost cand acc) empty l

  let find_min { queue; _ } = FloatPairMap.min_binding_opt queue

  let replace_node old new_ ({ endpoints; _ } as q) =
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
                     | Some r_cand -> Some { r_cand with node = new_ });
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
                    (string_of_edge_direction dir))
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
       counter.dirt_coercion)

let ( ++ ) c1 c2 =
  let combine _ a b = Some (a +. b) in
  {
    type_coercions =
      TyCoercionParam.Map.union combine c1.type_coercions c2.type_coercions;
    dirt_coercion =
      DirtCoercionParam.Map.union combine c1.dirt_coercion c2.dirt_coercion;
  }

let multiply c coercions =
  {
    type_coercions = TyCoercionParam.Map.map (( *. ) c) coercions.type_coercions;
    dirt_coercion = DirtCoercionParam.Map.map (( *. ) c) coercions.dirt_coercion;
  }

let combine (coercion_params : Coercion.Params.t) counter =
  let coercion_params =
    {
      type_coercions =
        coercion_params.type_coercion_params |> TyCoercionParam.Set.elements
        |> List.map (fun x -> (x, 1.0))
        |> TyCoercionParam.Map.of_bindings;
      dirt_coercion =
        coercion_params.dirt_coercion_params |> DirtCoercionParam.Set.elements
        |> List.map (fun x -> (x, 1.0))
        |> DirtCoercionParam.Map.of_bindings;
    }
  in
  coercion_params ++ counter

let check_polarity_same fold fn (polarities : FreeParams.params) params =
  let _ =
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
  in
  ()

let check_polarity_same_ty =
  check_polarity_same TyParam.Set.fold FreeParams.get_type_polarity

let check_polarity_same_dirt =
  check_polarity_same Dirt.Param.Set.fold FreeParams.get_dirt_polarity

let collapse_cycles { Language.Constraints.ty_constraints; dirt_constraints }
    polarities =
  let open Language.Constraints in
  (* Remove type cycles *)
  let garbage_collect_skeleton_component skel graph new_constr =
    let pack ty_param = { term = TyParam ty_param; ty = Skeleton.Param skel } in
    let components = TyConstraints.TyParamGraph.scc graph in
    (* For each component: pick one and add equal constraint  *)
    let new_constr' =
      List.fold
        (fun new_constr component ->
          (* Assert that the polarity is the same *)
          check_polarity_same_ty polarities component;
          match TyParam.Set.elements component with
          | [] -> assert false
          (* Select the first one as representative *)
          | top :: rest ->
              let new_constr' =
                List.fold
                  (fun new_constr param ->
                    Constraint.add_ty_equality (pack top, pack param) new_constr)
                  new_constr rest
              in
              new_constr')
        new_constr components
    in
    new_constr'
  in

  let ty_constraints =
    if !Config.garbage_collect.type_contraction.contract_cycles then
      Skeleton.Param.Map.fold garbage_collect_skeleton_component ty_constraints
        Constraint.empty
    else Constraint.empty
  in
  (* Dirt constraints *)
  if !Config.garbage_collect.dirt_contraction.contract_cycles then
    let components = DirtConstraints.DirtParamGraph.scc dirt_constraints in
    let ty_constraints =
      List.fold_left
        (fun ty_constraints component ->
          if
            Dirt.Param.Set.cardinal component = 1
            (* Compress cycles with the effect edges *)
            || not
                 (let edge_labels =
                    Dirt.Param.Set.fold
                      (fun v l ->
                        let edges =
                          DirtConstraints.DirtParamGraph.get_edges v
                            dirt_constraints
                        in
                        Dirt.Param.Set.fold
                          (fun target l ->
                            [
                              DirtConstraints.DirtParamGraph.Edges.get_edge
                                target edges;
                            ]
                            @ l)
                          component l)
                      component []
                    |> List.filter_map (fun x -> x)
                  in
                  let _, drt =
                    match edge_labels with [] -> assert false | x :: _ -> x
                  in
                  (Effect.Set.is_empty drt
                 || !Config.garbage_collect.dirt_contraction
                      .contract_same_dirt_cycles)
                  && List.for_all
                       (fun (_, drt') -> Effect.Set.equal drt drt')
                       edge_labels)
          then ty_constraints
          else
            (* Pick one and set all other to equal it *)
            let representative = Dirt.Param.Set.choose component in
            let ty_constraints =
              Dirt.Param.Set.fold
                (fun v acc ->
                  if v <> representative then
                    Constraint.add_dirt_equality
                      (Dirt.no_effect v, Dirt.no_effect representative)
                      acc
                  else acc)
                component ty_constraints
            in
            ty_constraints)
        ty_constraints components
    in
    ty_constraints
  else ty_constraints

let graph_to_constraints skel_param graph =
  let open Language.Constraints in
  let module BaseSym = TyParam in
  let module EdgeSym = TyCoercionParam in
  let module G = TyConstraints.TyParamGraph in
  G.fold (add_ty_constraint skel_param) graph empty

let join_simple_nodes { Language.Constraints.ty_constraints; _ }
    ({ type_coercions; _ } as cnt) (_params : FreeParams.params) =
  Print.debug "Counter: %t" (print cnt);
  let open Language.Constraints in
  let join_skeleton_component _skel add_constraint is_collapsible graph
      new_constr =
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
    let get_ones direction core_graph (node, n) =
      Print.debug "Direction: %s"
        (EdgeDirection.string_of_edge_direction direction);
      Print.debug "%t" (BaseSym.print node);
      assert (n <> 0);
      (* assert (BaseSym.Set.is_empty params.type_params.positive); *)
      if n = 1 then
        Some
          {
            edge_direction = direction;
            node;
            edge =
              (G.get_edges node core_graph |> BaseSym.Map.bindings |> function
               | [ ((_, e) : BaseSym.t * EdgeSym.t) ] -> e
               | [] -> assert false
               | _ -> assert false);
          }
      else None
    in
    let filter direction core_graph line =
      line |> BaseSym.Map.bindings
      |> List.filter_map (get_ones direction core_graph)
    in
    let indeg_line = filter Incoming inverse_graph indeg in
    let outdeg_line = filter Outgoing graph outdeg in
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
        ({ node = target; edge_direction; edge } :
          (BaseSym.t, EdgeSym.t) reduction_candidate)
        (base_graph, reverse_graph) parents queue constr =
      (* Removing outging/incoming edges with degree 1 is practically the same but on different (reversed) graph
         The naming in this function assumes that the input graph is original graph and we are removing edges with
         exactly 1 incoming edge *)
      (* Set the correct direction *)
      let direction_changer =
        match edge_direction with
        | Incoming -> fun x -> x
        | Outgoing -> EdgeDirection.reverse_edge_direction
      in
      let graph_reversal =
        match edge_direction with
        | Incoming -> fun (x, y) -> (x, y)
        | Outgoing -> fun (x, y) -> (y, x)
      in
      (* Sanity check *)
      Q.iter
        (fun _ { node; edge_direction = ed; _ } ->
          (* graphs are not yet reversed here *)
          let g, rg = (base_graph, reverse_graph) in
          match ed with
          | Incoming -> assert (G.get_edges node rg |> G.Edges.cardinal = 1)
          | Outgoing -> assert (G.get_edges node g |> G.Edges.cardinal = 1))
        queue;

      (* Node can get identified during the contraction phase, so we have to recheck it *)
      let target =
        BaseSym.Map.find_opt target parents |> Option.value ~default:target
      in
      (* Swap graphs according to edge direction *)
      let base_graph, reverse_graph =
        graph_reversal (base_graph, reverse_graph)
      in
      let remove_current_edge q =
        q
        |> Q.remove_non_strict (edge, Incoming)
        |> Q.remove_non_strict (edge, Outgoing)
      in
      let incoming = G.get_edges target reverse_graph in
      Print.debug "Incoming edges: %d" (G.Edges.cardinal incoming);
      assert (G.Edges.cardinal incoming = 1);
      let source, edge' = G.Vertex.Map.choose incoming in
      Print.debug "In mode %s, removing: %t %t with %t"
        (EdgeDirection.string_of_edge_direction edge_direction)
        (BaseSym.print target) (EdgeSym.print edge) (BaseSym.print source);
      assert (edge = edge');
      assert (EdgeSym.compare edge edge' = 0);
      let get_vertices = G.Edges.vertices in
      let next = G.get_edges target base_graph in
      let next_v = next |> get_vertices in
      let next_rev_v = G.get_edges target reverse_graph |> get_vertices in
      let source_next_v = G.get_edges source base_graph |> get_vertices in
      let source_next_rev_v =
        G.get_edges source reverse_graph |> get_vertices
      in
      Print.debug "Next: %t"
        (Print.sequence "," EdgeSym.print (next |> BaseSym.Map.values));

      (* We have to recalculaculate for 4 sets:
         incoming/outgiong from source and incoming/outgoing from target
          + joined source/target
      *)
      if is_collapsible edge then
        let base_graph =
          base_graph
          |> G.remove_edge source target (* remove this edge *)
          |> G.Edges.fold (* rewire other edges *)
               (fun next e acc ->
                 acc |> G.remove_edge target next
                 |> G.add_edge (* Triangels can produce duplicate edges *)
                      ~allow_duplicate:true source next e)
               next
          |> G.remove_vertex_unsafe target
        and reverse_graph =
          reverse_graph
          |> G.remove_edge target source
          |> G.Edges.fold (* rewire other edges *)
               (fun next e acc ->
                 acc |> G.remove_edge next target
                 |> G.add_edge ~allow_duplicate:true next source e)
               next
          |> G.remove_vertex_unsafe target
        in
        (* TODO: zdi se, da tega na novo nastalega ne pogledam pravilno (tj source)  *)
        let update_queue base_graph vertices direction queue =
          List.fold
            (fun acc potential_v ->
              let edges =
                base_graph |> G.get_edges potential_v |> G.Edges.edges
              in
              match edges with
              | [ potential_e ] ->
                  acc
                  |> Q.insert_new
                       (* If the coercion is not present, we assign it the largest value *)
                       (EdgeSym.Map.find_opt potential_e type_coercions
                       |> Option.value ~default:Float.infinity)
                       {
                         node = potential_v;
                         edge = potential_e;
                         edge_direction = direction;
                       }
              | _ -> acc |> Q.remove_node potential_v direction)
            queue vertices
          (* |> List.fold_right
               (fun potential edg acc ->
                 let num =
                   base_graph |> G.get_edges potential |> G.Edges.cardinal
                 in
                 if num = 1 then
                   acc
                   |> Q.insert_new
                        (* If the coercion is not present, we assign it the largest value *)
                        (EdgeSym.Map.find_opt edg type_coercions
                        |> Option.value ~default:Float.infinity)
                        {
                          node = potential;
                          edge = edg;
                          edge_direction = direction;
                        }
                 else (
                   Print.debug "Removing: %t" (EdgeSym.print edg);
                   acc
                   |> Q.remove_non_strict (edg, direction)
                   |> Q.remove_node potential)) *)

          (* Also check source *)
          (* |> fun acc ->
             let edgs = base_graph |> G.get_edges source in
             if G.Edges.cardinal edgs = 1 then (
               Print.debug "Adding source %t %s" (BaseSym.print source)
                 (EdgeDirection.string_of_edge_direction direction);
               let edg = G.Edges.fold (fun _ e acc -> e :: acc) edgs [] in
               assert (List.length edg = 1);
               let edg = List.hd edg in
               acc
               |> Q.insert_new
                    (EdgeSym.Map.find_opt edg type_coercions
                    |> Option.value ~default:Float.infinity)
                    { node = source; edge = edg; edge_direction = direction })
             else (
               Print.debug "Removing source %t %s" (BaseSym.print source)
                 (EdgeDirection.string_of_edge_direction direction);
               acc |> Q.remove_node source) *)
        in

        let potential =
          (source :: next_v) @ next_rev_v @ source_next_v @ source_next_rev_v
        in
        let queue =
          queue |> remove_current_edge
          |> Q.replace_node target source
          |> update_queue reverse_graph potential (direction_changer Incoming)
          |> update_queue base_graph potential (direction_changer Outgoing)
        in
        (* Clean up at the end *)
        let base_graph, reverse_graph =
          graph_reversal (base_graph, reverse_graph)
        in
        ((base_graph, reverse_graph), queue, add_constraint source target constr)
      else
        (* Clean up at the end *)
        let base_graph, reverse_graph =
          graph_reversal (base_graph, reverse_graph)
        in
        ((base_graph, reverse_graph), queue |> remove_current_edge, constr)
    in
    let rec process parents (graph, reverse_graph) (queue : Q.t) visited constr
        =
      (* Choose next one *)
      Print.debug "Queue: %t" (Q.print queue);
      Print.debug "Graph: %t"
        (graph |> graph_to_constraints _skel |> Constraints.print_dot);
      let rec find_next (queue : Q.t) =
        match Q.find_min queue with
        | Some (_, min) ->
            Print.debug "Trying: %t" (EdgeSym.print min.edge);
            let queue = queue |> Q.remove (min.edge, min.edge_direction) in
            if EdgeSym.Set.mem min.edge visited then find_next queue
            else Some (min, queue)
        | None -> None
      in
      match find_next queue with
      | Some (m, queue) ->
          let visited = EdgeSym.Set.add m.edge visited in
          let (graph, reverse_graph), queue, constr =
            process_part_general m (graph, reverse_graph) parents queue constr
          in
          process parents (graph, reverse_graph) queue visited constr
      | None -> constr
    in
    process BaseSym.Map.empty (graph, inverse_graph) reduction_heap
      EdgeSym.Set.empty new_constr
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
        join_skeleton_component skel add_constraint
          (fun _ -> (* collapse all edges *) true)
          graph acc)
      ty_constraints Constraint.empty
  in
  new_constr

let join_simple_dirt_nodes { Language.Constraints.dirt_constraints; _ } params
    _level =
  let open Language.Constraints in
  let module BaseSym = Dirt.Param in
  let module G = DirtConstraints.DirtParamGraph in
  let has_trivial_solution param mode =
    match (FreeParams.get_dirt_polarity param params, mode) with
    | None, _ -> true
    | Some Positive, Outgoing -> true
    | Some Negative, Incoming -> true
    | _ -> false
  in
  let get_source_sink graph inverse_graph =
    let vertices = G.vertices graph in
    let sources, sinks =
      BaseSym.Set.fold
        (fun v (sources, sinks) ->
          ( sources
            |> BaseSym.Set.union
                 (if G.get_edges v inverse_graph |> BaseSym.Map.is_empty then
                  BaseSym.Set.singleton v
                 else BaseSym.Set.empty),
            sinks
            |> BaseSym.Set.union
                 (if G.get_edges v graph |> BaseSym.Map.is_empty then
                  BaseSym.Set.singleton v
                 else BaseSym.Set.empty) ))
        vertices
        (BaseSym.Set.empty, BaseSym.Set.empty)
    in
    (sources, sinks)
  in
  let increment v m =
    BaseSym.Map.update v (function None -> Some 1 | Some x -> Some (x + 1)) m
  in
  let get_indeg_outdeg_one graph inverse_graph =
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
    let get_ones (k, n) =
      assert (n <> 0);
      if n = 1 then Some k else None
    in
    let filter line =
      line |> BaseSym.Map.bindings |> List.filter_map get_ones
      |> BaseSym.Set.of_list
    in
    let indeg_line = filter indeg and outdeg_line = filter outdeg in
    (indeg_line, outdeg_line)
  in
  let graph = dirt_constraints in
  let inverse_graph = G.reverse dirt_constraints in
  let sources, sinks = get_source_sink graph inverse_graph in
  let indeg_line, outdeg_line = get_indeg_outdeg_one graph inverse_graph in
  Print.debug "initial outgouing %t"
    (Print.sequence "," BaseSym.print (BaseSym.Set.elements outdeg_line));
  Print.debug "initial incoming %t"
    (Print.sequence "," BaseSym.print (BaseSym.Set.elements indeg_line));
  let contraction_data =
    {
      graph;
      inverse_graph;
      visited = BaseSym.Set.empty;
      unavailable = BaseSym.Set.empty;
      contraction_touched = BaseSym.Set.empty;
      changed = BaseSym.Set.empty;
      candidates =
        { sources; sinks; incoming = outdeg_line; outgoing = indeg_line };
    }
  in
  let add_constraint p1 p2 =
    Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.no_effect p2)
  in
  let add_empty_constraint p1 =
    Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.empty)
  in
  let add_full_constraint _p1 =
    failwith "We assume this is not going to happen"
  in
  (* We can assume that the graph is a DAG *)
  let process_source_sink
      ({ graph; visited; inverse_graph; unavailable; changed; _ } as
      contraction_data) mode target constr =
    Print.debug "Processing: %t, mode %s" (BaseSym.print target)
      (string_of_mode mode);
    let visited = BaseSym.Set.add target visited in
    let contraction_data = { contraction_data with visited } in
    if has_trivial_solution target mode then (
      Print.debug "Contracting";
      (*
         Print.debug "from me: %t"
           (Print.sequence "," BaseSym.print
              (G.get_edges target inverse_graph |> BaseSym.Map.keys)); *)
      assert (G.get_edges target inverse_graph |> G.Edges.cardinal = 0);

      let out = G.get_edges target graph in
      let graph =
        graph |> G.remove_edges target out |> G.remove_vertex_unsafe target
      in
      let out = BaseSym.Map.keys out in
      let inverse_graph =
        List.fold
          (fun inverse_graph v -> G.remove_edge v target inverse_graph)
          inverse_graph out
        |> G.remove_vertex_unsafe target
      in
      Print.debug "new Candidates: %t" (Print.sequence "," BaseSym.print out);
      (* No need to remove incoming edges, as there are none *)
      let contraction_data =
        {
          contraction_data with
          graph;
          inverse_graph;
          changed = BaseSym.Set.add target changed;
        }
      in
      ( (match mode with
        | Incoming -> add_full_constraint
        | Outgoing -> add_empty_constraint)
          target constr,
        recalculate_dirt_reduction_candidates contraction_data out ))
    else
      let contraction_data =
        {
          contraction_data with
          unavailable = BaseSym.Set.add target unavailable;
        }
      in
      (constr, recalculate_dirt_reduction_candidates contraction_data [])
  in
  let process_simple_node
      ({ graph; inverse_graph; visited; changed; _ } as contraction_data) mode
      target constr =
    (* Removing outging/incoming edges with degree 1 is practically the same but on different (reversed) graph
        The naming in this function assumes that the input graph is original graph and we are removing edges with
        exactly 1 incoming edge -> *)
    Print.debug "Contracting drit, in mode %s, removing: %t"
      (string_of_mode mode) (BaseSym.print target);

    Print.debug "outgoing %t"
      (Print.sequence "," BaseSym.print
         (BaseSym.Set.elements contraction_data.candidates.outgoing));

    let visited = BaseSym.Set.add target visited in
    let contraction_data = { contraction_data with visited } in
    let incoming = G.get_edges target inverse_graph in
    Print.debug "Inc: %t"
      (Print.sequence "," BaseSym.print (BaseSym.Map.keys incoming));
    assert (G.Edges.cardinal incoming = 1);
    let source, ((_, dirts) as _edge) = G.Vertex.Map.choose incoming in
    let outgoing = G.get_edges target graph in
    let outgoing_lst = outgoing |> G.Edges.edges in
    let union, intersection =
      List.fold
        (fun (union, intersection) (_, drt) ->
          (Effect.Set.union union drt, Effect.Set.inter intersection drt))
        (* If outgoing list is empty, everything holds  *)
        ( Effect.Set.empty,
          match outgoing_lst with
          | [] -> Effect.Set.empty
          | (_, drt) :: _ -> drt )
        outgoing_lst
    in
    let _all_edges_same = Effect.Set.equal union intersection in
    let all_next_empty = Effect.Set.is_empty union in
    let can_continue_on_graph = all_next_empty && Effect.Set.is_empty dirts in
    let contraction_touched =
      if can_continue_on_graph then BaseSym.Set.empty
      else BaseSym.Set.of_list (BaseSym.Map.keys outgoing)
    in
    let is_collapsible_edge =
      match FreeParams.get_dirt_polarity target params with
      | None -> true
      | _ -> false
    in
    if is_collapsible_edge then
      let constr = add_constraint target source constr in
      let contraction_data =
        {
          contraction_data with
          contraction_touched;
          changed = BaseSym.Set.add target changed;
        }
      in
      let contraction_data =
        if can_continue_on_graph then (
          (* All graph restructurings are done with assumption that target has no polarity -> is not present in type *)
          assert (FreeParams.get_dirt_polarity target params = None);
          (* Rewire edges *)
          let graph =
            graph
            |> G.remove_edges target outgoing (* remove edge fan *)
            |> G.remove_edge source target (* remove edge under contraction *)
            |> G.Edges.fold (* rewire edges *)
                 (fun out old_edge graph ->
                   (* If not all edges are the same, the edge label here is "wrong", we just keep it for bookkeeping purposes  *)
                   G.add_edge ~allow_duplicate:true source out old_edge graph)
                 outgoing
            |> G.remove_vertex_unsafe target
            (* Finally remove the target edge *)
          in
          (* Also update inverse graph *)
          let inverse_graph =
            inverse_graph
            |> G.Edges.fold
                 (fun out old_edge inverse_graph ->
                   (* Rewire fan *)
                   inverse_graph |> G.remove_edge out target
                   |> G.add_edge ~allow_duplicate:true out source old_edge)
                 outgoing
            |> G.remove_edge target source
            |> G.remove_vertex_unsafe target
          in
          let contraction_data =
            { contraction_data with graph; inverse_graph }
          in
          let new_cands = source :: BaseSym.Map.keys outgoing in
          Print.debug "new Candidates: %t"
            (Print.sequence "," BaseSym.print new_cands);
          recalculate_dirt_reduction_candidates contraction_data new_cands)
        else contraction_data
      in
      (constr, recalculate_dirt_reduction_candidates contraction_data [])
    else (constr, contraction_data)
  in
  let rec process data constr level =
    (* Print.debug "Indegs line: %t"
         (Print.sequence "," BaseSym.print (BaseSym.Set.elements indeg_line));
       Print.debug "Outdegs line: %t"
         (Print.sequence "," BaseSym.print (BaseSym.Set.elements outdeg_line)); *)
    (* Print.debug "Visited: %t"
         (Print.sequence "," BaseSym.print (BaseSym.Set.elements data.visited));
       Print.debug "Incoming: %t"
         (Print.sequence "," BaseSym.print
            (BaseSym.Set.elements data.candidates.incoming));
       Print.debug "Outgoing %t"
         (Print.sequence "," BaseSym.print
            (BaseSym.Set.elements data.candidates.outgoing)); *)
    if level <= 0 then assert false;
    match source_sink_candidate data with
    | Some (target, direction)
      when !Config.garbage_collect.dirt_contraction.contract_sink_nodes ->
        let data = invert_with_dir data direction in
        let constr, data = process_source_sink data direction target constr in
        let data = invert_with_dir data direction in
        process data constr (level - 1)
    | _ -> (
        match incoming_outgoing_candidate data with
        | Some (target, direction)
          when !Config.garbage_collect.dirt_contraction.contract_simple_nodes ->
            let data = invert_with_dir data direction in
            let constr, data =
              process_simple_node data direction target constr
            in
            let data = invert_with_dir data direction in
            process data constr (level - 1)
        | _ -> (constr, data))
  in
  process contraction_data Constraint.empty 1000

(* let join_simple_dirt_nodes { Language.Constraints.dirt_constraints; _ } params
    _level =
  let open Language.Constraints in
  let module BaseSym = Dirt.Param in
  let module G = DirtConstraints.DirtParamGraph in
  let has_trivial_solution param mode =
    match (FreeParams.get_dirt_polarity param params, mode) with
    | None, _ -> true
    | Some Positive, Outgoing -> true
    | Some Negative, Incoming -> true
    | _ -> false
  in

  let get_source_sink graph =
    let inverse_graph = G.reverse graph in
    let vertices = G.vertices graph in
    let sources, sinks =
      BaseSym.Set.fold
        (fun v (sources, sinks) ->
          ( sources
            |> BaseSym.Set.union
                 (if G.get_edges v inverse_graph |> BaseSym.Map.is_empty then
                  BaseSym.Set.singleton v
                 else BaseSym.Set.empty),
            sinks
            |> BaseSym.Set.union
                 (if G.get_edges v graph |> BaseSym.Map.is_empty then
                  BaseSym.Set.singleton v
                 else BaseSym.Set.empty) ))
        vertices
        (BaseSym.Set.empty, BaseSym.Set.empty)
    in
    (sources, sinks)
  in
  let increment v m =
    BaseSym.Map.update v (function None -> Some 1 | Some x -> Some (x + 1)) m
  in

  let get_indeg_outdeg_one graph =
    let inverse_graph = G.reverse graph in
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
    let get_ones (k, n) =
      assert (n <> 0);
      if n = 1 then Some k else None
    in
    let filter line =
      line |> BaseSym.Map.bindings |> List.filter_map get_ones
      |> BaseSym.Set.of_list
    in
    let indeg_line = filter indeg and outdeg_line = filter outdeg in
    (indeg_line, outdeg_line)
  in
  let join_dirt_component add_constraint add_empty_constraint
      add_full_constraint is_collapsible graph constr =
    (* We can assume that the graph is a DAG *)
    let indeg_line, outdeg_line = get_indeg_outdeg_one graph in
    let process_source_sink ?(mode = Outgoing) target
        (base_graph, reverse_graph) (visited, changed) =
      if has_trivial_solution target mode then (
        let visited = BaseSym.Set.add target visited in
        let out = G.get_edges target graph in
        let graph =
          graph |> G.remove_edges target out |> G.remove_vertex_unsafe target
        in
        assert (G.get_edges target reverse_graph |> G.Edges.cardinal = 0);
        ())
      else ()
    in
    let process_part_general ?(mode = "outgoing") target
        (indeg_line, outdeg_line) (base_graph, reverse_graph) (visited, changed)
        constr =
      (* Removing outging/incoming edges with degree 1 is practically the same but on different (reversed) graph
         The naming in this function assumes that the input graph is original graph and we are removing edges with
         exactly 1 incoming edge *)
      let remove_current_node_from_list = BaseSym.Set.remove target in
      let visited = BaseSym.Set.add target visited in
      Print.debug "Contracting drit, in mode %s, removing: %t" mode
        (BaseSym.print target);
      let incoming = G.get_edges target reverse_graph in
      assert (G.Edges.cardinal incoming = 1);
      let source, ((_, dirts) as edge) = G.Vertex.Map.choose incoming in
      let next = G.get_edges target base_graph in
      let only_empty =
        G.Edges.fold
          (fun to_ (_, drt) acc ->
            Print.debug "from me only_empty %t" (BaseSym.print to_);
            Effect.Set.is_empty drt && acc)
          next true
      in
      let all_edges_same =
        let l = G.Edges.fold (fun _ (_, drt) l -> drt :: l) next [] in
        match l with
        | [] -> false
        | x :: xs -> List.for_all (fun y -> Effect.Set.equal x y) xs
      in
      (* Check if outgoing edges strictly dominate this edge - only on outgoing *)
      let next_from_source =
        G.Vertex.Map.find_opt source reverse_graph
        |> Option.value ~default:BaseSym.Map.empty
      in
      let is_dominated =
        Effect.Set.subset dirts
          (G.Edges.fold
             (fun to_ (_, drt) ->
               Print.debug "from me %t" (BaseSym.print to_);
               Effect.Set.inter drt)
             next_from_source dirts)
        && mode = "outgoing"
        && (not (BaseSym.Map.is_empty next_from_source))
        && Effect.Set.is_empty dirts
        (* && _level = 2 *)
      in
      Print.debug "%b %b %b" (is_collapsible edge) only_empty is_dominated;
      let is_dominated = is_dominated in
      let can_continue_on_graph = all_edges_same && not is_dominated in
      if is_collapsible edge || is_dominated then
        let _ =
          Print.debug "Contracting drit, in mode %s, really removing: %t" mode
            (BaseSym.print target)
        in
        (* If all the rewired edges are simple, we can update graph, otherwise we have to re-solve and don't update graph just yet *)
        let (indeg_line, outdeg_line), (base_graph, reverse_graph) =
          (* if no graph invariants get broken, we do not need to resolve *)
          if can_continue_on_graph then
            let base_graph =
              if only_empty then
                base_graph
                |> G.remove_edge source target (* remove this edge *)
                |> G.Edges.fold (* rewire other edges *)
                     (fun next e acc ->
                       acc |> G.remove_edge target next
                       |> G.add_edge (* Triangels can produce duplicate edges *)
                            ~allow_duplicate:true source next e)
                     next
                |> G.remove_vertex_unsafe target
              else base_graph
            and reverse_graph =
              if only_empty then
                reverse_graph
                |> G.remove_edge target source
                |> G.Edges.fold (* rewire other edges *)
                     (fun next e acc ->
                       acc |> G.remove_edge next target
                       |> G.add_edge ~allow_duplicate:true next source e)
                     next
                |> G.remove_vertex_unsafe target
              else reverse_graph
            in
            let remove_edges base_graph line =
              line |> remove_current_node_from_list
              |> G.Edges.fold
                   (fun potential _ acc ->
                     let num =
                       base_graph |> G.get_edges potential |> G.Edges.cardinal
                     in
                     if num = 1 then acc |> BaseSym.Set.add potential
                     else acc |> BaseSym.Set.remove potential)
                   (next
                   |> G.Vertex.Map.map (fun _ -> ())
                   (* Treat source as any other *)
                   |> G.Edges.add_edge ~allow_duplicate:true source ())
            in
            let indeg_line = remove_edges reverse_graph indeg_line
            and outdeg_line = remove_edges base_graph outdeg_line in
            ((indeg_line, outdeg_line), (base_graph, reverse_graph))
          else ((indeg_line, outdeg_line), (base_graph, reverse_graph))
        in
        ( (indeg_line, outdeg_line),
          (base_graph, reverse_graph),
          (visited, BaseSym.Set.add target changed),
          add_constraint source target constr )
      else
        ( ( indeg_line |> remove_current_node_from_list,
            outdeg_line |> remove_current_node_from_list ),
          (base_graph, reverse_graph),
          (visited, changed),
          (* Do not contract constraints if the edge is not collapsible *)
          constr )
    in
    let rec process (indeg_line, outdeg_line) (graph, reverse_graph)
        (visited, changed) constr =
      let sources, sinks = get_source_sink graph in

      let indeg_line = BaseSym.Set.diff indeg_line visited in
      let outdeg_line = BaseSym.Set.diff outdeg_line visited in
      let sources = BaseSym.Set.diff sources visited in
      let sinks = BaseSym.Set.diff sinks visited in

      (* Print.debug "Indegs line: %t"
           (Print.sequence "," BaseSym.print (BaseSym.Set.elements indeg_line));
         Print.debug "Outdegs line: %t"
           (Print.sequence "," BaseSym.print (BaseSym.Set.elements outdeg_line)); *)
      match BaseSym.Set.choose_opt sources with
      | Some _ -> assert false
      | None -> (
          match BaseSym.Set.choose_opt sinks with
          | Some _ (* Don't optimize sinks for now *) | None -> (
              match BaseSym.Set.choose_opt indeg_line with
              | Some v ->
                  let ( (indeg_line, outdeg_line),
                        (graph, reverse_graph),
                        (visited, changed),
                        constr ) =
                    process_part_general v (indeg_line, outdeg_line)
                      (graph, reverse_graph) (visited, changed) constr
                  in
                  process (indeg_line, outdeg_line) (graph, reverse_graph)
                    (visited, changed) constr
              | _ -> (
                  match BaseSym.Set.choose_opt outdeg_line with
                  | Some v ->
                      let ( (outdeg_line, indeg_line),
                            (reverse_graph, graph),
                            (visited, changed),
                            constr ) =
                        process_part_general ~mode:"outgoing" v
                          (outdeg_line, indeg_line) (reverse_graph, graph)
                          (visited, changed) constr
                      in
                      process (indeg_line, outdeg_line) (graph, reverse_graph)
                        (visited, changed) constr
                  | _ ->
                      (* TODO: a bunch of asserts *)
                      (constr, changed))))
    in
    process (indeg_line, outdeg_line)
      (graph, G.reverse graph)
      (Dirt.Param.Set.empty, Dirt.Param.Set.empty)
      constr
  in
  join_dirt_component
    (fun p1 p2 ->
      Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.no_effect p2))
    (fun p1 -> Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.empty))
    (fun _p1 -> failwith "TODO")
    (fun (_, drt) -> Effect.Set.is_empty drt)
    dirt_constraints Constraint.empty *)

let calculate_lower_bound { Language.Constraints.dirt_constraints; _ }
    allow_contraction =
  (* Ths is a bad implementation of toposort, but it should work from now, to see, how it goes
     (at some point cycle detection should also sort it) *)
  let open Language.Constraints in
  let module BaseSym = Dirt.Param in
  let module G = DirtConstraints.DirtParamGraph in
  (* Toposort *)
  let components = G.scc_tarjan dirt_constraints in
  (* First combine multinodes *)
  let node_effects, parents, _component_parent =
    List.fold_left
      (fun (node_w, parents, component_parent) component ->
        match component with
        | top :: _ ->
            let effects, parents =
              List.fold
                (fun (effects, parents) start ->
                  (* Add parent node *)
                  let parents = BaseSym.Map.add start top parents in
                  let edges = G.get_edges start dirt_constraints in
                  (* loop over all outgoing in the same cycle *)
                  let effects =
                    List.fold
                      (fun effects target ->
                        let edge_effects =
                          edges |> G.Edges.get_edge target
                          |> Option.default_map Effect.Set.empty snd
                        in
                        Effect.Set.union effects edge_effects)
                      effects component
                  in
                  (effects, parents))
                (Effect.Set.empty, parents)
                component
            in
            (* add cycle effects to all nodes in this scc *)
            ( List.fold
                (fun acc v -> BaseSym.Map.add v effects acc)
                node_w component,
              parents,
              component_parent |> BaseSym.Map.add top component )
        | [] -> assert false)
      (BaseSym.Map.empty, BaseSym.Map.empty, BaseSym.Map.empty)
      components
  in
  (* Calculate lower bound for all nodes *)
  let lower_bounds = BaseSym.Map.empty in
  (* Traverse in topological sort order, and push all  *)
  let lower_bounds =
    List.fold_left
      (fun lower_bounds component ->
        let parent = List.hd component in
        let parent = BaseSym.Map.find parent parents in
        let component_lower_bound =
          match BaseSym.Map.find_opt parent lower_bounds with
          | Some lb -> lb
          | None -> Effect.Set.empty
        in
        let component_lower_bound =
          Effect.Set.union component_lower_bound
            (BaseSym.Map.find parent node_effects)
        in
        let lower_bounds =
          List.fold
            (fun lower_bounds v ->
              let edges = G.get_edges v dirt_constraints in
              let lower_bounds =
                BaseSym.Map.fold
                  (fun target (_, eff) lower_bounds ->
                    let pushed = Effect.Set.union eff component_lower_bound in
                    let target_parent = BaseSym.Map.find target parents in
                    let lower_bounds =
                      BaseSym.Map.update target_parent
                        (function
                          | None -> Some pushed
                          | Some existing ->
                              Some (Effect.Set.union existing pushed))
                        lower_bounds
                    in
                    lower_bounds)
                  edges lower_bounds
              in
              lower_bounds)
            lower_bounds component
        in
        lower_bounds)
      lower_bounds components
  in
  let constraints, change =
    G.fold
      (fun source target ((_, drt_set) as e) ((cons, _) as acc) ->
        let target_parent = BaseSym.Map.find target parents in
        let source_parent = BaseSym.Map.find source parents in
        if BaseSym.compare source target_parent = 0 then acc
        else if
          Effect.Set.subset drt_set
            (Option.value
               (BaseSym.Map.find_opt source_parent lower_bounds)
               ~default:Effect.Set.empty)
          && allow_contraction e
        then
          ( Constraint.add_dirt_equality
              (Dirt.no_effect source, Dirt.no_effect target)
              cons,
            true )
        else acc)
      dirt_constraints (Constraint.empty, false)
  in
  (constraints, change)

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

let optimize_constraints ~loc type_definitions subs constraints
    (get_counter, get_params) =
  let cycle_constraints = collapse_cycles constraints (get_params subs) in
  let subs', cycle_constraints' =
    Unification.unify ~loc type_definitions
      (subs, constraints, cycle_constraints)
  in
  let cycle_constraints' = Constraints.clean cycle_constraints' in
  Print.debug "Here: %t" (Constraints.print_dot cycle_constraints');
  let subs', constraints =
    if !Config.garbage_collect.type_contraction.contract_simple_nodes then
      let simple_one_constraints =
        join_simple_nodes cycle_constraints' (get_counter subs)
          (get_params subs)
      in
      let subs'', simple_one_constraints' =
        Unification.unify ~loc type_definitions
          ( subs |> Substitution.merge subs',
            cycle_constraints',
            simple_one_constraints )
      in
      (subs'', simple_one_constraints')
    else (subs', cycle_constraints')
  in
  let rec runner level subs_state cons_state =
    Print.debug "Contracting dirts on %d\n" level;
    Print.debug "(* Constraints graph before :\n %t \n*)"
      (Language.Constraints.print_dot ~param_polarity:(get_params subs_state)
         cons_state);
    let new_cons, contraction_state =
      join_simple_dirt_nodes cons_state (get_params subs_state) level
    in

    let subs_state', cons_state' =
      Unification.unify ~loc type_definitions (subs_state, cons_state, new_cons)
    in
    Print.debug "(* Constraints graph after :\n %t \n*)"
      (Language.Constraints.print_dot cons_state');
    let cons_state' = Constraints.clean cons_state' in
    if level >= 5 || Dirt.Param.Set.is_empty contraction_state.changed then
      (subs_state', cons_state')
    else runner (level + 1) subs_state' cons_state'
  in
  let subs', constraints = runner 0 subs' constraints in
  (subs', constraints)

let optimize_computation ~loc type_definitions subs constraints cmp =
  Print.debug "cmp: %t" (Term.print_computation cmp);

  optimize_constraints ~loc type_definitions subs constraints
    ( (fun subs ->
        let cmp = Term.apply_sub_comp subs cmp in
        let counter = score_computation cmp in
        let counter = multiply (-1.0) counter in
        counter),
      fun subs ->
        let cmp = Term.apply_sub_comp subs cmp in
        let parity = calculate_parity_dirty_ty cmp.ty in
        parity )

let optimize_top_let_rec ~loc type_definitions subs constraints defs =
  optimize_constraints ~loc type_definitions subs constraints
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
              FreeParams.union (calculate_parity_abs_ty abs.ty) acc)
            FreeParams.empty (Assoc.values_of defs)
        in
        counter )

(* 
if !Config.garbage_collect then
  let cycle_constraints = collapse_cycles constraints in
  let subs', cycle_constraints' =
    unify ~loc type_definitions (sub, constraints, cycle_constraints)
  in
  let cycle_constraints' = Constraints.clean cycle_constraints' in
  let simple_one_constraints = join_simple_nodes cycle_constraints' in
  let subs'', simple_one_constraints' =
    unify ~loc type_definitions
      ( sub |> Substitution.merge subs',
        cycle_constraints',
        simple_one_constraints )
  in
  let rec runner level subs_state cons_state =
    Print.debug "Contracting dirts on %d\n" level;
    Print.debug "(* Constraints graph before :\n %t \n*)"
      (Language.Constraints.print_dot cons_state);
    let new_cons, changed = join_simple_dirt_nodes cons_state level in
    (* Dont collect any lower bounds  *)
    let new_cons', ch = calculate_lower_bound cons_state (fun _ -> true) in

    let subs_state', cons_state' =
      unify ~loc type_definitions
        (subs_state, cons_state, new_cons |> Constraint.union new_cons')
    in

    Print.debug "(* Constraints graph after :\n %t \n*)"
      (Language.Constraints.print_dot cons_state');
    let cons_state' = Constraints.clean cons_state' in
    if level >= 10 || (Dirt.Param.Set.is_empty changed && not ch) then
      (subs_state', cons_state')
    else runner (level + 1) subs_state' cons_state'
  in
  let subs, constraints =
    runner 0
      (sub |> Substitution.merge subs' |> Substitution.merge subs'')
      simple_one_constraints'
  in
  (subs, constraints)
else (sub, constraints) *)
