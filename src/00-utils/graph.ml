module MakeEdges (Vertex : Symbol.S) = struct
  type 'a t = 'a Vertex.Map.t

  let empty = Vertex.Map.empty
  let get_edge t edges = Vertex.Map.find_opt t edges

  let add_edge ?(allow_duplicate = false) t w edges =
    Vertex.Map.update t
      (function
        | None -> Some w
        | Some v ->
            if not allow_duplicate then assert false;
            Some v)
      edges

  let remove_edge v2 edges =
    Vertex.Map.update v2
      (function None -> assert false | Some _ -> None)
      edges

  let fold f edges acc = Vertex.Map.fold f edges acc

  let cardinal g = Vertex.Map.cardinal g

  let vertices = Vertex.Map.keys

  let edges = Vertex.Map.values
end

module Make
    (Vertex : Symbol.S) (Edge : sig
      type t

      val print : ?safe:bool -> t -> Format.formatter -> unit
    end) =
struct
  module Vertex = Vertex
  module Edges = MakeEdges (Vertex)

  type t = Edge.t Edges.t Vertex.Map.t

  let empty = Vertex.Map.empty
  let is_empty = Vertex.Map.is_empty

  let get_edges t graph =
    Vertex.Map.find_opt t graph |> Option.value ~default:Edges.empty

  let add_edge ?(allow_duplicate = false) v1 v2 e graph =
    let v1_edges' =
      get_edges v1 graph |> Edges.add_edge ~allow_duplicate v2 e
    in
    Vertex.Map.add v1 v1_edges' graph

  let remove_edge v1 v2 graph =
    let v1_edges' = get_edges v1 graph |> Edges.remove_edge v2 in
    Vertex.Map.add v1 v1_edges' graph

  let remove_edges v edges (graph : t) : t =
    Vertex.Map.fold (fun v2 _ graph -> remove_edge v v2 graph) edges graph

  let remove_vertex_unsafe v graph = Vertex.Map.remove v graph

  let fold f graph acc = Vertex.Map.fold (fun v -> Edges.fold (f v)) graph acc

  let vertices graph =
    let vertices =
      fold
        (fun source sink _ vertices ->
          vertices |> Vertex.Set.add source |> Vertex.Set.add sink)
        graph Vertex.Set.empty
    in
    vertices

  let reverse graph =
    fold
      (fun source sink edge -> add_edge sink source edge)
      graph Vertex.Map.empty

  let traverse source graph =
    let rec traverse' visited source =
      let edges = get_edges source graph in
      Edges.fold
        (fun target _ visited ->
          if Vertex.Set.mem target visited then visited
          else traverse' (visited |> Vertex.Set.add target) target)
        edges visited
    in
    traverse' (Vertex.Set.singleton source) source

  let component graph reverse source =
    Vertex.Set.inter (traverse source graph) (traverse source reverse)

  let scc_tarjan graph =
    let rec strong_connect (v_index, v_lowlink, stack, on_stack, index) v =
      let v_index =
        Vertex.Map.update v
          (function None -> Some index | Some _ -> assert false)
          v_index
      in
      let v_lowlink = Vertex.Map.add v index v_lowlink in

      let index = index + 1 in
      let on_stack = on_stack |> Vertex.Set.add v in
      let stack = v :: stack in
      (* Loop over all successors *)
      let v_index, v_lowlink, stack, on_stack, index, components =
        Edges.fold
          (fun to_ _ (v_index, v_lowlink, stack, on_stack, index, components) ->
            if Vertex.Map.find_opt to_ v_index = None then
              let v_index, v_lowlink, stack, on_stack, index, components' =
                strong_connect (v_index, v_lowlink, stack, on_stack, index) to_
              in
              let components = components' @ components in
              let v_lowlink =
                Vertex.Map.update to_
                  (function
                    | None -> assert false
                    | Some lowlink ->
                        Some (min lowlink (Vertex.Map.find v v_lowlink)))
                  v_lowlink
              in
              (v_index, v_lowlink, stack, on_stack, index, components)
            else if Vertex.Set.mem to_ on_stack then
              let v_lowlink =
                Vertex.Map.update to_
                  (function
                    | None -> assert false
                    | Some lowlink ->
                        Some (min lowlink (Vertex.Map.find v v_lowlink)))
                  v_lowlink
              in
              (v_index, v_lowlink, stack, on_stack, index, components)
            else (v_index, v_lowlink, stack, on_stack, index, components))
          (get_edges v graph)
          (v_index, v_lowlink, stack, on_stack, index, [])
      in
      (* Check lowlink invariants *)
      let on_stack, component, stack =
        if Vertex.Map.find v v_index = Vertex.Map.find v v_lowlink then
          let rec popper on_stack component stack =
            match stack with
            | top :: rest ->
                let on_stack = Vertex.Set.remove top on_stack in
                let component = top :: component in
                if Vertex.compare top v = 0 then (on_stack, component, rest)
                else popper on_stack component rest
            | [] -> (on_stack, component, stack)
          in
          let on_stack, component, stack = popper on_stack [] stack in
          (on_stack, [ component ], stack)
        else (on_stack, [], stack)
      in
      assert (List.length component <= 1);

      (v_index, v_lowlink, stack, on_stack, index, component @ components)
    in
    let v_index = Vertex.Map.empty in
    let v_lowlink = v_index in
    let on_stack = Vertex.Set.empty in
    let _, _, stack, on_stack, index, components =
      Vertex.Set.fold
        (fun v ((v_index, v_lowlink, stack, on_stack, index, components) as acc) ->
          match Vertex.Map.find_opt v v_index with
          | None ->
              let v_index, v_lowlink, stack, on_stack, index, components' =
                strong_connect (v_index, v_lowlink, stack, on_stack, index) v
              in
              ( v_index,
                v_lowlink,
                stack,
                on_stack,
                index,
                components' @ components )
          | Some _ -> acc)
        (vertices graph)
        (v_index, v_lowlink, [], on_stack, 0, [])
    in
    assert (stack = []);
    assert (Vertex.Set.is_empty on_stack);
    assert (index = (graph |> vertices |> Vertex.Set.cardinal));
    assert (
      components |> List.map List.length |> List.fold ( + ) 0
      = (graph |> vertices |> Vertex.Set.cardinal));
    components

  let scc graph =
    let reversed = reverse graph in
    let visited = Vertex.Set.empty in
    let components = [] in
    let _, components =
      Vertex.Set.fold
        (fun source (visited, components) ->
          if Vertex.Set.mem source visited then (visited, components)
          else
            let c = component graph reversed source in
            (visited |> Vertex.Set.union c, c :: components))
        (vertices graph) (visited, components)
    in
    (* TODO: a bunch of asserts *)
    List.iter (fun cmp -> assert (Vertex.Set.cardinal cmp >= 1)) components;
    let all = List.fold_right Vertex.Set.union components Vertex.Set.empty in
    assert (Vertex.Set.equal all (vertices graph));
    (*  *)
    components

  let toposort graph =
    let permanent = Vertex.Set.empty in
    let temp = Vertex.Set.empty in
    let l = [] in
    let rec visit n (temp, permanent, l) =
      if Vertex.Set.mem n permanent then (temp, permanent, l)
      else (
        (* Check for cycle -> Should not happen *)
        assert (Vertex.Set.mem n temp |> not);

        let temp = Vertex.Set.add n temp in
        let outgoing = graph |> Vertex.Map.find n in
        let temp, permanent, l =
          Vertex.Set.fold
            (fun m (temp, permanent, l) -> visit m (temp, permanent, l))
            outgoing (temp, permanent, l)
        in
        let temp = Vertex.Set.remove n temp in
        let permanent = Vertex.Set.add n permanent in
        (temp, permanent, n :: l))
    in
    let _, _, l =
      Vertex.Map.fold
        (fun f _ (temp, permanent, l) ->
          if Vertex.Set.mem f permanent then (temp, permanent, l)
          else visit f (temp, permanent, l))
        graph (temp, permanent, l)
    in
    l

  let print_node additonal_label node ppf =
    let vertex = Vertex.print node in
    let additional_label = additonal_label node in
    Print.print ppf "node_%t[label=\"%t%s\"];" vertex vertex additional_label

  let print_edge (v1, edge, v2) ppf =
    Print.print ppf "@[<h>node_%t -> node_%t [label=\"%t\"]@]" (Vertex.print v1)
      (Vertex.print v2) (Edge.print edge)

  let print_node_component cluster_name additional_label (ind, cmp) ppf =
    if Vertex.Set.cardinal cmp = 1 then
      Print.print ppf "%t" (print_node additional_label (Vertex.Set.choose cmp))
    else
      Print.print ppf
        "subgraph cluster_%t_%d {label=\"\"; graph[style=dotted]; \n %t \n}"
        cluster_name ind
        (Print.sequence "\n"
           (print_node additional_label)
           (Vertex.Set.elements cmp))

  let print_dot additional_label graph cluster_name header ppf =
    let additional_label =
      match additional_label with None -> fun _ -> "" | Some f -> f
    in
    let _vertices, edges =
      fold
        (fun source sink edge (vertices, edges) ->
          ( vertices |> Vertex.Set.add source |> Vertex.Set.add sink,
            (source, edge, sink) :: edges ))
        graph (Vertex.Set.empty, [])
    in
    let components = scc graph in
    Print.print ppf "subgraph %t{\n%t\n//nodes\n%t\n\n//edges\n%t\n\n}\n"
      cluster_name header
      (Print.sequence "\n"
         (print_node_component cluster_name additional_label)
         (List.mapi (fun x i -> (x, i)) components))
      (Print.sequence "\n" print_edge edges)
end
