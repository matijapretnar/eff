module MakeEdges (Vertex : Symbol.S) = struct
  type 'a t = 'a Vertex.Map.t

  let empty = Vertex.Map.empty
  let get_edge t edges = Vertex.Map.find_opt t edges

  let add_edge t w edges =
    Vertex.Map.update t
      (function None -> Some w | Some _ -> assert false)
      edges

  let fold f edges acc = Vertex.Map.fold f edges acc
end

module Make
    (Vertex : Symbol.S) (Edge : sig
      type t

      val print : ?safe:bool -> t -> Format.formatter -> unit
    end) =
struct
  module Edges = MakeEdges (Vertex)

  type t = Edge.t Edges.t Vertex.Map.t

  let empty = Vertex.Map.empty
  let is_empty = Vertex.Map.is_empty

  let get_edges t graph =
    Vertex.Map.find_opt t graph |> Option.value ~default:Edges.empty

  let add_edge v1 v2 e graph =
    let v1_edges' = get_edges v1 graph |> Edges.add_edge v2 e in
    Vertex.Map.add v1 v1_edges' graph

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

  let print_node node ppf =
    let vertex = Vertex.print node in
    Print.print ppf "node_%t[label=\"%t\"];" vertex vertex

  let print_edge (v1, edge, v2) ppf =
    Print.print ppf "@[<h>node_%t -> node_%t [label=\"%t\"]@]" (Vertex.print v1)
      (Vertex.print v2) (Edge.print edge)

  let print_node_component cluster_name (ind, cmp) ppf =
    if Vertex.Set.cardinal cmp = 1 then
      Print.print ppf "%t" (print_node (Vertex.Set.choose cmp))
    else
      Print.print ppf
        "subgraph cluster_%t_%d {label=\"\"; graph[style=dotted]; \n %t \n}"
        cluster_name ind
        (Print.sequence "\n" print_node (Vertex.Set.elements cmp))

  let print_dot graph cluster_name header ppf =
    let _vertices, edges =
      fold
        (fun source sink edge (vertices, edges) ->
          ( vertices |> Vertex.Set.add source |> Vertex.Set.add sink,
            (source, edge, sink) :: edges ))
        graph (Vertex.Set.empty, [])
    in
    let components = scc graph in
    (* let vertices = Vertex.Set.elements vertices in *)
    Print.print ppf "subgraph %t{\n%t\n//nodes\n%t\n\n//edges\n%t\n\n}\n"
      cluster_name header
      (Print.sequence "\n"
         (print_node_component cluster_name)
         (List.mapi (fun x i -> (x, i)) components))
      (Print.sequence "\n" print_edge edges)
end
