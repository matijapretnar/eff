module MakeEdges (Vertex : Symbol.S) = struct
  type 'a t = 'a Vertex.Map.t

  let empty = Vertex.Map.empty

  let get_edge t edges = Vertex.Map.find_opt t edges

  let add_edge t w edges = Vertex.Map.add t w edges

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

  let print_node node ppf =
    let vertex = Vertex.print node in
    Print.print ppf "node_%t[label=\"%t\"];" vertex vertex

  let print_edge (v1, edge, v2) ppf =
    Print.print ppf "@[<h>node_%t -> node_%t [label=\"%t\"]@]" (Vertex.print v1)
      (Vertex.print v2) (Edge.print edge)

  let print_dot graph cluster_name header ppf =
    let vertices, edges =
      fold
        (fun source sink edge (vertices, edges) ->
          ( vertices |> Vertex.Set.add source |> Vertex.Set.add sink,
            (source, edge, sink) :: edges ))
        graph (Vertex.Set.empty, [])
    in
    let vertices = Vertex.Set.elements vertices in
    Print.print ppf "subgraph %t{\n%t\n//nodes\n%t\n\n//edges\n%t\n\n}\n"
      cluster_name header
      (Print.sequence "\n" print_node vertices)
      (Print.sequence "\n" print_edge edges)
end
