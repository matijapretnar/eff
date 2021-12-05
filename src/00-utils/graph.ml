module MakeEdges (Vertex : Symbol.S) = struct
  type 'a t = 'a Vertex.Map.t

  let empty = Vertex.Map.empty

  let get_edge t edges = Vertex.Map.find_opt t edges

  let add_edge t w edges = Vertex.Map.add t w edges

  let fold f edges acc = Vertex.Map.fold f edges acc
end

module Make (Vertex : Symbol.S) = struct
  module Edges = MakeEdges (Vertex)

  type 'a t = 'a Edges.t Vertex.Map.t

  let empty = Vertex.Map.empty

  let is_empty = Vertex.Map.is_empty

  let get_edges t graph =
    Vertex.Map.find_opt t graph |> Option.value ~default:Edges.empty

  let add_edge v1 v2 e graph =
    let v1_edges' = get_edges v1 graph |> Edges.add_edge v2 e in
    Vertex.Map.add v1 v1_edges' graph

  let fold f graph acc = Vertex.Map.fold (fun v -> Edges.fold (f v)) graph acc
end
