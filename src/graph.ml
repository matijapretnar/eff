module type Vertex =
sig
  type t
  type bound
  val sup : bound -> bound -> bound
  val inf : bound -> bound -> bound
  val compare : t -> t -> int
  val print : t -> Format.formatter -> unit
end

module Make (V : Vertex) =
  (* XXX Change the [V] signature so that [Common.position] is a parameter. 
     Also add printers for vertices to [V] so that the module can export printing of a graph. *)
struct
  type elt = V.t

  module S = Set.Make(struct
    type t = V.t * Common.position
    let compare (x, _) (y, _) = V.compare x y
  end)

  module G = Map.Make(V)

  type t = (S.t * S.t * V.bound option * V.bound option) G.t

  let empty = G.empty

  let sup x y = match x, y with
    | None, _ -> y
    | _, None -> x
    | Some x, Some y -> Some (V.sup x y)

  let inf x y = match x, y with
    | None, _ -> y
    | _, None -> x
    | Some x, Some y -> Some (V.inf x y)

  let get x (g : t) =
    try G.find x g with Not_found -> (S.empty, S.empty, None, None)

  let add_edge x y pos (g : t) =
    let (inx, outx, infx, supx) = get x g in
    let (iny, outy, infy, supy) = get y g in
      G.add x (inx, S.add (y, pos) outx, infx, inf supx supy) (G.add y (S.add (x, pos) iny, outy, sup infx infy, supy) g)

  let add_vertex x (g : t) =
    if G.mem x g then g else G.add x (S.empty, S.empty, None, None) g

  let remove_vertex x (g : t) =
    (* We must remove [x] as a key from [g], as well as an element of any in- our out-set *)
    let remove_x = S.filter (fun (y, _) -> x <> y) in
    (* XXX What do we do about lower and upper bounds of the discarded vertex? *)
    let (inx, outx, _, _) = get x g in
      S.elements inx, S.elements outx,
      G.fold
        (fun y (iny, outy, infy, supy) g -> G.add y (remove_x iny, remove_x outy, infy, supy) g)
        (G.remove x g)
        G.empty

  let fold_edges f grph acc =
    G.fold (fun x (_, outx, _, _) acc -> S.fold (fun (y, pos) acc -> f x y pos acc) outx acc) grph acc

  let fold_vertices f grph acc =
    G.fold (fun x (inx, outx, _, _) acc -> f x (S.elements inx) (S.elements outx) acc) grph acc

  let filter_edges p grph =
    fold_edges (fun x y pos acc -> if p x y pos then add_edge x y pos acc else acc) grph G.empty

  let transitive_closure grph =
    let add_closure_edges x y pos closure =
      let (inx, outx, _, _) = get x closure
      and (iny, outy, _, _) = get y closure in
      let left = S.add (x, pos) (S.diff inx iny)
      and right = S.add (y, pos) (S.diff outy outx) in
        S.fold (fun (x', _) grph ->
          S.fold (fun (y', _) grph ->
            add_edge x' y' pos grph
            ) right grph
          ) left closure
    in
    fold_edges add_closure_edges grph G.empty

    let print grph ppf =
      fold_vertices
        (fun x inx outx () ->
          Print.print ppf "@[%t <= %t <= %t@];@."
            (Print.sequence "," V.print (List.map fst inx))
            (V.print x)
            (Print.sequence "," V.print (List.map fst outx))
        )
        grph ()
end