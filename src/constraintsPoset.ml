module type Vertex =
sig
  type t
  val compare : t -> t -> int
end

module Make (V : Vertex) =
struct
  type elt = V.t

  module S = Set.Make(struct
    type t = V.t
    let compare = V.compare
  end)

  module G = Map.Make(V)

  type t = ((S.t * S.t) G.t) list

  let empty = []

  let get_aux x g =
    try G.find x g with Not_found -> (S.empty, S.empty)

  let keys g =
    List.map fst (G.bindings g)

  let skeletons g =
    List.map keys g

  let mem x g =
    try ignore (G.find x g); true with Not_found -> false

  let get_prec_aux x g =
    let (inx, _) = get_aux x g in
    S.elements inx

  let union = G.fold G.add

  let add_edge_aux x y g =
    if x = y then g else
    let (inx, outx) = get_aux x g
    and (iny, outy) = get_aux y g in
    let left = S.add x (S.diff inx iny)
    and right = S.add y (S.diff outy outx) in
    let extend_left l grph =
      let (inl, outl) = get_aux l grph in
      G.add l (inl, S.union outl (S.remove l right)) grph
    and extend_right r grph =
      let (inr, outr) = get_aux r grph in
      G.add r (S.union inr (S.remove r left), outr) grph in
    S.fold extend_left left (S.fold extend_right right g)

  let add_edge ty1 ty2 g =
    let within, without = List.partition (fun g -> mem ty1 g || mem ty2 g) g in
    match within with
    | [] -> (add_edge_aux ty1 ty2 G.empty) :: without
    | [g] -> (add_edge_aux ty1 ty2 g) :: without
    | [g1; g2] -> (add_edge_aux ty1 ty2 (union g1 g2)) :: without
    | _ -> assert false

  let get_prec x g =
    let rec get = function
    | [] -> []
    | g :: gs ->
        if mem x g then
          get_prec_aux x g
        else
          get gs
    in
    get g

  let fold_edges f grph acc =
    G.fold (fun x (_, outx) acc -> S.fold (fun y acc -> f x y acc) outx acc) grph acc

  let map_aux f grph =
    let f_set s = S.fold (fun x fs -> S.add (f x) fs) s S.empty in
    G.fold (fun x (inx, outx) acc -> G.add (f x) (f_set inx, f_set outx) acc) grph G.empty

  let map f grph = List.map (map_aux f) grph

  let remove_skeleton p grph =
    let rec remove unremoved = function
    | [] -> (G.empty, unremoved)
    | g :: gs ->
        if mem p g then
          (g, unremoved @ gs)
        else
          remove (g :: unremoved) gs
    in
    let (skel, new_grph) = remove [] grph in
    let ps = Common.uniq (p :: keys skel) in
    let rest = fold_edges (fun p q acc -> (p, q) :: acc) skel [] in
    (new_grph, ps, rest)

  let garbage_collect pos neg grph =
    let pos = List.fold_right S.add pos S.empty
    and neg = List.fold_right S.add neg S.empty in
    let collect_aux grph =
      let collect x (inx, outx) grph =
        let inx =
          if S.mem x pos then S.inter neg inx else S.empty
        and outx =
          if S.mem x neg then S.inter pos outx else S.empty
        in
        if S.cardinal inx + S.cardinal outx = 0 then
         grph
        else
          G.add x (inx, outx) grph
      in
      G.fold collect grph G.empty
    in
    List.filter (fun g -> g <> G.empty) (List.map collect_aux grph)

  let union grph1 grph2 = Common.uniq (grph1 @ grph2)

end
