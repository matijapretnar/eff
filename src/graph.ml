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

  type t = (S.t * S.t) G.t

  let empty = G.empty

  let get x (g : t) =
    try G.find x g with Not_found -> (S.empty, S.empty)

  let keys g =
    List.map fst (G.bindings g)

  let mem x (g : t) =
    try ignore (G.find x g); true with Not_found -> false

  let get_succ x g =
    let (_, outx) = get x g in
    S.elements outx

  let get_prec x g =
    let (inx, _) = get x g in
    S.elements inx

  let add_edge x y (g : t) =
    if x = y then g else
    let (inx, outx) = get x g
    and (iny, outy) = get y g in
    let left = S.add x (S.diff inx iny)
    and right = S.add y (S.diff outy outx) in
    let extend_left l grph =
      let (inl, outl) = get l grph in
      G.add l (inl, S.union outl (S.remove l right)) grph
    and extend_right r grph =
      let (inr, outr) = get r grph in
      G.add r (S.union inr (S.remove r left), outr) grph in
    S.fold extend_left left (S.fold extend_right right g)

  let fold_edges f grph acc =
    G.fold (fun x (_, outx) acc -> S.fold (fun y acc -> f x y acc) outx acc) grph acc

  let union = G.fold G.add

  let map f grph =
    let f_set s = S.fold (fun x fs -> S.add (f x) fs) s S.empty in
    G.fold (fun x (inx, outx) acc -> G.add (f x) (f_set inx, f_set outx) acc) grph G.empty

  let garbage_collect pos neg grph =
    let pos = List.fold_right S.add pos S.empty
    and neg = List.fold_right S.add neg S.empty in
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

end
