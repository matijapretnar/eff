module type Vertex =
sig
  type t
  val compare : t -> t -> int
end

module Make (V : Vertex) =
  (* XXX Change the [V] signature so that [Common.position] is a parameter. 
     Also add printers for vertices to [V] so that the module can export printing of a graph. *)
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

  let add_vertex x (g : t) =
    if G.mem x g then g else G.add x (S.empty, S.empty) g

  let remove_vertex x (g : t) =
    (* We must remove [x] as a key from [g], as well as an element of any in- our out-set *)
    let remove_x = S.filter (fun y -> x <> y) in
    (* XXX What do we do about lower and upper bounds of the discarded vertex? *)
    let (inx, outx) = get x g in
      S.elements inx, S.elements outx,
      G.fold
        (fun y (iny, outy) g -> G.add y (remove_x iny, remove_x outy) g)
        (G.remove x g)
        G.empty

  let fold_edges f grph acc =
    G.fold (fun x (_, outx) acc -> S.fold (fun y acc -> f x y acc) outx acc) grph acc
  let fold_vertices f grph acc =
    G.fold (fun x (inx, outx) acc -> f x (S.elements inx) (S.elements outx) acc) grph acc

  let union = G.fold G.add

  let leaves grph =
    G.fold (fun x (inx, outx) acc -> if S.is_empty inx then x :: acc else acc) grph []

  let filter_edges p grph =
    let g = G.fold (fun x (inx, outx) acc -> G.add x (S.empty, S.empty) acc) grph G.empty in
    fold_edges (fun x y acc -> if p x y then add_edge x y acc else acc) grph g

  let map f grph =
    let f_set s = S.fold (fun x fs -> S.add (f x) fs) s S.empty in
    G.fold (fun x (inx, outx) acc -> G.add (f x) (f_set inx, f_set outx) acc) grph G.empty

  let garbage_collect pos neg grph =
    let pos = List.fold_right S.add pos S.empty
    and neg = List.fold_right S.add neg S.empty in
    let collect x (inx, outx) grph =
      let x_pos = S.mem x pos
      and x_neg = S.mem x neg in
      let inx = if x_pos then S.inter neg inx else S.empty
      and outx = if x_neg then S.inter pos outx else S.empty in
      match S.cardinal inx + S.cardinal outx with
      | 0 -> grph
      | _ -> G.add x (inx, outx) grph
    in
    G.fold collect grph G.empty

  let simplify pos neg grph =
    let add x (inx, outx) sbst =
      if List.mem x pos && S.cardinal inx = 1 then (x, S.choose inx) :: sbst
      else if List.mem x neg && S.cardinal outx = 1 then (x, S.choose outx) :: sbst
      else sbst
    and collect_substitution (x, y) (used, sbst) =
      if List.mem y used then
        used, sbst
      else
        (x :: used), (x, y) :: sbst
    in
    let sbst = G.fold add grph [] in
    let _, sbst = List.fold_right collect_substitution sbst ([], []) in
    sbst
 (*    let print grph ppf =
      fold_vertices
        (fun x inx outx () ->
          Print.print ppf "@[%t <= %t <= %t@];@."
            (Print.sequence ", " V.print (List.map fst inx))
            (V.print x)
            (Print.sequence ", " V.print (List.map fst outx))
        )
        grph () *)
end