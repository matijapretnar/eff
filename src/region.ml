module V = struct
  type t = Type.region_param
  let compare = Pervasives.compare
end

type elt = V.t

module S = Set.Make(struct
  type t = V.t
  let compare = V.compare
end)

module G = Map.Make(V)

type region_bound =
  | Without of Type.region_param * Type.region_param list
  | Instance of Type.instance_param

type t = (S.t * S.t) G.t * (Type.region_param, region_bound list) Common.assoc

let empty = (G.empty, [])

let get x (g) =
  try G.find x g with Not_found -> (S.empty, S.empty)

let get_succ x g =
  let (_, outx) = get x g in
  S.elements outx

let add_edge x y (g) =
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

let union (grph1, bnds1) (grph2, bnds2) =
  (G.fold G.add grph1 grph2,
    Common.assoc_map (Common.compose Common.uniq List.flatten) (Common.assoc_flatten (bnds1 @ bnds2)))

let subst_region_bound sbst = function
  | Without (p, rs) -> Without (sbst.Type.region_param p, List.map sbst.Type.region_param rs)
  | Instance i -> Instance (sbst.Type.instance_param i)

let add_region_bound r bnd (grph, bnds) =
  let succ = get_succ r grph in
  let new_bounds = List.map (fun r -> (r, bnd)) (r :: succ) in
  (grph, Common.assoc_map (Common.compose Common.uniq List.flatten) (Common.assoc_flatten (new_bounds @ bnds)))

let add_instance_constraint inst r =
  add_region_bound r [Instance inst]

let add_handled_constraint r1 r2 rs =
  add_region_bound r2 [Without (r1, rs)]

let add_region_constraint rgn1 rgn2 (grph, bnds) =
  let new_grph = add_edge rgn1 rgn2 grph in
  let new_cstr = (new_grph, bnds) in
  match Common.lookup rgn1 bnds with
  | None -> new_cstr
  | Some bnds -> add_region_bound rgn2 bnds new_cstr

let subst sbst (grph, bnds) =
  let f_set s = S.fold (fun x fs -> S.add (sbst.Type.region_param x) fs) s S.empty in
  let grph = G.fold (fun x (inx, outx) acc -> G.add (sbst.Type.region_param x) (f_set inx, f_set outx) acc) grph G.empty in
  let bnds = List.map (fun (r, bnd) -> (sbst.Type.region_param r, List.map (subst_region_bound sbst) bnd)) bnds in
  (grph, bnds)

let garbage_collect pos neg (grph, bnds) =
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
  let bnds = List.filter (fun (r, ds) -> S.mem r pos && ds != []) bnds in
  (G.fold collect grph G.empty, bnds)

let region_less ~non_poly r1 r2 ppf =
  Print.print ppf "%t %s %t" (Type.print_region_param ~non_poly r1) (Symbols.less ()) (Type.print_region_param ~non_poly r2)

let print_region_bounds ~non_poly bnds ppf =
  let print bnd ppf =
    match bnd with
    | Instance i -> Type.print_instance_param i ppf
    | Without (prs, rs) -> Print.print ppf "%t - [%t]" (Type.print_region_param ~non_poly prs) (Print.sequence ", " (Type.print_region_param ~non_poly) rs)
  in
  Print.sequence ", " print bnds ppf

let bounds ~non_poly r bnds ppf =
  match bnds with
  | [] -> ()
  | bnds -> Print.print ppf "%t %s %t" (print_region_bounds ~non_poly bnds) (Symbols.less ()) (Type.print_region_param ~non_poly r)

let print ~non_poly (g, bnds) ppf =
  let pps = fold_edges (fun r1 r2 lst -> if r1 != r2 then region_less ~non_poly r1 r2 :: lst else lst) g [] in
  let pps = List.fold_right (fun (r, bnds) lst -> if bnds != [] then bounds ~non_poly r bnds :: lst else lst) bnds pps in
  if pps != [] then
    Print.print ppf " | %t" (Print.sequence "," Common.id pps)

let pos_handled pos neg (grph, bnds) =
  []
(* 
   let add_region_bound bnd (posi, nega) = match bnd with
  | Region.Without (r, rs) -> (([], [], r :: rs) @@@ posi, nega)
  | Region.Instance _ -> (posi, nega)
  in
  let (((_, _, pos_rs) as posi), nega) = (Trio.uniq pos, Trio.uniq neg) in
  let (posi, nega) = List.fold_right (fun (d, bnds) (posi, nega) ->
                                      if List.mem d pos_rs then List.fold_right add_region_bound bnds (posi, nega) else (posi, nega)) cnstrs.Constraints.region_bounds (posi, nega) in
 *)
