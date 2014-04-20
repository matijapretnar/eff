type elt = Type.region_param

module Instances = Map.Make(struct
  type t = Type.instance_param * Type.region_param
  let compare = Pervasives.compare
end)

module Regions = Map.Make(struct
  type t = Type.region_param * Type.region_param
  let compare = Pervasives.compare
end)

module HandledRegions = Set.Make(struct
  type t = Type.region_param
  let compare = Pervasives.compare
end)

type t = {
  instances: (HandledRegions.t list) Instances.t;
  regions: (HandledRegions.t list) Regions.t
}

let empty = {
  instances = Instances.empty;
  regions = Regions.empty;
}

let union bnds1 bnds2 = {
  instances = Instances.fold Instances.add bnds1.instances bnds2.instances;
  regions = Regions.fold Regions.add bnds1.regions bnds2.regions;
}

let subst_handled_regions sbst =
  let add r rs' = HandledRegions.add (sbst.Type.region_param r) rs' in
  List.map (fun rs -> HandledRegions.fold add rs HandledRegions.empty)

let subst_instances sbst ibnds =
  let add (i, r) rs ibnds' =
    Instances.add (sbst.Type.instance_param i, sbst.Type.region_param r) (subst_handled_regions sbst rs) ibnds' in
  Instances.fold add ibnds Instances.empty

let subst_regions sbst rbnds =
  let add (i, r) rs rbnds' =
    Regions.add (sbst.Type.region_param i, sbst.Type.region_param r) (subst_handled_regions sbst rs) rbnds' in
  Regions.fold add rbnds Regions.empty

let subst sbst bnds = {
  instances = subst_instances sbst bnds.instances;
  regions = subst_regions sbst bnds.regions;
}

let garbage_collect pos neg bnds =
  {
    instances =
      Instances.filter
      (fun (_, r) bnds -> List.mem r pos && bnds != [])
      bnds.instances;
    regions =
      Regions.filter
      (fun (r1, r2) bnds -> r1 != r2 && List.mem r1 neg && List.mem r2 pos && bnds != [])
      bnds.regions;
  }

let pos_handled pos neg bnds =
  let add _ = List.fold_right HandledRegions.union in
  let pos' = Instances.fold add bnds.instances (Regions.fold add bnds.regions HandledRegions.empty) in
  HandledRegions.elements pos'

let add_handled rs =
  let rec add = function
  | [] -> [rs]
  | rs' :: rss ->
    if HandledRegions.subset rs' rs then rs' :: rss
    else if HandledRegions.subset rs rs' then add rss
    else rs' :: add rss
  in
  add

let double_fold f xs ys acc =
  List.fold_right (fun x acc ->
    List.fold_right (fun y acc ->
      f x y acc
    ) ys acc
  ) xs acc

let add_region_constraint r1 r2 rs bnds =
  let rs = List.fold_right HandledRegions.add rs HandledRegions.empty in
  let l_rbnds =
    Regions.fold
    (fun (r, r1') rss l_rbnds -> if r1' = r1 then (r, rss) :: l_rbnds else l_rbnds)
    bnds.regions [(r1, [HandledRegions.empty])]
  and r_rbnds =
    Regions.fold
    (fun (r2', r) rss r_rbnds -> if r2' = r2 then (r, rss) :: r_rbnds else r_rbnds)
    bnds.regions [(r2, [HandledRegions.empty])]
  and ibnds =
    Instances.fold
    (fun (i, r1') rss ibnds -> if r1' = r1 then (i, rss) :: ibnds else ibnds)
    bnds.instances []
  in
  let add_ibnd (i, rss1') (r2', rss2') ibnds =
    let rss =
      try Instances.find (i, r2') bnds.instances
      with Not_found -> []
    in
    let add rs1' rs2' ibnds =
      let rs' = HandledRegions.union rs1' (HandledRegions.union rs rs2') in
      Instances.add (i, r2') (add_handled rs' rss) ibnds
    in
    double_fold add rss1' rss2' ibnds
  in
  let add_rbnd (r1', rss1') (r2', rss2') rbnds =
    let rss =
      try Regions.find (r1', r2') bnds.regions
      with Not_found -> []
    in
    let add rs1' rs2' rbnds =
      let rs' = HandledRegions.union rs1' (HandledRegions.union rs rs2') in
      Regions.add (r1', r2') (add_handled rs' rss) rbnds
    in
    double_fold add rss1' rss2' rbnds
  in
  {
    instances = double_fold add_ibnd ibnds r_rbnds bnds.instances;
    regions = double_fold add_rbnd l_rbnds r_rbnds bnds.regions
  }

let add_instance_constraint i r2 rs bnds =
  let rs = List.fold_right HandledRegions.add rs HandledRegions.empty in
  let r_rbnds =
    Regions.fold
    (fun (r2', r) rss r_rbnds -> if r2' = r2 then (r, rss) :: r_rbnds else r_rbnds)
    bnds.regions [(r2, [HandledRegions.empty])]
  in
  let add_ibnd (r2', rss2') ibnds =
    let rss =
      try Instances.find (i, r2') bnds.instances
      with Not_found -> []
    in
    let add rs2' ibnds =
      let rs' = HandledRegions.union rs rs2' in
      Instances.add (i, r2') (add_handled rs' rss) ibnds
    in
    List.fold_right add rss2' ibnds
  in
  {
    instances = List.fold_right add_ibnd r_rbnds bnds.instances;
    regions = bnds.regions
  }

let print_removed_regions ~non_poly rs ppf =
  if HandledRegions.is_empty rs then
    Print.print ppf ""
  else
    let rs = HandledRegions.elements rs in
    Print.print ppf "- %t" (Print.sequence " - " (Type.print_region_param ~non_poly) rs)

let print_instance_bound ~non_poly i r rs ppf =
  Print.print ppf "%t%t %s %t" (Type.print_instance_param i) (print_removed_regions ~non_poly rs) (Symbols.less ()) (Type.print_region_param ~non_poly r)

let print_region_bound ~non_poly r1 r2 rs ppf =
  Print.print ppf "%t%t %s %t" (Type.print_region_param r1) (print_removed_regions ~non_poly rs) (Symbols.less ()) (Type.print_region_param ~non_poly r2)

let print ~non_poly bnds ppf =
  let pps = Regions.fold (
    fun (r1, r2) ->
      List.fold_right (fun rs pps -> print_region_bound ~non_poly r1 r2 rs :: pps)
  ) bnds.regions [] in
  let pps = Instances.fold (
    fun (i, r) ->
      List.fold_right (fun rs pps -> print_instance_bound ~non_poly i r rs :: pps)
  ) bnds.instances pps in
  if pps = [] then () else
  Print.print ppf " |@,@[%t@]" (Print.sequence "," Common.id pps)

