type ty_param = Ty_Param of int
type dirt_param = Dirt_Param of int
type region_param = Region_Param of int

let fresh_ty_param = Common.fresh (fun n -> Ty_Param n)
let fresh_dirt_param = Common.fresh (fun n -> Dirt_Param n)
let fresh_region_param = Common.fresh (fun n -> Region_Param n)

type t = ty_param list * dirt_param list * region_param list

let empty = ([], [], [])
let append (ts1, ds1, rs1) (ts2, ds2, rs2) = (ts1 @ ts2, ds1 @ ds2, rs1 @ rs2)
let flatten_map f lst = List.fold_left append empty (List.map f lst)
let diff (ts1, ds1, rs1) (ts2, ds2, rs2) = (Common.diff ts1 ts2, Common.diff ds1 ds2, Common.diff rs1 rs2)
let uniq (ts1, ds1, rs1) = (Common.uniq ts1, Common.uniq ds1, Common.uniq rs1)

type substitution = {
  ty_param : ty_param -> ty_param;
  dirt_param : dirt_param -> dirt_param;
  region_param : region_param -> region_param;
}

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst =
  {
    ty_param = Common.id;
    dirt_param = Common.id;
    region_param = Common.id;
  }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = Common.compose sbst1.ty_param sbst2.ty_param;
    dirt_param = Common.compose sbst1.dirt_param sbst2.dirt_param;
    region_param = Common.compose sbst1.region_param sbst2.region_param;
  }

let refresher fresh =
  let substitution = ref [] in
  fun p ->
    match Common.lookup p !substitution with
    | None ->
        let p' = fresh () in
        substitution := Common.update p p' !substitution;
        p'
    | Some p' -> p'

let beautifying_subst () =
  if !Config.disable_beautify then
    identity_subst
  else
    {
      ty_param = refresher (Common.fresh (fun n -> Ty_Param n));
      dirt_param = refresher (Common.fresh (fun n -> Dirt_Param n));
      region_param = refresher (Common.fresh (fun n -> Region_Param n));
    }

let refreshing_subst () =
  {
    ty_param = refresher fresh_ty_param;
    dirt_param = refresher fresh_dirt_param;
    region_param = refresher fresh_region_param;
  }

let print_ty_param ?(non_poly=empty) ((Ty_Param k) as t) ppf =
  let (ts, _, _) = non_poly in
  Symbols.ty_param k (List.mem t ts) ppf

let print_dirt_param ?(non_poly=empty) ((Dirt_Param k) as d) ppf =
  let (_, ds, _) = non_poly in
  Symbols.dirt_param k (List.mem d ds) ppf

let print_region_param ?(non_poly=empty) ((Region_Param k) as r) ppf =
  let (_, _, rs) = non_poly in
  Symbols.region_param k (List.mem r rs) ppf

let format_region (Region_Param i) = i

let rest_int (Dirt_Param i) = i

let print_type_param (Ty_Param n) ppf =
   Format.fprintf ppf "'t%d" n
