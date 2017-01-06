type ty_param = int
type dirt_param = int
type region_param = int

let fresh_ty_param = Common.fresh Common.id
let fresh_dirt_param = Common.fresh Common.id
let fresh_region_param = Common.fresh Common.id

type t = ty_param list * dirt_param list * region_param list

let make (ts, ds, rs) = (ts, ds, rs)
let unmake (ts, ds, rs) = (ts, ds, rs)

let empty = ([], [], [])
let append (ts1, ds1, rs1) (ts2, ds2, rs2) = (ts1 @ ts2, ds1 @ ds2, rs1 @ rs2)
let flatten_map f lst = List.fold_left append empty (List.map f lst)
let diff (ts1, ds1, rs1) (ts2, ds2, rs2) = (Common.diff ts1 ts2, Common.diff ds1 ds2, Common.diff rs1 rs2)
let uniq (ts1, ds1, rs1) = (Common.uniq ts1, Common.uniq ds1, Common.uniq rs1)

let add_ty_param t (ts, ds, rs) = (t::ts, ds, rs)
let add_dirt_param d (ts, ds, rs) = (ts, d::ds, rs)
let add_region_param r (ts, ds, rs) = (ts, ds, r::rs)

let ty_param_mem t (ts, _, _) = List.mem t ts
let dirt_param_mem d (_, ds, _) = List.mem d ds
let region_param_mem r (_, _, rs) = List.mem r rs

type substitution = {
  ty_param : ty_param -> ty_param;
  dirt_param : dirt_param -> dirt_param;
  region_param : region_param -> region_param;
}

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
      ty_param = refresher (Common.fresh Common.id);
      dirt_param = refresher (Common.fresh Common.id);
      region_param = refresher (Common.fresh Common.id);
    }

let refreshing_subst () =
  {
    ty_param = refresher fresh_ty_param;
    dirt_param = refresher fresh_dirt_param;
    region_param = refresher fresh_region_param;
  }

let print_ty_param ?(non_poly=empty) t ppf =
  let (ts, _, _) = non_poly in
  Symbols.ty_param t (List.mem t ts) ppf

let print_dirt_param ?(non_poly=empty) d ppf =
  let (_, ds, _) = non_poly in
  Symbols.dirt_param d (List.mem d ds) ppf

let print_region_param ?(non_poly=empty) r ppf =
  let (_, _, rs) = non_poly in
  Symbols.region_param r (List.mem r rs) ppf

let print_type_param t ppf =
  Format.fprintf ppf "'t%d" t

let project_ty_params (ts, _, _) = ts
