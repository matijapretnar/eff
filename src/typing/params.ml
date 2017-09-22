type ty_param = int
type dirt_param = int
type region_param = int
type ty_coercion_param = int
type dirt_coercion_param = int
type dirty_coercion_param = int

let fresh_ty_param = OldUtils.fresh OldUtils.id
let fresh_dirt_param = OldUtils.fresh OldUtils.id
let fresh_region_param = OldUtils.fresh OldUtils.id
let fresh_ty_coercion_param = OldUtils.fresh OldUtils.id
let fresh_dirty_coercion_param = OldUtils.fresh OldUtils.id
let fresh_dirt_coercion_param = OldUtils.fresh OldUtils.id


type t = ty_param list * dirt_param list * region_param list

let make (ts, ds, rs) = (ts, ds, rs)
let unmake (ts, ds, rs) = (ts, ds, rs)

let empty = ([], [], [])
let append (ts1, ds1, rs1) (ts2, ds2, rs2) = (ts1 @ ts2, ds1 @ ds2, rs1 @ rs2)
let flatten_map f lst = List.fold_left append empty (List.map f lst)
let diff (ts1, ds1, rs1) (ts2, ds2, rs2) = (OldUtils.diff ts1 ts2, OldUtils.diff ds1 ds2, OldUtils.diff rs1 rs2)
let uniq (ts1, ds1, rs1) = (OldUtils.uniq ts1, OldUtils.uniq ds1, OldUtils.uniq rs1)

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
    ty_param = OldUtils.id;
    dirt_param = OldUtils.id;
    region_param = OldUtils.id;
  }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = OldUtils.compose sbst1.ty_param sbst2.ty_param;
    dirt_param = OldUtils.compose sbst1.dirt_param sbst2.dirt_param;
    region_param = OldUtils.compose sbst1.region_param sbst2.region_param;
  }

let refresher fresh =
  let substitution = ref [] in
  fun p ->
    match OldUtils.lookup p !substitution with
    | None ->
      let p' = fresh () in
      substitution := OldUtils.update p p' !substitution;
      p'
    | Some p' -> p'

let beautifying_subst () =
  if !Config.disable_beautify then
    identity_subst
  else
    {
      ty_param = refresher (OldUtils.fresh OldUtils.id);
      dirt_param = refresher (OldUtils.fresh OldUtils.id);
      region_param = refresher (OldUtils.fresh OldUtils.id);
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


let print_ty_coercion_param ?(non_poly=empty) t ppf =
  let (ts, _, _) = non_poly in
  Symbols.ty_coercion_param t (List.mem t ts) ppf

let print_dirty_coercion_param ?(non_poly=empty) t ppf =
  let (ts, _, _) = non_poly in
  Symbols.dirty_coercion_param t (List.mem t ts) ppf

let print_dirt_coercion_param ?(non_poly=empty) t ppf =
  let (ts, _, _) = non_poly in
  Symbols.dirt_coercion_param t (List.mem t ts) ppf

let project_ty_params (ts, _, _) = ts
let project_dirt_params (_, ds, _) = ds
