type ty_param = int
type dirt_param = int

let fresh_ty_param = Common.fresh Common.id
let fresh_dirt_param = Common.fresh Common.id

type t = ty_param list * dirt_param list

let make (ts, ds) = (ts, ds)
let unmake (ts, ds) = (ts, ds)

let empty = ([], [])
let append (ts1, ds1) (ts2, ds2) = (ts1 @ ts2, ds1 @ ds2)
let flatten_map f lst = List.fold_left append empty (List.map f lst)
let diff (ts1, ds1) (ts2, ds2) = (Common.diff ts1 ts2, Common.diff ds1 ds2)
let uniq (ts1, ds1) = (Common.uniq ts1, Common.uniq ds1)

let add_ty_param t (ts, ds) = (t::ts, ds)
let add_dirt_param d (ts, ds) = (ts, d::ds)

let ty_param_mem t (ts, _) = List.mem t ts
let dirt_param_mem d (_, ds) = List.mem d ds

type substitution = {
  ty_param : ty_param -> ty_param;
  dirt_param : dirt_param -> dirt_param;
}

let identity_subst =
  {
    ty_param = Common.id;
    dirt_param = Common.id;
  }

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  {
    ty_param = Common.compose sbst1.ty_param sbst2.ty_param;
    dirt_param = Common.compose sbst1.dirt_param sbst2.dirt_param;
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
    }

let refreshing_subst () =
  {
    ty_param = refresher fresh_ty_param;
    dirt_param = refresher fresh_dirt_param;
  }

let print_ty_param ?(non_poly=empty) t ppf =
  let (ts, _) = non_poly in
  Symbols.ty_param t (List.mem t ts) ppf

let print_dirt_param ?(non_poly=empty) d ppf =
  let (_, ds) = non_poly in
  Symbols.dirt_param d (List.mem d ds) ppf

let print_type_param t ppf =
  Format.fprintf ppf "'t%d" t

let project_ty_params (ts, _) = ts
let project_dirt_params (_, ds) = ds
