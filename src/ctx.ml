type ty_scheme = Type.ty_param list * Type.ty
type t = (Common.variable, ty_scheme) Common.assoc

let empty = []

let lookup ?pos ctx x =
  match Common.lookup x ctx with
  | Some (ps, t) -> snd (Type.refresh ps t)
  | None -> Error.typing ?pos "Unknown name %s" x

let extend ctx x ty_scheme = (x, ty_scheme) :: ctx

let extend_ty ctx x ty = (x, ([], ty)) :: ctx

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty) =
    assert (List.for_all (fun (p, _) -> not (List.mem p ps)) sbst);
    (ps, Type.subst_ty sbst ty)
  in
  Common.assoc_map subst_ty_scheme ctx

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  let binding_params (_, (ps, ty)) = Common.diff (Type.free_params ty) ps in
  Common.uniq (Common.flatten_map binding_params ctx)

let generalize ctx poly ty =
  if poly then
    let ps = Common.diff (Type.free_params ty) (free_params ctx) in
    (ps, ty)
  else
    ([], ty)
