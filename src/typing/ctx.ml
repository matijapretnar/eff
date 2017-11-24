type ty_scheme = Type.ty_param list * Type.ty
type t = (CoreSyntax.variable, ty_scheme) OldUtils.assoc

let empty = []

let lookup ~loc ctx x =
  match OldUtils.lookup x ctx with
  | Some (ps, t) -> snd (Type.refresh ps t)
  | None -> Error.typing ~loc "Unknown name %t" (CoreSyntax.Variable.print x)

let extend ctx x ty_scheme = (x, ty_scheme) :: ctx

let extend_ty ctx x ty = (x, ([], ty)) :: ctx

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty) =
    assert (List.for_all (fun (p, _) -> not (List.mem p ps)) sbst);
    (ps, Type.subst_ty sbst ty)
  in
  OldUtils.assoc_map subst_ty_scheme ctx

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  let binding_params (_, (ps, ty)) = OldUtils.diff (Type.free_params ty) ps in
  let xs = OldUtils.flatten_map binding_params ctx in
    OldUtils.uniq xs

let generalize ctx poly ty =
  if poly then
    let ps = OldUtils.diff (Type.free_params ty) (free_params ctx) in
    (ps, ty)
  else
    ([], ty)
