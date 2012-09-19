type t = (int, Type.ty_scheme) Common.assoc

let empty = []

let lookup ctx x =
  match Common.lookup x ctx with
  | None -> None
  | Some sch -> Some (Type.refresh sch)

let extend ctx x ty_scheme = (x, ty_scheme) :: ctx

let extend_ty ctx x ty = (x, (Trio.empty, ty, [])) :: ctx

let subst_ctx ctx sbst = Common.assoc_map (Type.subst_ty_scheme sbst) ctx

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  (* Code repeats, compare to type.ml, Matija loves to clean up such things. *)
  let binding_params (_, schm) = Type.free_params schm in
  Trio.uniq (Trio.flatten_map binding_params ctx)

let generalize ctx poly ty cstrs =
  if poly then
    let ps = Trio.diff (Type.free_params (Trio.empty, ty, cstrs)) (free_params ctx) in
    (ps, ty, cstrs)
  else
    (Trio.empty, ty, cstrs)
