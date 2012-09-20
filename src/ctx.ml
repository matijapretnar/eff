type t = (int, Type.ty_scheme) Common.assoc

let empty = []

let lookup ctx x =
  match Common.lookup x ctx with
  | None -> None
  | Some sch -> Some (Type.refresh sch)

let extend_ty ctx x ty cstrs =
    (x, (Trio.empty, ty, cstrs)) :: ctx

let subst_ctx ctx sbst = Common.assoc_map (Type.subst_ty_scheme sbst) ctx

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  let binding_params (_, schm) = Type.free_params schm in
  Trio.uniq (Trio.flatten_map binding_params ctx)

let extend ctx x ty cstrs =
  let ps = Trio.diff (Type.free_params (Trio.empty, ty, cstrs)) (free_params ctx) in
  (x, (ps, ty, cstrs)) :: ctx

let to_list ctx = ctx