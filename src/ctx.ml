type t = (int, Type.ty_scheme option) Common.assoc

let empty = []

let lookup ctx x =
  match Common.lookup x ctx with
  | None -> None
  | Some None -> Some None
  | Some (Some sch) -> Some (Some (Type.refresh sch))

let extend_ty ctx x =
    (x, None) :: ctx

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let extend ctx x sch =
  (x, Some sch) :: ctx

let to_list ctx = ctx