type ty_scheme = (int, Type.ty) Common.assoc * Type.ty * Constr.constraints list
type dirty_scheme = (int, Type.ty) Common.assoc * Type.dirty * Constr.constraints list

type t = (int, ty_scheme option) Common.assoc


let empty = []

let refresh_ctx param_refreshers ctx =
  Common.assoc_map (Type.refresh_ty param_refreshers) ctx


(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh (ctx, ty, cnstrs) =
  let refreshers = Type.global_param_refreshers () in
  refresh_ctx refreshers ctx, Type.refresh_ty refreshers ty, (List.map (Constr.refresh_constraints refreshers) cnstrs)

let lookup ctx x =
  match Common.lookup x ctx with
  | None -> None
  | Some None -> Some None
  | Some (Some sch) -> Some (Some (refresh sch))

let extend_ty ctx x =
    (x, None) :: ctx

(** [Type.free_params ctx] returns a list of all free type parameters in [ctx]. *)
let extend ctx x sch =
  (x, Some sch) :: ctx

let to_list ctx = ctx