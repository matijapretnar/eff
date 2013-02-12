type t = (Core.variable, Scheme.ty_scheme) Common.assoc


let empty = []

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh (ctx, ty, cnstrs) =
  let sbst = Type.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Constraints.subst_constraints sbst cnstrs

let lookup ctx x = Common.option_map refresh (Common.lookup x ctx)

(** [Type.free_params ctx] returns a list of all free type parameters in [ctx]. *)
let extend ctx x sch = (x, sch) :: ctx

let to_list ctx = ctx