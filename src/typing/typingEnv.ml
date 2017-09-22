type t = (Typed.variable, Types.target_ty) OldUtils.assoc

let empty = []

let lookup ctx x =  (OldUtils.lookup x ctx)

let update ctx x sch = (x, sch) :: ctx
