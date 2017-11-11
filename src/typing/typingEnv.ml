type t = (Typed.variable, Scheme.ty_scheme) OldUtils.assoc

let empty = []

let lookup ctx x = OldUtils.option_map Scheme.refresh (OldUtils.lookup x ctx)

let update ctx x sch = (x, sch) :: ctx