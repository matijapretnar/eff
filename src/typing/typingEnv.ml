type t = (Untyped.variable, Scheme.ty_scheme) Common.assoc

let empty = []

let lookup ctx x = Common.option_map Scheme.refresh (Common.lookup x ctx)

let update ctx x sch = (x, sch) :: ctx
