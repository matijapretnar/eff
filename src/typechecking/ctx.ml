type t = (Syntax.variable, Scheme.ty_scheme) Common.assoc

let empty = []

let lookup ctx x = Common.option_map Scheme.refresh (Common.lookup x ctx)

let extend ctx x sch = (x, sch) :: ctx
