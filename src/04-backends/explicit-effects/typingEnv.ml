open Utils

type t = (Language.CoreTypes.Variable.t, Type.ty_scheme) Assoc.t

let empty = Assoc.empty

let lookup ctx x = Assoc.lookup x ctx

let update ctx x sch = Assoc.update x sch ctx
