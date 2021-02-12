open Utils

type t = (Language.CoreTypes.Variable.t, Type.ty) Assoc.t

let empty = Assoc.empty

let lookup ctx x = Assoc.lookup x ctx

let update ctx x sch = Assoc.update x sch ctx

let return_context ctx = Assoc.to_list ctx

let apply_sub ctx sub =
  Assoc.kmap
    (fun (var, ty) -> (var, Substitution.apply_substitutions_to_type sub ty))
    ctx
