type t = (Typed.variable, Types.target_ty) Assoc.t

let empty = Assoc.empty

let lookup ctx x = Assoc.lookup x ctx

let update ctx x sch = Assoc.update x sch ctx

let return_context ctx = Assoc.to_list ctx

let apply_sub ctx sub =
  Assoc.kmap
    (fun (var, ty) -> (var, Unification.apply_substitution_ty sub ty))
    ctx
