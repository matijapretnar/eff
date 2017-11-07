type t = (Typed.variable, Types.target_ty) OldUtils.assoc

let empty = []

let lookup ctx x =  (OldUtils.lookup x ctx)

let update ctx x sch = (x, sch) :: ctx

let return_context ctx = ctx 

let apply_sub ctx sub = List.map (fun (var,ty) -> (var, Unification.apply_substitution_ty sub ty)) ctx