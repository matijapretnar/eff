open Utils
open Language

type t = (CoreTypes.Variable.t, Type.ty_scheme) Assoc.t

let empty = Assoc.empty

let lookup ctx x : Term.expression * Constraint.omega_ct list =
  match Assoc.lookup x ctx with
  | Some ty_scheme ->
      let ty_scheme = Type.refresh_ty_scheme ty_scheme in
      let x =
        Term.poly_var_with_parameters x ty_scheme.parameters ty_scheme.monotype
      in
      let cnstrs =
        List.map
          (fun (w, ct) -> Constraint.TyOmega (w, ct))
          ty_scheme.parameters.ty_constraints
        @ List.map
            (fun (w, dt) -> Constraint.DirtOmega (w, dt))
            ty_scheme.parameters.dirt_constraints
      in
      (x, cnstrs)
  | None -> assert false

let update ctx x sch = Assoc.update x sch ctx
