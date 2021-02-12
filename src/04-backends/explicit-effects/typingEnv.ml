open Utils

type t = (Language.CoreTypes.Variable.t, Type.ty_scheme) Assoc.t

let empty = Assoc.empty

let lookup ctx x =
  match Assoc.lookup x ctx with
  | Some ty_scheme ->
      assert (ty_scheme.Type.ty_constraints = []);
      assert (ty_scheme.dirt_constraints = []);
      (Term.poly_var (Term.variable x ty_scheme.Type.monotype) [] [], [])
  | None -> assert false

let update ctx x sch = Assoc.update x sch ctx
