type t = { params : Type.Params.t; constraints : Constraints.t; ty : Type.ty }

let monotype ty =
  { params = Type.Params.empty; constraints = Constraints.empty; ty }
