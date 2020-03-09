
open CoreUtils

type variable = CoreTypes.Variable.t

type pattern =
  | PVar of variable

type term =
  | Var of variable
  | Lambda of abstraction

and abstraction = pattern * term
