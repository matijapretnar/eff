(** Syntax of the intermediate language. *)

type expression = plain_expression Common.pos
and plain_expression =
  | Var of Common.variable
  | Const of Common.const
  | Tuple of expression list
  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option
  | Lambda of abstraction
  | Operation of operation
  | Handler of handler

and computation = plain_computation Common.pos
and plain_computation =
  | Value of expression
  | Let of (Pattern.t * computation) list * computation
  | LetRec of (Common.variable * abstraction) list * computation
  | Match of expression * abstraction list
  | While of computation * computation
  | For of Common.variable * expression * expression * computation * bool
  | Apply of expression * expression
  | New of Common.tyname * resource option
  | Handle of expression * computation
  | Check of computation

and handler = {
  operations : (operation, abstraction2) Common.assoc;
  value : abstraction;
  finally : abstraction;
}

and abstraction = Pattern.t * computation

and abstraction2 = Pattern.t * Pattern.t * computation

and operation = expression * Common.opsym

and resource = expression * (Common.opsym, abstraction2) Common.assoc
