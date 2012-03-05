(** Syntax of the intermediate language. *)

module C = Common

type expression =
  plain_expression C.pos
and plain_expression =
  | Var of C.variable
  | Const of C.const
  | Tuple of expression list
  | Lambda of abstraction
  | Record of (C.field, expression) C.assoc
  | Variant of C.label * expression option
  | Operation of operation
  | Handler of handler

and computation =
  plain_computation C.pos
and plain_computation =
  | Apply of expression * expression
  | Value of expression
  | Match of expression * abstraction list
  | While of computation * computation
  | For of C.variable * expression * expression * computation * bool
  | New of C.effname * (expression * (C.opname * abstraction2) list) option
  | Handle of expression * computation
  | Let of abstraction list * computation
  | LetRec of (C.variable * abstraction) list * computation
  | Check of computation

and handler = {
  operations : (operation, Pattern.t * abstraction) C.assoc;
  return : abstraction;
  finally : abstraction;
}

and abstraction = Pattern.t * computation

and abstraction2 = Pattern.t * Pattern.t * computation

and operation = expression * C.opname

let from_unit = Tuple []
