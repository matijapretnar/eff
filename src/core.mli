(** Syntax of the core language. *)

(** Pure expressions *)
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

(** Impure computations *)
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

(** Handler definitions *)
and handler = {
  operations : (operation, abstraction2) Common.assoc;
  value : abstraction;
  finally : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = Pattern.t * computation

(** Abstractions that take two arguments. *)
and abstraction2 = Pattern.t * Pattern.t * computation

(** An operation is an expression that represents an instance together with
    an operation symbol. *)
and operation = expression * Common.opsym

(** A resource consists of an expression for initial state and of a definition
    of operations, which take an argument and a state, and return a result and
    the new state. *)
and resource = expression * (Common.opsym, abstraction2) Common.assoc
