(** Syntax of the core language. *)

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

type pattern = plain_pattern CoreUtils.located

and plain_pattern =
  | PVar of variable
  | PAnnotated of pattern * Type.ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (field, pattern) Assoc.t
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

type expression = plain_expression CoreUtils.located
(** Pure expressions *)

and plain_expression =
  | Var of variable
  | Const of Const.t
  | Annotated of expression * Type.ty
  | Tuple of expression list
  | Record of (field, expression) Assoc.t
  | Variant of label * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler

and computation = plain_computation CoreUtils.located
(** Impure computations *)

and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Handle of expression * computation
  | Check of computation

and handler = {
  effect_clauses : (effect, abstraction2) Assoc.t;
  value_clause : abstraction;
  finally_clause : abstraction;
}
(** Handler definitions *)

and abstraction = pattern * computation
(** Abstractions that take one argument. *)

and abstraction2 = pattern * pattern * computation
(** Abstractions that take two arguments. *)

val print_pattern : ?max_level:int -> pattern -> Format.formatter -> unit

val print_computation :
  ?max_level:int -> computation -> Format.formatter -> unit

val print_expression : ?max_level:int -> expression -> Format.formatter -> unit
