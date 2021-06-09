open Utils

type state

val initial_state : state

val extend : Term.pattern -> Value.value -> state -> state

val extend_let_rec :
  state ->
  (Term.variable, Type.TyCoercionParam.t list * Term.abstraction) Assoc.t ->
  state

val eval_expression : state -> Term.expression -> Value.value

val run : state -> Term.computation -> Value.value

val update : Language.CoreTypes.Variable.t -> Value.value -> state -> state

val lookup : Term.variable -> state -> Value.value option
