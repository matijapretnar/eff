open Utils
open Language

type state

val initial_state : state
val extend : Term.pattern -> Value.value -> state -> state
val extend_let_rec : state -> (Term.variable, Term.abstraction) Assoc.t -> state
val eval_expression : state -> Term.expression -> Value.value
val run : state -> Term.computation -> Value.value
val update : Language.Term.Variable.t -> Value.value -> state -> state
val lookup : Term.variable -> state -> Value.value option
val add_runner : Term.effect -> (Value.value -> Value.value) -> state -> state
