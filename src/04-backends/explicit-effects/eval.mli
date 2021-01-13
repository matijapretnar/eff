open Utils

type state

val initial_state : state

val extend : Typed.pattern -> Value.value -> state -> state

val extend_let_rec :
  state -> (Typed.variable, Typed.abstraction) Assoc.t -> state

val run : state -> Typed.computation -> Value.value

val update : Typed.variable -> Value.value -> state -> state

val lookup : Typed.variable -> state -> Value.value option
