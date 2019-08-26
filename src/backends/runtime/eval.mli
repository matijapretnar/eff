module ExEff = Typed

type state

val initial_state : state

val extend : ExEff.pattern -> Value.value -> state -> state

val extend_let_rec :
  state -> (ExEff.variable, ExEff.abstraction) Assoc.t -> state

val run : state -> ExEff.computation -> Value.value

val update : ExEff.variable -> Value.value -> state -> state

val lookup : ExEff.variable -> state -> Value.value option
