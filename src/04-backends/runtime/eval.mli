open Utils
open Language

type state

val initial_state : state

val extend : UntypedSyntax.pattern -> Value.value -> state -> state

val extend_let_rec :
  state -> (UntypedSyntax.variable, UntypedSyntax.abstraction) Assoc.t -> state

val eval : state -> UntypedSyntax.expression -> Value.value

val run : state -> UntypedSyntax.computation -> Value.value

val update : UntypedSyntax.variable -> Value.value -> state -> state

val lookup : UntypedSyntax.variable -> state -> Value.value option
