type state
val empty : state
val extend : Typed.pattern -> Value.value -> state -> state
val extend_let_rec : state -> (Typed.variable, Typed.abstraction) Common.assoc -> state
val run : state -> Typed.computation -> Value.value
val update : Typed.variable -> Value.value -> state -> state
val lookup : Typed.variable -> state -> Value.value option
