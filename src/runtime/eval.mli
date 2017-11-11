type state
val empty : state
val extend : Untyped.pattern -> Value.value -> state -> state
val extend_let_rec : state -> (Untyped.variable, Untyped.abstraction) OldUtils.assoc -> state
val run : state -> Untyped.computation -> Value.value
val update : Untyped.variable -> Value.value -> state -> state
val lookup : Untyped.variable -> state -> Value.value option
