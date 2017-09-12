type state
val empty : state
val extend : TypedSyntax.pattern -> Value.value -> state -> state
val extend_let_rec : state -> (TypedSyntax.variable, TypedSyntax.abstraction) OldUtils.assoc -> state
val run : state -> TypedSyntax.computation -> Value.value
val update : TypedSyntax.variable -> Value.value -> state -> state
val lookup : TypedSyntax.variable -> state -> Value.value option
