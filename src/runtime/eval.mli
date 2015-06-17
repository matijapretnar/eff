type env
val initial : env
val lookup : Untyped.variable -> env -> Value.value option
val update : Untyped.variable -> Value.value -> env -> env
val extend : Untyped.pattern -> Value.value -> env -> env
val extend_let_rec : env -> (Untyped.variable, Untyped.abstraction) Common.assoc -> env
val run : env -> Untyped.computation -> Value.value
