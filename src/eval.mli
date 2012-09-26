type env
val initial : env
val lookup : Core.variable -> env -> Value.value option
val update : Core.variable -> Value.value -> env -> env
val extend : Core.pattern -> Value.value -> env -> env
val extend_let_rec : env -> (Core.variable, Core.abstraction) Common.assoc -> env
val run : env -> Core.computation -> Value.value
