type env
val initial : env
val lookup : Syntax.variable -> env -> Value.value option
val update : Syntax.variable -> Value.value -> env -> env
val extend : Syntax.pattern -> Value.value -> env -> env
val extend_let_rec : env -> (Syntax.variable, Syntax.abstraction) Common.assoc -> env
val run : env -> Syntax.computation -> Value.value
