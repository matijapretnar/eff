val extend : Untyped.pattern -> Value.value -> RuntimeEnv.t -> RuntimeEnv.t
val extend_let_rec : RuntimeEnv.t -> (Untyped.variable, Untyped.abstraction) Common.assoc -> RuntimeEnv.t
val run : RuntimeEnv.t -> Untyped.computation -> Value.value
