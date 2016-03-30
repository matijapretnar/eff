val extend : Typed.pattern -> Value.value -> RuntimeEnv.t -> RuntimeEnv.t
val extend_let_rec : RuntimeEnv.t -> (Typed.variable, Typed.abstraction) Common.assoc -> RuntimeEnv.t
val run : RuntimeEnv.t -> Typed.computation -> Value.value
