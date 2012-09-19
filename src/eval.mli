type env
val initial : env
val lookup : Common.variable -> env -> Value.value option
val update : Common.variable -> Value.value -> env -> env
val extend : Common.variable Pattern.t -> Value.value -> env -> env
val extend_let_rec : env -> (Common.variable, Core.abstraction) Common.assoc -> env
val run : env -> Core.computation -> Value.value
