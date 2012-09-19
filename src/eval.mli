type env
val initial : env
val lookup : int -> env -> Value.value option
val update : int -> Value.value -> env -> env
val extend : int Pattern.t -> Value.value -> env -> env
val extend_let_rec : env -> (int, Core.abstraction) Common.assoc -> env
val run : env -> Core.computation -> Value.value
