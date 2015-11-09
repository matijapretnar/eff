type t
val initial : t
val lookup : Untyped.variable -> t -> Value.value option
val update : Untyped.variable -> Value.value -> t -> t
