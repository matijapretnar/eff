type t
val empty : t
val lookup : Untyped.variable -> t -> Value.value option
val update : Untyped.variable -> Value.value -> t -> t
