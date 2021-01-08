open Utils
open Language

type value =
  | Const of Const.t
  | Tuple of value list
  | Record of (CoreTypes.Field.t, value) Assoc.t
  | Variant of CoreTypes.Label.t * value option
  | Closure of closure
  | Handler of (result -> result)

and result = Value of value | Call of CoreTypes.Effect.t * value * closure

and closure = value -> result

val unit_value : value

val unit_result : result

val to_bool : value -> bool

val to_int : value -> int

val to_float : value -> float

val to_str : value -> string

val to_handler : value -> result -> result

val print_value : ?max_level:int -> value -> Format.formatter -> unit

val print_effect : CoreTypes.Effect.t -> Format.formatter -> unit

val print_result : result -> Format.formatter -> unit
