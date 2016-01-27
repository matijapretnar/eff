type value =
  | Const of Const.t
  | Tuple of value list
  | Record of (Common.field, value) Common.assoc
  | Variant of Common.label * value option
  | Closure of closure
  | Handler of (result -> result)

and result =
  | Value of value
  | Call of Typed.effect * value * closure

and closure = value -> result

val unit_value : value
val unit_result : result

val to_bool : value -> bool
val to_int : value -> Big_int.big_int
val to_float : value -> float
val to_str : value -> string
val to_handler : value -> result -> result

val print_value : ?max_level:int -> value -> Format.formatter -> unit
val print_effect : Typed.effect -> Format.formatter -> unit
val print_result : result -> Format.formatter -> unit