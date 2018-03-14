type value =
  | Const of Const.t
  | Tuple of value list
  | Record of (OldUtils.field, value) OldUtils.assoc
  | Variant of OldUtils.label * value option
  | Closure of closure
  | Handler of (result -> result)

and result = Value of value | Call of OldUtils.effect * value * closure

and closure = value -> result

val unit_value : value

val unit_result : result

val first : value -> value
val second : value -> value

val to_out_channel : value -> out_channel
val to_in_channel : value -> in_channel

val to_bool : value -> bool

val to_int : value -> int

val to_float : value -> float

val to_str : value -> string

val to_handler : value -> result -> result

val print_value : ?max_level:int -> value -> Format.formatter -> unit

val print_effect : OldUtils.effect -> Format.formatter -> unit

val print_result : result -> Format.formatter -> unit
