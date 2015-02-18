type value =
  | Const of Common.const
  | Tuple of value list
  | Record of (Common.field, value) Common.assoc
  | Variant of Common.label * value option
  | Closure of closure
  | Instance of instance
  | Handler of (result -> result)

and result = Result of (closure -> (int * Common.opsym, value -> closure -> result) Common.assoc -> result)

and closure = value -> result

and operation = instance * Common.opsym

and instance = int * string option * resource option

and resource = value ref * (Common.opsym, value -> value -> result) Common.assoc

val value : value -> result
val unit_value : value
val unit_result : result

val fresh_instance : string option -> resource option -> value

val to_bool : value -> bool
val to_int : value -> Big_int.big_int
val to_float : value -> float
val to_str : value -> string
val to_instance : value -> instance
val to_handler : value -> result -> result

val print_value : ?max_level:int -> value -> Format.formatter -> unit
val print_instance : instance -> Format.formatter -> unit
val print_operation : operation -> Format.formatter -> unit
