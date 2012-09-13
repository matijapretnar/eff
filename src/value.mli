type value =
    Const of Common.const
  | Tuple of value list
  | Record of (Common.field, value) Common.assoc
  | Variant of Common.label * value option
  | Closure of closure
  | Instance of instance
  | Handler of (result -> result)
and result = Value of value | Operation of operation * value * closure
and closure = value -> result
and operation = instance * Common.opsym
and instance = int * string option * resource option
and resource =
    value ref * (Common.opsym, value -> value -> result) Common.assoc
val fresh_instance : string option -> resource option -> value
val from_unit : value
val from_bool : bool -> value
val from_int : Big_int.big_int -> value
val from_str : string -> value
val from_float : float -> value
val from_fun : closure -> value
val value : value -> result
val to_bool : value -> bool
val to_int : value -> Big_int.big_int
val to_float : value -> float
val to_str : value -> string
val to_instance : value -> instance
val to_handler : value -> result -> result
val value_unit : result
val value_bool : bool -> result
val value_int : Big_int.big_int -> result
val value_str : string -> result
val value_fun : closure -> result
val value_float : float -> result
val compare : value -> value -> Common.comparison
val compare_list : value list -> value list -> Common.comparison
val compare_record :
  (Common.field, value) Common.assoc ->
  (Common.field, value) Common.assoc -> Common.comparison
val compare_option : value option -> value option -> Common.comparison
val equal : value -> value -> bool
val less_than : value -> value -> bool
