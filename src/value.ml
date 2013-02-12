type value =
  | Const of Common.const
  | Tuple of value list
  | Record of (Common.field, value) Common.assoc
  | Variant of Common.label * value option
  | Closure of closure
  | Instance of instance
  | Handler of (result -> result)

and result =
  | Value of value
  | Operation of operation * value * closure

and closure = value -> result

and operation = instance * Common.opsym

and instance = int * string option * resource option

and resource = value ref * (Common.opsym, value -> value -> result) Common.assoc

let unit_value = Tuple []
let unit_result = Value unit_value

let fresh_instance =
  let fresh = Common.fresh Common.id in
  fun description resource -> Instance (fresh (), description, resource)

let to_bool = function
  | Const (Common.Boolean b) -> b
  | _ -> Error.runtime "A boolean value expected."

let to_int = function
  | Const (Common.Integer n) -> n
  | _ -> Error.runtime "An integer value expected."

let to_float = function
  | Const (Common.Float f) -> f
  | _ -> Error.runtime "A floating-point value expected."

let to_str = function
  | Const (Common.String s) -> s
  | _ -> Error.runtime "A string value expected."

let to_instance = function
  | Instance i -> i
  | _ -> Error.runtime "An effect instance expected."

let to_handler = function
  | Handler h -> h
  | _ -> Error.runtime "A handler expected."
