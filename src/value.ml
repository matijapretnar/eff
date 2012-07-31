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


let fresh_instance =
  let fresh = Common.fresh "effect instance" in
  fun description resource -> Instance (fresh (), description, resource)

let from_unit = Tuple []
let from_bool b = Const (Common.Boolean b)
let from_int n = Const (Common.Integer n)
let from_str s = Const (Common.String s)
let from_float f = Const (Common.Float f)
let from_fun f = Closure f

let value v = Value v

let to_bool ?pos = function
  | Const (Common.Boolean b) -> b
  | _ -> Error.runtime ?pos "A boolean value expected."

let to_int ?pos = function
  | Const (Common.Integer n) -> n
  | _ -> Error.runtime ?pos "An integer value expected."

let to_float ?pos = function
  | Const (Common.Float f) -> f
  | _ -> Error.runtime ?pos "A floating-point value expected."

let to_str ?pos = function
  | Const (Common.String s) -> s
  | _ -> Error.runtime ?pos "A string value expected."

let to_instance ?pos = function
  | Instance i -> i
  | _ -> Error.runtime ?pos "An effect instance expected."

let to_handler ?pos = function
  | Handler h -> h
  | _ -> Error.runtime ?pos "A handler expected."

let value_unit = Value (from_unit)
let value_bool b = Value (from_bool b)
let value_int n = Value (from_int n)
let value_str s = Value (from_str s)
let value_fun f = Value (from_fun f)
let value_float f = Value (from_float f)

let rec equal v1 v2 =
  match v1, v2 with
  | Record r1, Record r2 when List.length r1 = List.length r2 ->
      List.for_all (fun (f1, v1) -> equal v1 (List.assoc f1 r2)) r1
  | Closure f1, Closure f2 -> f1 == f2
  | Handler h1, Handler h2 -> h1 == h2
  | _, _ -> v1 = v2

let rec less_than v1 v2 =
  match v1, v2 with
  | Record r1, Record r2 when List.length r1 = List.length r2 ->
      List.for_all (fun (f1, v1) -> less_than v1 (List.assoc f1 r2)) r1
  | Closure f1, Closure f2 -> false
  | Handler h1, Handler h2 -> false
  | _, _ -> v1 < v2
