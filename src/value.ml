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

(* You math think the following code is ugly, but at least it works, and it
   is not going to die when we extend the datatype of values because we
   avoid using wild wildcards such as _, _. Also, the function is written
   so that it works as expected when --no-types is used. *)
let rec equal v = function
  | Const c ->
    (match v with
      | Const c' -> Common.equal_const c c'
      | _ -> false)
  | Tuple lst ->
    (match v with
      | Tuple lst' -> equal_list lst lst'
      | _ -> false)
  | Record lst ->
    (match v with
      | Record lst' -> equal_record lst lst'
      | _ -> false)
  | Variant (lbl, u)->
    (match v with
      | Variant (lbl', u') ->
        lbl = lbl' && equal_option u u'
      | _ -> false)
  | Closure c ->
    (match v with
      | Closure c' -> c == c'
      | _ -> false)
  | Instance (i, _, _) ->
    (match v with
      | Instance (i', _, _) -> i = i'
      | _ -> false)
  | Handler h ->
    (match v with
      | Handler h' -> h == h'
      | _ -> false)

and equal_list lst1 lst2 =
  match lst1, lst2 with
    | ([], []) -> true
    | (u::lst1, v::lst2) -> equal u v && equal_list lst1 lst2
    | ([], _ :: _) | (_ :: _, []) -> false

and equal_record lst1 lst2 =
  List.length lst1 = List.length lst2 &&
  List.for_all (fun (fld, u) ->
    match Common.lookup fld lst2 with
      | Some v -> equal u v
      | None -> false)
  lst1

and equal_option o1 o2 =
  match o1, o2 with
    | None, None -> true
    | Some v1, Some v2 -> equal v1 v2
    | Some _, None | None, Some _ -> false

let rec less_than v1 v2 =
  match v1, v2 with
  | Record r1, Record r2 when List.length r1 = List.length r2 ->
      List.for_all (fun (f1, v1) -> less_than v1 (List.assoc f1 r2)) r1
  | Closure f1, Closure f2 -> false
  | Handler h1, Handler h2 -> false
  | _, _ -> v1 < v2
