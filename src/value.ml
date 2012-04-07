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

let value_unit = Value (from_unit)
let value_bool b = Value (from_bool b)
let value_int n = Value (from_int n)
let value_str s = Value (from_str s)
let value_fun f = Value (from_fun f)
let value_float f = Value (from_float f)

let rec equal v1 v2 =
  match v1, v2 with
  | Const c1, Const c2 -> Common.equal_const c1 c2
  | Tuple vs1, Tuple vs2 -> equal_list vs1 vs2
  | Record r1, Record r2 -> equal_record r1 r2 && equal_record r2 r1
  | Variant (lbl1, None), Variant (lbl2, None) ->
      lbl1 = lbl2
  | Variant (lbl1, Some v1), Variant (lbl2, Some v2) ->
      lbl1 = lbl2 && equal v1 v2
  | Closure f1, Closure f2 -> f1 == f2
  | Instance i1, Instance i2 -> i1 = i2
  | Handler h1, Handler h2 -> h1 == h2
  | _, _ -> false
and equal_list vs1 vs2 =
  try List.for_all2 equal vs1 vs2
  with Invalid_argument "for_all2" -> false
and equal_record r1 r2 =
  List.fold_left (fun b (f2, v2) -> match Common.lookup f2 r1 with
                 | Some v1 when equal v1 v2 -> b
                 | _ -> false) true
      r2
and equal_operations op1 op2 =
  List.fold_left (fun b (op, f) -> match Common.lookup op op1 with
                 | Some g when f == g -> b
                 | _ -> false) true
      op2

let rec less_than v1 v2 =
  match v1, v2 with
  | Const c1, Const c2 -> Common.less_than_const c1 c2
  | Tuple vs1, Tuple vs2 -> less_than_list vs1 vs2
  | Record r1, Record r2 -> less_than_record r1 r2
  | Variant (lbl1, _), Variant (lbl2, _) when lbl1 < lbl2 -> true
  | Variant (lbl1, Some v1), Variant (lbl2, Some v2) ->
      lbl1 = lbl2 && less_than v1 v2
  | Closure f1, Closure f2 -> false
  | Instance (i1, _, _), Instance (i2, _, _) -> i1 < i2
  | Handler h1, Handler h2 -> false
  | _, _ -> false
and less_than_list vs1 vs2 =
  match vs1, vs2 with
  | _, [] -> false
  | [], _ -> true
  | v1 :: vs1, v2 :: vs2 ->
      if less_than v1 v2 then
        true
      else if less_than v2 v1 then
        false
      else
        less_than_list vs1 vs2
and less_than_record r1 r2 =
  List.fold_left (fun b (f1, v1) -> match Common.lookup f1 r2 with
                 | Some v2 when less_than v1 v2 -> b
                 | _ -> false) true
      r1
