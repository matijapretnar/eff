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

(* Comparison of values is a trickier business than you might think. *)
let rec compare v1 v2 =
  match v1 with
    | Const c ->
      (match v2 with
        | Const c' -> Common.compare_const c c'
        | _ -> Common.Invalid)
    | Tuple lst ->
      (match v2 with
        | Tuple lst' -> compare_list lst lst'
        | _ -> Common.Invalid)
    | Record lst ->
      (match v2 with
        | Record lst' -> compare_record lst lst'
        | _ -> Common.Invalid)
    | Variant (lbl, u)->
      (match v2 with
        | Variant (lbl', u') ->
          let r = Pervasives.compare lbl lbl' in
            if r < 0 then Common.Less
            else if r > 0 then Common.Greater
            else compare_option u u'
        | _ -> Common.Invalid)
    | Closure c ->
      (match v2 with
        | Closure c' -> if c == c' then Common.Equal else Common.Invalid
        | _ -> Common.Invalid)
    | Instance (i, _, _) ->
      (match v2 with
        | Instance (i', _, _) ->
          let r = Pervasives.compare i i' in
            if r < 0 then Common.Less
            else if r > 0 then Common.Greater
            else Common.Equal
        | _ -> Common.Invalid)
    | Handler h ->
      (match v2 with
        | Handler h' -> if h == h' then Common.Equal else Common.Invalid
        | _ -> Common.Invalid)

and compare_list lst1 lst2 =
  match lst1, lst2 with
    | ([], []) -> Common.Equal
    | (u::lst1, v::lst2) ->
      (match compare u v with
        | Common.Less -> Common.Less
        | Common.Equal -> compare_list lst1 lst2
        | Common.Greater -> Common.Greater
        | Common.Invalid -> Common.Invalid)
    | ([], _ :: _) -> Common.Less
    | (_ :: _, []) -> Common.Greater

and compare_record lst1 lst2 =
  (* Is is easiest to canonically sort the fields, then compare as lists. *)
  let rec comp = function
    | [], [] -> Common.Equal
    | (fld1,v1)::lst1, (fld2,v2)::lst2 ->
      let r = Pervasives.compare fld1 fld2 in
        if r < 0 then Common.Less
        else if r > 0 then Common.Greater 
        else
          (match compare v1 v2 with
            | Common.Less -> Common.Less
            | Common.Equal -> comp (lst1, lst2)
            | Common.Greater -> Common.Greater
            | Common.Invalid -> Common.Invalid)
    | [], _ :: _ -> Common.Less
    | _ :: _, [] -> Common.Greater
  in
    comp
      ((List.sort (fun (fld1, _) (fld2, _) -> Pervasives.compare fld1 fld2) lst1),
       (List.sort (fun (fld1, _) (fld2, _) -> Pervasives.compare fld1 fld2) lst2))

and compare_option o1 o2 =
  match o1, o2 with
    | None, None -> Common.Equal
    | Some v1, Some v2 -> compare v1 v2
    | None, Some _ -> Common.Less
    | Some _, None -> Common.Greater

(* Now it is easy to get equality and less than, not to mention we
   can now easily add a builtin "compare". *)
let equal v1 v2 = (compare v1 v2 = Common.Equal)

let less_than v1 v2 =
  match compare v1 v2 with
    | Common.Invalid -> Error.runtime "invalid comparison with <"
    | Common.Less -> true
    | Common.Greater | Common.Equal -> false


