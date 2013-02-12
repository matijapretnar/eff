module V = Value

let from_bool b = V.Const (Common.Boolean b)
let from_int n = V.Const (Common.Integer n)
let from_str s = V.Const (Common.String s)
let from_float f = V.Const (Common.Float f)
let from_fun f = V.Closure f

let value_bool b = V.Value (from_bool b)
let value_int n = V.Value (from_int n)
let value_str s = V.Value (from_str s)
let value_float f = V.Value (from_float f)
let value_fun f = V.Value (from_fun f)


(** [binary_closure f] converts a function [f] that takes two values into two
    nested closures. *)
let binary_closure f = from_fun (fun v1 -> value_fun (fun v2 -> f v1 v2))

(** [int_int_to_int f] takes a binary integer function f and transforms it into
    a closure that takes two values and evaluates to a value. *)
let int_int_to_int f =
  let int_f v1 v2 = value_int (f (V.to_int v1) (V.to_int v2)) in
  binary_closure int_f

(** [float_float_to_float f] takes a binary float function f and transforms it
    into a closure that takes two values and evaluates to a value. *)
let float_float_to_float f =
  let float_f v1 v2 = value_float (f (V.to_float v1) (V.to_float v2)) in
  binary_closure float_f

(* Comparison of values is a trickier business than you might think. *)
let rec compare v1 v2 =
  match v1 with
    | V.Closure _ | V.Handler _ -> Common.Invalid
    | V.Const c ->
      (match v2 with
        | V.Closure _ | V.Handler _ -> Common.Invalid
        | V.Const c' -> Common.compare_const c c'
        | V.Tuple _ | V.Record _ | V.Variant _ | V.Instance _ -> Common.Less)
    | V.Tuple lst ->
      (match v2 with
        | V.Closure _ | V.Handler _ -> Common.Invalid
        | V.Const _ -> Common.Greater
        | V.Tuple lst' -> compare_list lst lst'
        | V.Record _ | V.Variant _ | V.Instance _ -> Common.Less)
    | V.Record lst ->
      (match v2 with
        | V.Closure _ | V.Handler _ -> Common.Invalid
        | V.Const _ | V.Tuple _ -> Common.Greater
        | V.Record lst' -> compare_record lst lst'
        | V.Variant _ | V.Instance _ -> Common.Less)
    | V.Variant (lbl, u)->
      (match v2 with
        | V.Closure _ | V.Handler _ -> Common.Invalid
        | V.Const _ | V.Tuple _ | V.Record _ -> Common.Greater
        | V.Variant (lbl', u') ->
          let r = Pervasives.compare lbl lbl' in
            if r < 0 then Common.Less
            else if r > 0 then Common.Greater
            else compare_option u u'
        | V.Instance _ -> Common.Less)
    | V.Instance (i, _, _) ->
      (match v2 with
        | V.Closure _ | V.Handler _ -> Common.Invalid
        | V.Const _ | V.Tuple _ | V.Record _ | V.Variant _ -> Common.Greater
        | V.Instance (i', _, _) ->
          let r = Pervasives.compare i i' in
            if r < 0 then Common.Less
            else if r > 0 then Common.Greater
            else Common.Equal)

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
let equal v1 v2 =
  match compare v1 v2 with
    | Common.Equal -> true
    | Common.Less | Common.Greater -> false
    | Common.Invalid -> Error.runtime "invalid comparison with ="

let less_than v1 v2 =
  match compare v1 v2 with
    | Common.Less -> true
    | Common.Greater | Common.Equal -> false
    | Common.Invalid -> Error.runtime "invalid comparison with <"

let comparison_functions = [
  ("=", binary_closure (fun v1 v2 -> value_bool (equal v1 v2)));
  ("<", binary_closure (fun v1 v2 -> value_bool (less_than v1 v2)));
]

let arithmetic_operations = [
  ("~-", from_fun (fun v -> value_int (Big_int.minus_big_int (V.to_int v))));
  ("+", int_int_to_int Big_int.add_big_int);
  ("-", int_int_to_int Big_int.sub_big_int);
  ("*", int_int_to_int Big_int.mult_big_int);
  ("/", int_int_to_int Big_int.div_big_int);
  ("mod", int_int_to_int Big_int.mod_big_int);
  ("**", int_int_to_int Big_int.power_big_int_positive_big_int);
  ("~-.", from_fun (fun v -> value_float (~-. (V.to_float v))));
  ("+.", float_float_to_float (+.));
  ("-.", float_float_to_float (-.));
  ("*.", float_float_to_float ( *. ));
  ("/.", float_float_to_float (/.));
]

let string_operations = [
  ("^", binary_closure (fun v1 v2 -> value_str (V.to_str v1 ^ V.to_str v2)));
  ("string_length",
    from_fun (fun v -> value_int (Big_int.big_int_of_int (String.length (V.to_str v)))));
]

let conversion_functions = [
  ("to_string",
    let to_string v =
      let s = Print.to_string "%t" (Print.value v) in
      value_str s
    in
    from_fun to_string);
  ("float_of_int",
    from_fun (fun v -> value_float (Big_int.float_of_big_int (V.to_int v))));
]

(** [external_instance name ops] returns an instance with a given name and
    a resource with unit state and operations defined as [ops]. *)
let external_instance name ops =
  let resource_op op v s = V.Value (V.Tuple [op v; s]) in
  let ops = Common.assoc_map resource_op ops in
  V.fresh_instance (Some name) (Some (ref V.unit_value, ops))

let std_print v =
  let str = V.to_str v in
    print_string str;
    flush stdout;
    V.unit_value
and std_read _ =
  let str = read_line () in
  from_str str

let create_exception v = 
  let exc_name = V.to_str v in
  let exception_raise param =
    let message = Print.to_string "%s %t." exc_name (Print.value param) in
      Error.runtime "%s" message
  in
    V.Value (external_instance exc_name [
      ("raise", exception_raise);
    ])

let rnd_int v =
  from_int (Big_int.big_int_of_int (Random.int (Big_int.int_of_big_int (V.to_int v))))
and rnd_float v =
  from_float (Random.float (V.to_float v))

let effect_instances = [
  ("std", external_instance "standard I/O" [
    ("print", std_print);
    ("read", std_read);
  ]);

  ("exception", from_fun create_exception);

  ("rnd", external_instance "random number generator" [
    ("int", rnd_int);
    ("float", rnd_float);
  ]);
]

(** [values] is an association list of external names and values, consisting of
    comparison functions, arithmetic operations, string operations, conversion
    functions, and effect instances. *)
let values =
  comparison_functions @
  arithmetic_operations @
  string_operations @
  conversion_functions @
  effect_instances
