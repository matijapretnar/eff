module V = Value

(** [binary_closure f] converts a function [f] that takes two values into two
    nested closures. *)
let binary_closure f = V.from_fun (fun v1 -> V.value_fun (fun v2 -> f v1 v2))

(** [int_int_to_int f] takes a binary integer function f and transforms it into
    a closure that takes two values and evaluates to a value. *)
let int_int_to_int f =
  let int_f v1 v2 = V.value_int (f (V.to_int v1) (V.to_int v2)) in
  binary_closure int_f

(** [float_float_to_float f] takes a binary float function f and transforms it
    into a closure that takes two values and evaluates to a value. *)
let float_float_to_float f =
  let float_f v1 v2 = V.value_float (f (V.to_float v1) (V.to_float v2)) in
  binary_closure float_f

let comparison_functions = [
  ("=", binary_closure (fun v1 v2 -> V.value_bool (V.equal v1 v2)));
  ("<", binary_closure (fun v1 v2 -> V.value_bool (V.less_than v1 v2)));
]

let arithmetic_operations = [
  ("~-", V.from_fun (fun v -> V.value_int (Big_int.minus_big_int (V.to_int v))));
  ("+", int_int_to_int Big_int.add_big_int);
  ("-", int_int_to_int Big_int.sub_big_int);
  ("*", int_int_to_int Big_int.mult_big_int);
  ("/", int_int_to_int Big_int.div_big_int);
  ("mod", int_int_to_int Big_int.mod_big_int);
  ("**", int_int_to_int Big_int.power_big_int_positive_big_int);
  ("~-.", V.from_fun (fun v -> V.value_float (~-. (V.to_float v))));
  ("+.", float_float_to_float (+.));
  ("-.", float_float_to_float (-.));
  ("*.", float_float_to_float ( *. ));
  ("/.", float_float_to_float (/.));
]

let string_operations = [
  ("^", binary_closure (fun v1 v2 -> V.value_str (V.to_str v1 ^ V.to_str v2)));
  ("string_length",
    V.from_fun (fun v -> V.value_int (Big_int.big_int_of_int (String.length (V.to_str v)))));
]

let conversion_functions = [
  ("to_string",
    let to_string v =
      let s = Print.to_string "%t" (Print.value v) in
      V.value_str s
    in
    V.from_fun to_string);
  ("float_of_int",
    V.from_fun (fun v -> V.value_float (Big_int.float_of_big_int (V.to_int v))));
]

(** [external_instance name ops] returns an instance with a given name and
    a resource with unit state and operations defined as [ops]. *)
let external_instance name ops =
  let resource_op op v s = V.Value (V.Tuple [op v; s]) in
  let ops = Common.assoc_map resource_op ops in
  V.fresh_instance (Some name) (Some (ref V.from_unit, ops))

let std_print v =
  let str = V.to_str v in
    print_string str;
    flush stdout;
    V.from_unit
and std_read _ =
  let str = read_line () in
  V.from_str str

let create_exception v = 
  let exc_name = V.to_str v in
  let exception_raise param =
    let message = Print.to_string "%s %t." exc_name (Print.value param) in
      Error.exc "%s" message
  in
    V.Value (external_instance exc_name [
      ("raise", exception_raise);
    ])

let rnd_int v =
  V.from_int (Big_int.big_int_of_int (Random.int (Big_int.int_of_big_int (V.to_int v))))
and rnd_float v =
  V.from_float (Random.float (V.to_float v))

let effect_instances = [
  ("std", external_instance "standard I/O" [
    ("print", std_print);
    ("read", std_read);
  ]);

  ("exception", V.from_fun create_exception);

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
