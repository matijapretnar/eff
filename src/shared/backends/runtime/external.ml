open Utils
open Language
open CoreUtils
module V = Value

let from_bool b = V.Const (Const.of_boolean b)

let from_int n = V.Const (Const.of_integer n)

let from_str s = V.Const (Const.of_string s)

let from_float f = V.Const (Const.of_float f)

let from_fun f = V.Closure f

let value_bool b = V.Value (from_bool b)

let value_int n = V.Value (from_int n)

let value_str s = V.Value (from_str s)

let value_float f = V.Value (from_float f)

let value_fun f = V.Value (from_fun f)

(** [binary_closure f] converts a function [f] that takes two values into two
    nested closures. *)
let binary_closure f = from_fun (fun v1 -> value_fun (fun v2 -> f v1 v2))

(** [ternary_closure f] converts a function [f] that takes three values into three
    nested closures. *)
let ternary_closure f =
  from_fun (fun v1 -> value_fun (fun v2 -> value_fun (fun v3 -> f v1 v2 v3)))

(** [int_int_to_int f] takes a binary integer function f and transforms it into
    a closure that takes two values and evaluates to a value. *)
let int_int_to_int f =
  let int_f v1 v2 = value_int (f (V.to_int v1) (V.to_int v2)) in
  binary_closure int_f

(** [float_to_float f] takes a unary float function f and transforms it into
    a closure that takes two values and evaluates to a value. *)
let float_to_float f = from_fun (fun v -> value_float (f (V.to_float v)))

(** [float_float_to_float f] takes a binary float function f and transforms it
    into a closure that takes two values and evaluates to a value. *)
let float_float_to_float f =
  let float_f v1 v2 = value_float (f (V.to_float v1) (V.to_float v2)) in
  binary_closure float_f

(* Comparison of values is a trickier business than you might think. *)
let rec compare v1 v2 =
  match v1 with
  | V.Closure _ | V.Handler _ -> Invalid
  | V.Const c -> (
      match v2 with
      | V.Closure _ | V.Handler _ -> Invalid
      | V.Const c' -> Const.compare c c'
      | V.Tuple _ | V.Record _ | V.Variant _ -> Less)
  | V.Tuple lst -> (
      match v2 with
      | V.Closure _ | V.Handler _ -> Invalid
      | V.Const _ -> Greater
      | V.Tuple lst' -> compare_list lst lst'
      | V.Record _ | V.Variant _ -> Less)
  | V.Record lst -> (
      match v2 with
      | V.Closure _ | V.Handler _ -> Invalid
      | V.Const _ | V.Tuple _ -> Greater
      | V.Record lst' -> compare_record lst lst'
      | V.Variant _ -> Less)
  | V.Variant (lbl, u) -> (
      match v2 with
      | V.Closure _ | V.Handler _ -> Invalid
      | V.Const _ | V.Tuple _ | V.Record _ -> Greater
      | V.Variant (lbl', u') ->
          let r = Stdlib.compare lbl lbl' in
          if r < 0 then Less else if r > 0 then Greater else compare_option u u'
      )

and compare_list lst1 lst2 =
  match (lst1, lst2) with
  | [], [] -> Equal
  | u :: lst1, v :: lst2 -> (
      match compare u v with
      | Less -> Less
      | Equal -> compare_list lst1 lst2
      | Greater -> Greater
      | Invalid -> Invalid)
  | [], _ :: _ -> Less
  | _ :: _, [] -> Greater

and compare_record lst1 lst2 =
  (* Is is easiest to canonically sort the fields, then compare as lists. *)
  let rec comp = function
    | [], [] -> Equal
    | (fld1, v1) :: lst1, (fld2, v2) :: lst2 -> (
        let r = Stdlib.compare fld1 fld2 in
        if r < 0 then Less
        else if r > 0 then Greater
        else
          match compare v1 v2 with
          | Less -> Less
          | Equal -> comp (lst1, lst2)
          | Greater -> Greater
          | Invalid -> Invalid)
    | [], _ :: _ -> Less
    | _ :: _, [] -> Greater
  in
  let lst1' = Assoc.to_list lst1 in
  let lst2' = Assoc.to_list lst2 in
  comp
    ( List.sort (fun (fld1, _) (fld2, _) -> Stdlib.compare fld1 fld2) lst1',
      List.sort (fun (fld1, _) (fld2, _) -> Stdlib.compare fld1 fld2) lst2' )

and compare_option o1 o2 =
  match (o1, o2) with
  | None, None -> Equal
  | Some v1, Some v2 -> compare v1 v2
  | None, Some _ -> Less
  | Some _, None -> Greater

(* Now it is easy to get equality and less than, not to mention we
   can now easily add a builtin "compare". *)
let equal v1 v2 =
  match compare v1 v2 with
  | Equal -> true
  | Less | Greater -> false
  | Invalid -> Error.runtime "invalid comparison with ="

let less_than v1 v2 =
  match compare v1 v2 with
  | Less -> true
  | Greater | Equal -> false
  | Invalid -> Error.runtime "invalid comparison with <"

let comparison_functions =
  Assoc.of_list
    [
      ("=", binary_closure (fun v1 v2 -> value_bool (equal v1 v2)));
      ("<", binary_closure (fun v1 v2 -> value_bool (less_than v1 v2)));
    ]

let constants =
  Assoc.of_list
    [
      ("infinity", from_float infinity);
      ("neg_infinity", from_float neg_infinity);
      ("nan", from_float nan);
    ]

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
      let b = pow a (n / 2) in
      if n mod 2 = 0 then b * b else b * b * a

let arithmetic_operations =
  Assoc.of_list
    [
      ("~-", from_fun (fun v -> value_int (-V.to_int v)));
      ("+", int_int_to_int ( + ));
      ("-", int_int_to_int ( - ));
      ("*", int_int_to_int ( * ));
      ("/", int_int_to_int ( / ));
      ("mod", int_int_to_int ( mod ));
      ("**", int_int_to_int pow);
      ("~-.", from_fun (fun v -> value_float ~-.(V.to_float v)));
      ("+.", float_float_to_float ( +. ));
      ("-.", float_float_to_float ( -. ));
      ("*.", float_float_to_float ( *. ));
      ("/.", float_float_to_float ( /. ));
      ("exp", float_to_float exp);
      ("expm1", float_to_float expm1);
      ("log", float_to_float log);
      ("log1p", float_to_float log1p);
      ("cos", float_to_float cos);
      ("sin", float_to_float sin);
      ("tan", float_to_float tan);
      ("acos", float_to_float acos);
      ("asin", float_to_float asin);
      ("atan", float_to_float atan);
      ("sqrt", float_to_float sqrt);
    ]

let string_operations =
  Assoc.of_list
    [
      ("^", binary_closure (fun v1 v2 -> value_str (V.to_str v1 ^ V.to_str v2)));
      ( "string_length",
        from_fun (fun v -> value_int (String.length (V.to_str v))) );
      ( "sub",
        ternary_closure (fun v1 v2 v3 ->
            value_str (String.sub (V.to_str v1) (V.to_int v2) (V.to_int v3))) );
    ]

let conversion_functions =
  Assoc.of_list
    [
      ( "to_string",
        let to_string v =
          Value.print_value v Format.str_formatter;
          let s = Format.flush_str_formatter () in
          value_str s
        in
        from_fun to_string );
      ( "string_of_float",
        from_fun (fun v -> value_str (string_of_float (V.to_float v))) );
      ( "string_of_int",
        from_fun (fun v -> value_str (string_of_int (V.to_int v))) );
      ( "float_of_int",
        from_fun (fun v -> value_float (float_of_int (V.to_int v))) );
      ( "int_of_float",
        from_fun (fun v -> value_int (int_of_float (V.to_float v))) );
    ]

(** [values] is an association list of external names and values, consisting of
    comparison functions, arithmetic operations, string operations, conversion
    functions, and effect instances. *)
let values =
  comparison_functions |> Assoc.concat constants
  |> Assoc.concat arithmetic_operations
  |> Assoc.concat string_operations
  |> Assoc.concat conversion_functions
