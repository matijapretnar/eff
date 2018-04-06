module V = Value

let from_char c = V.Const (Const.of_char c)

let from_bool b = V.Const (Const.of_boolean b)

let from_int n = V.Const (Const.of_integer n)

let from_str s = V.Const (Const.of_string s)

let from_float f = V.Const (Const.of_float f)

let from_fun f = V.Closure f

let value_list b = V.Value (Tuple b)

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
  | V.Closure _ | V.Handler _ -> OldUtils.Invalid
  | V.Const c -> (
    match v2 with
    | V.Closure _ | V.Handler _ -> OldUtils.Invalid
    | V.Const c' -> Const.compare c c'
    | V.Tuple _ | V.Record _ | V.Variant _ -> OldUtils.Less )
  | V.Tuple lst -> (
    match v2 with
    | V.Closure _ | V.Handler _ -> OldUtils.Invalid
    | V.Const _ -> OldUtils.Greater
    | V.Tuple lst' -> compare_list lst lst'
    | V.Record _ | V.Variant _ -> OldUtils.Less )
  | V.Record lst -> (
    match v2 with
    | V.Closure _ | V.Handler _ -> OldUtils.Invalid
    | V.Const _ | V.Tuple _ -> OldUtils.Greater
    | V.Record lst' -> compare_record lst lst'
    | V.Variant _ -> OldUtils.Less )
  | V.Variant (lbl, u) ->
    match v2 with
    | V.Closure _ | V.Handler _ -> OldUtils.Invalid
    | V.Const _ | V.Tuple _ | V.Record _ -> OldUtils.Greater
    | V.Variant (lbl', u') ->
        let r = Pervasives.compare lbl lbl' in
        if r < 0 then OldUtils.Less
        else if r > 0 then OldUtils.Greater
        else compare_option u u'


and compare_list lst1 lst2 =
  match (lst1, lst2) with
  | [], [] -> OldUtils.Equal
  | u :: lst1, v :: lst2 -> (
    match compare u v with
    | OldUtils.Less -> OldUtils.Less
    | OldUtils.Equal -> compare_list lst1 lst2
    | OldUtils.Greater -> OldUtils.Greater
    | OldUtils.Invalid -> OldUtils.Invalid )
  | [], _ :: _ -> OldUtils.Less
  | _ :: _, [] -> OldUtils.Greater


and compare_record lst1 lst2 =
  (* Is is easiest to canonically sort the fields, then compare as lists. *)
  let rec comp = function
    | [], [] -> OldUtils.Equal
    | (fld1, v1) :: lst1, (fld2, v2) :: lst2 -> (
        let r = Pervasives.compare fld1 fld2 in
        if r < 0 then OldUtils.Less
        else if r > 0 then OldUtils.Greater
        else
          match compare v1 v2 with
          | OldUtils.Less -> OldUtils.Less
          | OldUtils.Equal -> comp (lst1, lst2)
          | OldUtils.Greater -> OldUtils.Greater
          | OldUtils.Invalid -> OldUtils.Invalid )
    | [], _ :: _ -> OldUtils.Less
    | _ :: _, [] -> OldUtils.Greater
  in
  comp
    ( List.sort (fun (fld1, _) (fld2, _) -> Pervasives.compare fld1 fld2) lst1
    , List.sort (fun (fld1, _) (fld2, _) -> Pervasives.compare fld1 fld2) lst2
    )


and compare_option o1 o2 =
  match (o1, o2) with
  | None, None -> OldUtils.Equal
  | Some v1, Some v2 -> compare v1 v2
  | None, Some _ -> OldUtils.Less
  | Some _, None -> OldUtils.Greater


(* Now it is easy to get equality and less than, not to mention we
   can now easily add a builtin "compare". *)
let equal v1 v2 =
  match compare v1 v2 with
  | OldUtils.Equal -> true
  | OldUtils.Less | OldUtils.Greater -> false
  | OldUtils.Invalid -> Error.runtime "invalid comparison with ="


let less_than v1 v2 =
  match compare v1 v2 with
  | OldUtils.Less -> true
  | OldUtils.Greater | OldUtils.Equal -> false
  | OldUtils.Invalid -> Error.runtime "invalid comparison with <"


let comparison_functions =
  [ ("=", binary_closure (fun v1 v2 -> value_bool (equal v1 v2)))
  ; ("<", binary_closure (fun v1 v2 -> value_bool (less_than v1 v2))) ]


let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
      let b = pow a (n / 2) in
      if n mod 2 = 0 then b * b else b * b * a


let arithmetic_operations =
  [ ("~-", from_fun (fun v -> value_int (-V.to_int v)))
  ; ("+", int_int_to_int ( + ))
  ; ("-", int_int_to_int ( - ))
  ; ("*", int_int_to_int ( * ))
  ; ("/", int_int_to_int ( / ))
  ; ("mod", int_int_to_int ( mod ))
  ; ("**", int_int_to_int pow)
  ; ("~-.", from_fun (fun v -> value_float ~-.(V.to_float v)))
  ; ("+.", float_float_to_float ( +. ))
  ; ("-.", float_float_to_float ( -. ))
  ; ("*.", float_float_to_float ( *. ))
  ; ("/.", float_float_to_float ( /. )) ]


(* let int_int_to_int f =
let int_f v1 v2 = value_int (f (V.to_int v1) (V.to_int v2)) in
binary_closure int_f *)

let string_string_to_list f =
	let ff v1 v2 =  value_list (List.map from_str (f (V.to_char v1) (V.to_str v2))) in
	binary_closure ff
    
    
let string_operations =
  [ ("^", binary_closure (fun v1 v2 -> value_str (V.to_str v1 ^ V.to_str v2)))
  ; ( "string_length", from_fun (fun v -> value_int (String.length (V.to_str v))) ) 
  ; ( "trim", from_fun (fun v -> value_str (String.trim (V.to_str v))) ) 
  ; ( "split_on_char", string_string_to_list String.split_on_char)
  
  (* ; ( "split_on_char", string_string_to_list (fun v -> value_str (String.trim (V.to_str v))) )  *)
  (* ; ( "split_on_char", from_fun (fun c -> value_fun (fun v -> f c v -> (String.split_on_char c (V.to_str v) )))) *)
    ]




let conversion_functions =
  [ ( "to_string"
    , let to_string v =
        Value.print_value v Format.str_formatter ;
        let s = Format.flush_str_formatter () in
        value_str s
      in
      from_fun to_string )
  ; ( "float_of_int"
    , from_fun (fun v -> value_float (float_of_int (V.to_int v))) ) ]


(** [values] is an association list of external names and values, consisting of
    comparison functions, arithmetic operations, string operations, conversion
    functions, and effect instances. *)
let values =
  comparison_functions @ arithmetic_operations @ string_operations
  @ conversion_functions
