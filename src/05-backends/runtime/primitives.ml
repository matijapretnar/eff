open Utils
open Language
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

(** [int_to_int f] takes a unary integer function f and transforms it into
    a closure that takes two values and evaluates to a value. *)
let int_to_int f = from_fun (fun v -> value_int (f (V.to_int v)))

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
  | V.Closure _ | V.Handler _ -> Const.Invalid
  | V.Const c -> (
      match v2 with
      | V.Closure _ | V.Handler _ | V.TypeCoercionClosure _
      | V.DirtCoercionClosure _ ->
          Invalid
      | V.Const c' -> Const.compare c c'
      | V.Tuple _ | V.Record _ | V.Variant _ -> Less)
  | V.Tuple lst -> (
      match v2 with
      | V.Closure _ | V.Handler _ | V.TypeCoercionClosure _
      | V.DirtCoercionClosure _ ->
          Invalid
      | V.Const _ -> Greater
      | V.Tuple lst' -> compare_list lst lst'
      | V.Record _ | V.Variant _ -> Less)
  | V.Record lst -> (
      match v2 with
      | V.Closure _ | V.Handler _ | V.TypeCoercionClosure _
      | V.DirtCoercionClosure _ ->
          Invalid
      | V.Const _ | V.Tuple _ -> Greater
      | V.Record lst' -> compare_record lst lst'
      | V.Variant _ -> Less)
  | V.Variant (lbl, u) -> (
      match v2 with
      | V.Closure _ | V.Handler _ | V.TypeCoercionClosure _
      | V.DirtCoercionClosure _ ->
          Invalid
      | V.Const _ | V.Tuple _ | V.Record _ -> Greater
      | V.Variant (lbl', u') ->
          let r = Stdlib.compare lbl lbl' in
          if r < 0 then Less else if r > 0 then Greater else compare_option u u'
      )
  | V.TypeCoercionClosure _ | V.DirtCoercionClosure _ -> Invalid

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
    | [], [] -> Const.Equal
    | (fld1, v1) :: lst1, (fld2, v2) :: lst2 -> (
        let r = Stdlib.compare fld1 fld2 in
        if r < 0 then Less
        else if r > 0 then Greater
        else
          match compare v1 v2 with
          | Less -> Less
          | Const.Equal -> comp (lst1, lst2)
          | Greater -> Greater
          | Invalid -> Invalid)
    | [], _ :: _ -> Less
    | _ :: _, [] -> Greater
  in
  let lst1' = Type.Field.Map.bindings lst1 in
  let lst2' = Type.Field.Map.bindings lst2 in
  comp
    ( List.sort (fun (fld1, _) (fld2, _) -> Stdlib.compare fld1 fld2) lst1',
      List.sort (fun (fld1, _) (fld2, _) -> Stdlib.compare fld1 fld2) lst2' )

and compare_option o1 o2 =
  match (o1, o2) with
  | None, None -> Const.Equal
  | Some v1, Some v2 -> compare v1 v2
  | None, Some _ -> Less
  | Some _, None -> Greater

(* Now it is easy to get equality and less than, not to mention we
   can now easily add a builtin "compare". *)
let equal v1 v2 =
  match compare v1 v2 with
  | Const.Equal -> true
  | Less | Greater -> false
  | Invalid -> Error.runtime "invalid comparison with ="

let not_equal v1 v2 = not (equal v1 v2)

let less_than v1 v2 =
  match compare v1 v2 with
  | Const.Less -> true
  | Greater | Equal -> false
  | Invalid -> Error.runtime "invalid comparison with <"

let greater_than v1 v2 = less_than v2 v1
let greater_than_or_equal v1 v2 = greater_than v1 v2 || equal v1 v2
let less_than_or_equal v1 v2 = less_than v1 v2 || equal v1 v2

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
      let b = pow a (n / 2) in
      if n mod 2 = 0 then b * b else b * b * a

let primitive_value = function
  | Primitives.CompareEq ->
      binary_closure (fun v1 v2 -> value_bool (equal v1 v2))
  | Primitives.CompareGe ->
      binary_closure (fun v1 v2 -> value_bool (greater_than_or_equal v1 v2))
  | Primitives.CompareGt ->
      binary_closure (fun v1 v2 -> value_bool (greater_than v1 v2))
  | Primitives.CompareLe ->
      binary_closure (fun v1 v2 -> value_bool (less_than_or_equal v1 v2))
  | Primitives.CompareLt ->
      binary_closure (fun v1 v2 -> value_bool (less_than v1 v2))
  | Primitives.CompareNe ->
      binary_closure (fun v1 v2 -> value_bool (not_equal v1 v2))
  | Primitives.FloatAcos -> float_to_float acos
  | Primitives.FloatAdd -> float_float_to_float ( +. )
  | Primitives.FloatAsin -> float_to_float asin
  | Primitives.FloatAtan -> float_to_float atan
  | Primitives.FloatCos -> float_to_float cos
  | Primitives.FloatDiv -> float_float_to_float ( /. )
  | Primitives.FloatExp -> float_to_float exp
  | Primitives.FloatExpm1 -> float_to_float expm1
  | Primitives.FloatInfinity -> from_float infinity
  | Primitives.FloatLog -> float_to_float log
  | Primitives.FloatLog1p -> float_to_float log1p
  | Primitives.FloatMul -> float_float_to_float ( *. )
  | Primitives.FloatNaN -> from_float nan
  | Primitives.FloatNeg -> from_fun (fun v -> value_float ~-.(V.to_float v))
  | Primitives.FloatNegInfinity -> from_float neg_infinity
  | Primitives.FloatOfInt ->
      from_fun (fun v -> value_float (float_of_int (V.to_int v)))
  | Primitives.FloatSin -> float_to_float sin
  | Primitives.FloatSqrt -> float_to_float sqrt
  | Primitives.FloatSub -> float_float_to_float ( -. )
  | Primitives.FloatTan -> float_to_float tan
  | Primitives.IntegerAdd -> int_int_to_int ( + )
  | Primitives.IntegerDiv -> int_int_to_int ( / )
  | Primitives.IntegerMod -> int_int_to_int ( mod )
  | Primitives.IntegerMul -> int_int_to_int ( * )
  | Primitives.IntegerNeg -> from_fun (fun v -> value_int (-V.to_int v))
  | Primitives.IntegerAbs -> int_to_int abs
  | Primitives.IntegerPow -> int_int_to_int pow
  | Primitives.IntegerSub -> int_int_to_int ( - )
  | Primitives.IntOfFloat ->
      from_fun (fun v -> value_int (int_of_float (V.to_float v)))
  | Primitives.StringConcat ->
      binary_closure (fun v1 v2 -> value_str (V.to_str v1 ^ V.to_str v2))
  | Primitives.StringLength ->
      from_fun (fun v -> value_int (String.length (V.to_str v)))
  | Primitives.StringOfFloat ->
      from_fun (fun v -> value_str (string_of_float (V.to_float v)))
  | Primitives.StringOfInt ->
      from_fun (fun v -> value_str (string_of_int (V.to_int v)))
  | Primitives.StringSub ->
      ternary_closure (fun v1 v2 v3 ->
          value_str (String.sub (V.to_str v1) (V.to_int v2) (V.to_int v3)))
  | Primitives.ToString ->
      let to_string v =
        V.print_value v Format.str_formatter;
        let s = Format.flush_str_formatter () in
        value_str s
      in
      from_fun to_string

let runner prim v =
  match prim with
  | Primitives.Print ->
      let str = V.to_str v in
      Format.pp_print_string !Config.output_formatter str;
      Format.pp_print_flush !Config.output_formatter ();
      V.unit_value
  | Primitives.Raise -> Error.runtime "%t" (V.print_value v)
  | Primitives.RandomInt ->
      let rnd_int = Random.int (V.to_int v) in
      let rnd_int_v = V.Const (Const.of_integer rnd_int) in
      rnd_int_v
  | Primitives.RandomFloat ->
      let rnd_float = Random.float (V.to_float v) in
      let rnd_float_v = V.Const (Const.of_float rnd_float) in
      rnd_float_v
  | Primitives.Read ->
      let str = read_line () in
      let str_v = V.Const (Const.of_string str) in
      str_v
  | Primitives.Write -> (
      match v with
      | V.Tuple [ V.Const (Const.String file_name); V.Const (Const.String str) ]
        ->
          let file_handle =
            open_out_gen
              [ Open_wronly; Open_append; Open_creat; Open_text ]
              0o666 file_name
          in
          Printf.fprintf file_handle "%s" str;
          close_out file_handle;
          V.unit_value
      | _ -> Error.runtime "A pair of a file name and string expected")
