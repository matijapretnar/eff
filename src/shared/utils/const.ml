open CoreUtils

type t = Integer of int | String of string | Boolean of bool | Float of float

type ty = IntegerTy | StringTy | BooleanTy | FloatTy

let of_integer n = Integer n

let of_string s = String s

let of_boolean b = Boolean b

let of_float f = Float f

let of_true = of_boolean true

let of_false = of_boolean false

let print c ppf =
  match c with
  | Integer k -> Format.fprintf ppf "%d" k
  | String s -> Format.fprintf ppf "%S" s
  | Boolean b -> Format.fprintf ppf "%B" b
  | Float f -> Format.fprintf ppf "%F" f

let print_ty c ppf =
  match c with
  | IntegerTy -> Format.fprintf ppf "int"
  | StringTy -> Format.fprintf ppf "string"
  | BooleanTy -> Format.fprintf ppf "bool"
  | FloatTy -> Format.fprintf ppf "float"

let infer_ty = function
  | Integer _ -> IntegerTy
  | String _ -> StringTy
  | Boolean _ -> BooleanTy
  | Float _ -> FloatTy

let compare c1 c2 =
  let cmp x y =
    let r = Stdlib.compare x y in
    if r < 0 then CoreUtils.Less
    else if r > 0 then CoreUtils.Greater
    else CoreUtils.Equal
  in
  match (c1, c2) with
  | Integer n1, Integer n2 -> cmp n1 n2
  | String s1, String s2 -> cmp s1 s2
  | Boolean b1, Boolean b2 -> cmp b1 b2
  | Float x1, Float x2 -> cmp x1 x2
  | _ -> Error.runtime "Incomparable constants %t and %t" (print c1) (print c2)

let equal c1 c2 = compare c1 c2 = Equal
