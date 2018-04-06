type t =
  | Char of char
  | Integer of int
  | String of string
  | Boolean of bool
  | Float of float
  | In_channel of in_channel
  | Out_channel of out_channel


let of_in_channel n = In_channel n
let of_out_channel n = Out_channel n

let of_char c = Char c

let of_integer n = Integer n

let of_string s = String s

let of_boolean b = Boolean b

let of_float f = Float f

let of_true = of_boolean true

let of_false = of_boolean false

let print c ppf =
  match c with
  | Char k -> Format.fprintf ppf "%c" k
  | Integer k -> Format.fprintf ppf "%d" k
  | String s -> Format.fprintf ppf "%S" s
  | Boolean b -> Format.fprintf ppf "%B" b
  | Float f -> Format.fprintf ppf "%F" f
  | In_channel f -> Format.fprintf ppf "<In channel>"
  | Out_channel f -> Format.fprintf ppf "<Out channel>" 


let compare c1 c2 =
  let cmp x y =
    let r = Pervasives.compare x y in
    if r < 0 then OldUtils.Less
    else if r > 0 then OldUtils.Greater
    else OldUtils.Equal
  in
  match (c1, c2) with
  | Integer n1, Integer n2 -> cmp n1 n2
  | String s1, String s2 -> cmp s1 s2
  | Boolean b1, Boolean b2 -> cmp b1 b2
  | Float x1, Float x2 -> cmp x1 x2
  | Char x1, Char x2 -> cmp x1 x2
  | _ -> Error.runtime "Incomparable constants %t and %t" (print c1) (print c2)


let equal c1 c2 = compare c1 c2 = OldUtils.Equal
