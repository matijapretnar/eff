type t =
  | Integer of int
  | String of string
  | Boolean of bool
  | Float of float

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

let compare c1 c2 =
  let cmp x y =
    let r = Pervasives.compare x y in
      if r < 0 then Common.Less
      else if r > 0 then Common.Greater
      else Common.Equal
  in
    match c1 with
      | Integer k ->
        (match c2 with
          | Integer k' -> 
            let r = Pervasives.compare k k' in
              if r < 0 then Common.Less
              else if r > 0 then Common.Greater
              else Common.Equal
          | String _ | Boolean _ | Float _ -> Common.Less)
    | String s ->
      (match c2 with
        | Integer _ -> Common.Greater
        | String s' -> cmp s s'
        | Boolean _ | Float _ -> Common.Less)
    | Boolean b ->
      (match c2 with
        | Integer _ | String _ -> Common.Greater
        | Boolean b' -> cmp b b'
        | Float _ -> Common.Less)
    | Float x ->
      (match c2 with
        | Integer _ | String _ | Boolean _ -> Common.Greater
        | Float x' -> cmp x x')

let equal c1 c2 = (compare c1 c2 = Common.Equal)
