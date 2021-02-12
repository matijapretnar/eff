type term =
  | Num of int
  | Add of term * term
  | Mul of term * term
  | Sub of term * term
  | Div of term * term

exception DivByZero

let addCase =
  Add
    ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
      Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )

let rec createZeroCase n =
  match n with
  | 0 -> Sub (addCase, addCase)
  | n -> Sub (createZeroCase (n - 1), createZeroCase (n - 1))

let rec createCase n =
  match n with
  | 1 -> Div (Num 100, createZeroCase 3)
  | _ -> Add (addCase, createCase (n - 1))

let bigTest num =
  let rec interp = function
    | Num b -> b
    | Add (l, r) ->
        let x = interp l in
        let y = interp r in
        x + y
    | Mul (l, r) ->
        let x = interp l in
        let y = interp r in
        x * y
    | Sub (l, r) ->
        let x = interp l in
        let y = interp r in
        x - y
    | Div (l, r) ->
        let y = interp r in
        let x = interp l in
        if y = 0 then raise DivByZero else x / y
  in

  let finalCase = createCase num in
  try interp finalCase with DivByZero -> -1
