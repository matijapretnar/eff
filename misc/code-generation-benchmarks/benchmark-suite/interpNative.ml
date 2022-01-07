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

let bigTestException num =
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
  let rec looper k s =
    if k = 0 then s
    else looper (k - 1) (s + try interp finalCase with DivByZero -> -1)
  in
  looper 100 0

let bigTestOption num =
  let rec interp = function
    | Num b -> Some b
    | Add (l, r) -> (
        let x = interp l in
        match x with
        | None -> None
        | Some x -> (
            let y = interp r in
            match y with None -> None | Some y -> Some (x + y)))
    | Mul (l, r) -> (
        let x = interp l in
        match x with
        | None -> None
        | Some x -> (
            let y = interp r in
            match y with None -> None | Some y -> Some (x * y)))
    | Sub (l, r) -> (
        let x = interp l in
        match x with
        | None -> None
        | Some x -> (
            let y = interp r in
            match y with None -> None | Some y -> Some (x - y)))
    | Div (l, r) -> (
        let y = interp r in
        match y with
        | None -> None
        | Some y -> (
            match interp l with
            | None -> None
            | Some x -> if y = 0 then None else Some (x / y)))
  in
  let finalCase = createCase num in
  let rec looper k s =
    if k = 0 then s
    else
      looper (k - 1) (s + match interp finalCase with None -> -1 | Some x -> x)
  in
  looper 100 0

let testState n =
  let rec interp b = function
    | Num b -> (b, b * b)
    | Add (l, r) ->
        let x, b = interp b l in
        let y, b = interp b r in
        (x + y, b)
    | Mul (l, r) ->
        let x, b = interp b l in
        let y, b = interp b r in
        (x * y, b)
    | Sub (l, r) ->
        let x, b = interp b l in
        let y, b = interp b r in
        (x - y, b)
    | Div (l, r) ->
        let y, b = interp b r in
        let x, b = interp b l in
        if y = 0 then (b, b) else (x / y, b)
  in
  let finalCase = createCase n in
  let rec looper k s =
    if k = 0 then s else looper (k - 1) (s + fst (interp n finalCase))
  in
  looper 100 0

(*

# testState 100;;
- : int = 12772

*)
