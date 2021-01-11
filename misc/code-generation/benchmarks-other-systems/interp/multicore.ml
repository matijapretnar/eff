type term =
    | Num of int
    | Add of term * term
    | Mul of term * term
    | Sub of term * term
    | Div of term * term

effect DivByZero : (unit -> int)

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
    begin match y with
    | 0 -> perform DivByZero ()
    | _ -> x / y
    end

(******************************************************************************)

let addCase =
    Add (
        Add (
            Add ((Num 20), (Num 2)),
            Mul ((Num 1), (Num 2))
        ),
        Sub (
            Add ((Num 2), (Num 2)),
            Div ((Num 1), (Num 10))
        )
    );;

let rec createCase n =
    begin match n with
    | 1 -> (Div (Num 100, Num 0))
    | _ -> Add (addCase, (createCase (n - 1)))
    end

let finalCase = createCase 200

let bigTest () =
    match interp (createCase 200) with
    | x -> x
    | effect DivByZero k ->
        continue k (fun () -> -1);;
