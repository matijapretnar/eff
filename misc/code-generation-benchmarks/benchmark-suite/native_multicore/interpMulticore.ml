(******************************************************************************)

type term =
    | Num of int
    | Add of term * term
    | Mul of term * term
    | Sub of term * term
    | Div of term * term

effect DivByZero : unit -> int

(******************************************************************************)

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
    begin match y with
    | 0 -> perform (DivByZero ())
    | _ -> x / y
    end
  in
  let finalCase = createCase num in
  let rec looper k s = 
    if k = 0 then s else looper (k-1) (s + (match 
    interp finalCase
  with 
  | effect (DivByZero ()) k -> -1
  | x -> x))
  in
  looper 100 0


effect Get: unit -> int
effect Set: int -> unit
;;
let testState num = 
  let rec interp = function
  | Num b -> 
    perform (Set (b*b));
    b
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
    | 0 -> perform (Get ())
    | _ -> x / y
    end
  in
  let finalCase = createCase num in
  let rec looper k s = 
    if k = 0 then s else looper (k-1) (s + ((match interp finalCase with
    | y -> (fun _ -> y)
    | effect (Get ()) k -> (
      fun (s: int) -> 
        (continue k s) s
      )
    | effect (Set s) k -> (
      fun _ -> (continue k ()) s
    ) ) (num)))
  in
  looper 100 0
  

(*

# testState 100;;
- : int = 12772

*)