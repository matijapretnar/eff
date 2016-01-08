type effect_symbol = string

type ('eff_arg, 'eff_res) effect = effect_symbol

type 'a computation =
  | Value : 'a -> 'a computation
  | Call : ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation) -> 'a computation

type ('a, 'b) value_clause = 'a -> 'b computation
type ('a, 'b) finally_clause = 'a -> 'b computation

type 'a effect_clauses =
  | Nil : 'a effect_clauses
  | Cons : ('eff_arg, 'eff_res) effect * ('eff_arg -> ('eff_res -> 'a computation) -> 'a computation) * 'a effect_clauses -> 'a effect_clauses

type ('a, 'b) handler = {
  value: ('a, 'b) value_clause;
  effect_clauses: 'b effect_clauses;
}

let rec find_case : 'eff_arg 'eff_res. ('eff_arg, 'eff_res) effect -> 'a effect_clauses -> ('eff_arg -> ('eff_res -> 'a computation) -> 'a computation) =
  fun eff eff_clauses ->
    match eff_clauses with
    | Nil ->
      (fun x k -> Call (eff, x, k))
    | Cons (eff', case, eff_clauses) ->
      if eff = eff' then Obj.magic case else find_case eff eff_clauses

let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> k y >> f)

let rec handle (h : ('a, 'b) handler) (c : 'a computation) : 'b computation =
  match c with
  | Value x -> h.value x
  | Call (eff, arg, k) ->
    let f = find_case eff h.effect_clauses in
    f arg (fun y -> handle h (k y))

let value (x : 'a) : 'a computation = Value x

let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) : 'c computation =
  Call (eff, arg, cont)

let effect eff = fun arg -> call eff arg value

let run = function
  | Value x -> x
  | Call (eff, _, _) -> failwith ("Uncaught effect " ^ eff)

let (+) = fun x -> value (fun y -> value (Pervasives.(+) x y))
let (-) = fun x -> value (fun y -> value (Pervasives.(-) x y))
let ( * ) = fun x -> value (fun y -> value (Pervasives.( * ) x y))
let (/) = fun x -> value (fun y -> value (Pervasives.(/) x y))

let (+.) = fun x -> value (fun y -> value (Pervasives.(+.) x y))
let (-.) = fun x -> value (fun y -> value (Pervasives.(-.) x y))
let ( *. ) = fun x -> value (fun y -> value (Pervasives.( *. ) x y))
let (/.) = fun x -> value (fun y -> value (Pervasives.(/.) x y))

let (=) = fun x -> value (fun y -> value (Pervasives.(=) x y))
let (!=) = fun x -> value (fun y -> value (Pervasives.(!=) x y))
let (<>) = fun x -> value (fun y -> value (Pervasives.(<>) x y))
let (<) = fun x -> value (fun y -> value (Pervasives.(<) x y))
let (>) = fun x -> value (fun y -> value (Pervasives.(>) x y))
let (<=) = fun x -> value (fun y -> value (Pervasives.(<=) x y))
let (>=) = fun x -> value (fun y -> value (Pervasives.(>=) x y))

let (&&) = fun x -> value (fun y -> value (Pervasives.(&&) x y))
let (||) = fun x -> value (fun y -> value (Pervasives.(||) x y))
