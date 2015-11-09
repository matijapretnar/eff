type effect_symbol = string

type ('eff_arg, 'eff_res) effect = effect_symbol

type 'a computation =
  | Value : 'a -> 'a computation
  | Call : ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation) -> 'a computation

type ('a, 'b) value_case = 'a -> 'b computation
type ('a, 'b) finally_case = 'a -> 'b computation

type _ effect_cases =
  | Nil : 'a effect_cases
  | Cons : ('eff_arg, 'eff_res) effect * ('eff_arg -> ('eff_res -> 'a computation) -> 'a computation) * 'a effect_cases -> 'a effect_cases

type ('a, 'b, 'c) handler = {
  value: ('a, 'b) value_case;
  effect_cases: 'b effect_cases;
}

let rec find_case : 'eff_arg 'eff_res. ('eff_arg, 'eff_res) effect -> 'a effect_cases -> ('eff_arg -> ('eff_res -> 'a computation) -> 'a computation) =
  fun eff eff_cases ->
    match eff_cases with
    | Nil ->
      (fun x k -> Call (eff, x, k))
    | Cons (eff', case, eff_cases) ->
      if eff = eff' then Obj.magic case else find_case eff eff_cases

let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> k y >> f)

let rec handle (h : ('a, _, 'b) handler) (c : 'a computation) : 'b computation =
  match c with
  | Value x -> h.value x
  | Call (eff, arg, k) ->
    let f = find_case eff h.effect_cases in
    f arg (fun y -> handle h (k y))

let value (x : 'a) : 'a computation = Value x

let apply_effect (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) : 'c computation =
  Call (eff, arg, cont)

let run = function
  | Value x -> x
  | Call (eff, _, _) -> failwith ("Uncaught effect " ^ eff)

(*
let abs = fun x -> value (if x < 0 then -x else x)
let (<) = fun x -> value (fun y -> value (x < y))
let (=) = fun x -> value (fun y -> value (x = y))
let (+) = fun x -> value (fun y -> value (x + y))
let (&&) = fun x -> value (fun y -> value (x && y))
let (<>) = fun x -> value (fun y -> value (x <> y))
let (-) = fun x -> value (fun y -> value (x - y))
let raise exc = value (fun x -> Call (("raise", exc), x, fun _ -> assert false))
*)
