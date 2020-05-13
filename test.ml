type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
        -> 'a computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
      (('eff_arg, 'eff_res) effect ->
      ('eff_arg -> ('eff_res -> 'b) -> 'b))

type ('a, 'b) handler_clauses =
  {
    value_clause : 'a -> 'b;
    effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses
  }

let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, (fun y -> (k y) >> f))

let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler =
    function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff
        in clause arg (fun y -> handler (k y))
  in
  handler

let value (x : 'a) : 'a computation = Value x

let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
  'c computation = Call (eff, arg, cont)

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let effect eff arg = call eff arg value

let run =
  function
  | Value x -> x
  | Call (eff, _, _) -> failwith ("Uncaught effect")

let ( ** ) =
  let rec pow a = Pervasives.(function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)) in
  pow

let string_length _ = assert false
let to_string _ = assert false

let lift_unary f = fun x -> value (f x)
let lift_binary f = fun x -> value (fun y -> value (f x y))

;;

_var_0 (* = *): ((int) -> ((int) -> (bool))) = =_var_1 (* < *): ((int) -> ((int) -> (bool))) = <_var_2 (* - *): ((int) -> ((int) -> (int))) = -type (_, _) effect += Fail : (unit, () (empty)) effect;;

let test_latent = (fun (n) -> (let rec loop_latent = (fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) (let _var_8 = ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (_var_0 (* = *))) (n))) in ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (_var_8)) (0)))) >> (fun (_var_7) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((match ((fun (coer_refl_x) -> (coer_refl_x)) (_var_7)) with | true -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) (())) | false -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) (let _var_10 = ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (_var_1 (* < *))) (n))) in ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (_var_10)) (0)))) >> (fun (_var_9) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((match ((fun (coer_refl_x) -> (coer_refl_x)) (_var_9)) with | true -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (effect Fail)) (())) >> (fun (_var_11) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((match (_var_11) with )))))) | false -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) (let _var_13 = ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (_var_2 (* - *))) (n))) in ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (_var_13)) (1)))) >> (fun (_var_12) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) ((fun (coer_x1) -> (fun (coer_x2) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (loop_latent))) (_var_12)))))) )))))) )))) in  (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (loop_latent)) (n)))) in (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (x) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x)))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (test_latent)) (10000))