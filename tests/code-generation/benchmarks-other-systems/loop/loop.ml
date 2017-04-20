(*
=== GENERATED FROM loop.eff ===
commit SHA: 6c75bd3071f112cb37f7555615d859e4e3fe8423
=== BEGIN SOURCE ===

external ( = ) : int -> int -> bool = "="
external ( < ) : int -> int -> bool = "<"
external ( - ) : int -> int -> int = "-"
external ( + ) : int -> int -> int = "+"

effect Fail : unit -> int

let rec loop_latent n =
    if n = 0 then
        #Fail ()
    else if n < 0 then
        #Fail ()
    else
        loop_latent (n - 1)

let latent_handler = handler
| val y -> y
| #Fail () k -> k 0

let test_latent n =
    loop_latent n;;

let test_once () =
    with latent_handler handle (test_latent 10000);;

let rec test_many n =
    if n = 0 then
        ()
    else
        let a = test_once () in
        test_many (n - 1 + a);;

test_many 10000000

=== END SOURCE ===
*)

type ('eff_arg,'eff_res) effect = ..
type 'a computation =
  | Value: 'a -> 'a computation
  | Call: ('eff_arg,'eff_res) effect* 'eff_arg* ('eff_res -> 'a computation)
  -> 'a computation
type ('eff_arg,'eff_res,'b) effect_clauses =
  ('eff_arg,'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b
type ('a,'b) handler_clauses =
  {
  value_clause: 'a -> 'b;
  effect_clauses: 'eff_arg 'eff_res . ('eff_arg,'eff_res,'b) effect_clauses;}
let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> (k y) >> f)))
let rec handler (h : ('a,'b) handler_clauses) =
  (let rec handler =
     function
     | Value x -> h.value_clause x
     | Call (eff,arg,k) ->
         let clause = h.effect_clauses eff in
         clause arg (fun y  -> handler (k y)) in
   handler : 'a computation -> 'b)
let value (x : 'a) = (Value x : 'a computation)
let call (eff : ('a,'b) effect) (arg : 'a) (cont : 'b -> 'c computation) =
  (Call (eff, arg, cont) : 'c computation)
let rec lift (f : 'a -> 'b) =
  (function
   | Value x -> Value (f x)
   | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> lift f (k y)))) : 
  'a computation -> 'b computation)
let effect eff arg = call eff arg value
let run =
  function | Value x -> x | Call (eff,_,_) -> failwith "Uncaught effect"
let ( ** ) =
  let rec pow a =
    let open Pervasives in
      function
      | 0 -> 1
      | 1 -> a
      | n ->
          let b = pow a (n / 2) in (b * b) * (if (n mod 2) = 0 then 1 else a) in
  pow
let string_length _ = assert false
let to_string _ = assert false
let lift_unary f x = value (f x)
let lift_binary f x = value (fun y  -> value (f x y))
let _ = "End of pervasives"
let _var_1 = (=)
let _var_2 = (<)
let _var_3 = (-)
let _var_4 = (+)
type (_,_) effect +=
  | Effect_Fail: (unit,int) effect
let rec _loop_latent_5 _n_6 =
  if _n_6 = 0
  then call Effect_Fail () (fun _result_2  -> value _result_2)
  else
    if _n_6 < 0
    then call Effect_Fail () (fun _result_4  -> value _result_4)
    else _loop_latent_5 (_n_6 - 1)
let _latent_handler_13 comp =
  handler
    {
      value_clause = (fun _y_15  -> value _y_15);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Fail  ->
               (fun (() : unit)  -> fun (_k_14 : int -> _)  -> _k_14 0)
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
let _test_latent_16 _n_17 = _loop_latent_5 _n_17
let _test_once_18 () =
  let rec _loop_latent_9 _n_6 =
    if _n_6 = 0 then 0 else if _n_6 < 0 then 0 else _loop_latent_9 (_n_6 - 1) in
  _loop_latent_9 10000
let rec _test_many_19 _n_20 =
  if _n_20 = 0 then () else _test_many_19 ((_n_20 - 1) + (_test_once_18 ()))
let _ = _test_many_19 10000000
