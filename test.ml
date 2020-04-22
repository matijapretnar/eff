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

effect (unit, int) Dummy 

let (h9) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (3))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h8) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h9)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h7) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h8)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h6) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h7)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h5) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h6)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h4) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h5)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h3) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h4)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h2) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) ((x1) (Value ((fun (coer_refl_x) -> (coer_refl_x)) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h3)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in (let (h1) = ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (y)) ))) ((x1) (Value ((fun (x) -> ((match (x) with | Value (y) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (y)) ))) (x2))))))) (fun c -> ((handler {value_clause = (fun (y) -> (Value ((fun (coer_refl_x) -> (coer_refl_x)) (let (x) = ((fun (coer_refl_x) -> (coer_refl_x)) (y)) 
in (x))))); effect_clauses = (fun (x : (a, b) effect) -> (match x with | Dummy -> (fun ((_ : unit), (l : int -> _ computation)) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (coer_refl_x) -> (coer_refl_x)) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (h2)) ((fun (coer_refl_x) -> (coer_refl_x)) (3))))) | eff' -> (fun (arg, k) -> Call (eff', arg, k)))) }) c))) 
in ((fun (x) -> ((match (x) with | Value (y) -> (fun (coer_refl_x) -> (coer_refl_x)) (y) ))) (((fun (x) -> ((match (x) with | Value (y) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (y)) ))) (((fun (coer_x1) -> (fun (coer_x2) -> ((fun (x) -> ((match (x) with | Value (y) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (y)) ))) ((coer_x1) ((fun (coer_refl_x) -> (coer_refl_x)) (coer_x2)))))) (effect Dummy)) (()))) ((fun (x1) -> (fun (x2) -> ((fun (x) -> ((match (x) with | Value (y) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (y)) ))) ((x1) (Value ((fun (x) -> ((match (x) with | Value (y) -> Value ((fun (coer_refl_x) -> (coer_refl_x)) (y)) ))) (x2))))))) (h1))))))))))))