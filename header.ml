type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation) -> 'a computation

and ('a, 'b) abstraction = {
  pure: 'a -> 'b;
  impure: 'a -> 'b computation;
}

type ('a, 'b) value_clause = ('a, 'b) abstraction

type ('a, 'b) finally_clause = ('a, 'b) abstraction

type ('eff_arg, 'eff_res, 'b) pure_effect_clauses =
  (('eff_arg, 'eff_res) effect -> ('eff_arg -> ('eff_res, 'b) abstraction -> 'b))

type ('eff_arg, 'eff_res, 'b) impure_effect_clauses =
  (('eff_arg, 'eff_res) effect -> ('eff_arg -> ('eff_res, 'b) abstraction -> 'b computation))

type ('a, 'b, 'c) handler =
  {
    value_clause : ('a, 'b) value_clause;
    finally_clause : ('b, 'c) finally_clause;
    pure_effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) pure_effect_clauses;
    impure_effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) impure_effect_clauses
  }



let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, (fun y -> (k y) >> f))
  
let compile_handler (h : ('a, 'b, _) handler) : ('a computation -> 'b computation) * ('a computation -> 'b)  =
  let rec handler =
    function
    | Value x -> h.value_clause.impure x
    | Call (eff, arg, k) ->
        let clause = h.impure_effect_clauses eff
        in clause arg ({ pure = (fun y -> pure_handler (k y)); impure = (fun y -> handler (k y))})
  and pure_handler =
    function
    | Value x -> h.value_clause.pure x
    | Call (eff, arg, k) ->
        let clause = h.pure_effect_clauses eff
        in clause arg ({ pure = (fun y -> pure_handler (k y)); impure = (fun y -> handler (k y))})
  in
  (handler, pure_handler)

let rec handle (h : ('a, 'b, 'c) handler) (c : 'a computation) : 'c computation =
  let handler, _ = compile_handler h in
  (handler c) >> h.finally_clause.impure

let rec pure_handle (h : ('a, 'b, 'c) handler) (c : 'a computation) : 'c =
  let _, pure_handler = compile_handler h in
  (h.finally_clause.pure) (pure_handler c) 

let value (x : 'a) : 'a computation = Value x
  
let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
  'c computation = Call (eff, arg, cont)
  
let effect eff arg = call eff arg value

let run =
  function
  | Value x -> x
  | Call _ -> failwith "Uncaught effect"

let ( ** ) =
  let rec pow a = Pervasives.(function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)) in
  pow
