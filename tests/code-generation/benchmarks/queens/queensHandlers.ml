type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
        -> 'a computation

type ('a, 'b) value_clause = 'a -> 'b computation

type ('a, 'b) finally_clause = 'a -> 'b computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
      (('eff_arg, 'eff_res) effect ->
      ('eff_arg -> ('eff_res -> 'b computation) -> 'b computation))

type ('a, 'b, 'c) handler =
  { value_clause : ('a, 'b) value_clause;
    finally_clause : ('b, 'c) finally_clause;
    effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses
  }

let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, (fun y -> (k y) >> f))
  
let rec handle (h : ('a, 'b, 'c) handler) (c : 'a computation) :
  'c computation =
  let rec handler =
    function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff
        in clause arg (fun y -> handler (k y))
  in (handler c) >> h.finally_clause
  
let value (x : 'a) : 'a computation = Value x
  
let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
  'c computation = Call (eff, arg, cont)
  
let effect eff arg = call eff arg value

let run =
  function
  | Value x -> x
  | Call (eff, _, _) -> failwith ("Uncaught effect")

(******************************************************************************)

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available number_of_queens x qs =
  let rec loop possible y =
    if y < 1 then
      possible
    else if List.for_all (no_attack (x, y)) qs then
      loop (y :: possible) (y - 1)
    else
      loop possible (y - 1)
  in
  loop [] number_of_queens

(******************************************************************************)

type (_, _) effect += Effect_decide : (unit, bool) effect
type (_, _) effect += Effect_fail : (unit, 'empty) effect

let decide x = call Effect_decide () value
let fail () = call Effect_fail () (fun _ -> assert false)

(******************************************************************************)

let rec choose = function
  | [] -> fail ()
  | x :: xs -> decide () >> fun b -> if b then value x else choose xs

let backtrack = {
  value_clause = value;
  finally_clause = value;
  effect_clauses = fun (type a) (type b) (eff : (a, b) effect) -> (
    match eff with
    | Effect_decide -> fun _ k ->
        handle {
          value_clause = value;
          finally_clause = value;
          effect_clauses = fun (type a) (type b) (eff : (a, b) effect) -> (
            match eff with
            | Effect_fail -> fun _ _ -> k false
            | eff -> fun arg k -> Call (eff, arg, k)
            :
            a -> (b -> _ computation) -> _ computation
          )
        } (k true)
    | eff -> fun arg k -> Call (eff, arg, k)
    :
    a -> (b -> _ computation) -> _ computation
  )
}

let choose_all = {
  value_clause = (fun x -> value [x]);
  finally_clause = value;
  effect_clauses = fun (type a) (type b) (eff : (a, b) effect) -> (
    match eff with
    | Effect_decide -> fun _ k ->
        k true >> fun lst1 ->
        k false >> fun lst2 ->
        value (lst1 @ lst2)
    | Effect_fail -> fun _ _ ->
        value []
    | eff -> fun arg k -> Call (eff, arg, k)
    :
    a -> (b -> _ computation) -> _ computation
  )
}

(******************************************************************************)

let queens number_of_queens =
  let rec place x qs =
    if x > number_of_queens then value qs else
      choose (available number_of_queens x qs) >>
      fun y -> (place (x + 1) ((x, y) :: qs))
  in
  place 1 []

let queens_one number_of_queens =
  handle backtrack (queens number_of_queens)

let queens_all number_of_queens =
  handle choose_all (queens number_of_queens)
