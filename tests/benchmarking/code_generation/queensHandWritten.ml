type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
      -> 'a computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
  ('eff_arg, 'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b

type ('a, 'b) handler_clauses = {
  value_clause : 'a -> 'b;
  effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses;
}

let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> k y >> f)

let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler = function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff in
        clause arg (fun y -> handler (k y))
  in
  handler

let value (x : 'a) : 'a computation = Value x

let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
    'c computation =
  Call (eff, arg, cont)

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let effect eff arg = call eff arg value

let run = function
  | Value x -> x
  | Call (eff, _, _) -> failwith "Uncaught effect"

let ( ** ) =
  let rec pow a =
    Pervasives.(
      function
      | 0 -> 1
      | 1 -> a
      | n ->
          let b = pow a (n / 2) in
          b * b * if n mod 2 = 0 then 1 else a)
  in
  pow

let string_length _ = assert false

let to_string _ = assert false

let lift_unary f x = value (f x)

let lift_binary f x = value (fun y -> value (f x y))

(******************************************************************************)

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec not_attacked x' = function
  | [] -> true
  | x :: xs -> if no_attack x' x then not_attacked x' xs else false

let available (number_of_queens, x, qs) =
  let rec loop (possible, y) =
    if y < 1 then possible
    else if not_attacked (x, y) qs then loop (y :: possible, y - 1)
    else loop (possible, y - 1)
  in
  loop ([], number_of_queens)

(******************************************************************************)

type (_, _) effect += Effect_decide : (unit, bool) effect

type (_, _) effect += Effect_fail : (unit, 'empty) effect

let decide x = call Effect_decide () value

let fail () = call Effect_fail () (fun _ -> assert false)

(******************************************************************************)

let rec choose = function
  | [] -> fail ()
  | x :: xs -> decide () >> fun b -> if b then value x else choose xs

let backtrack =
  handler
    {
      value_clause = (fun y _ -> y);
      effect_clauses =
        (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
          match eff with
          | Effect_decide -> fun _ k kf -> k true (fun () -> k false kf)
          | Effect_fail -> fun _ _ kf -> kf ());
    }

let optionalize =
  handler
    {
      value_clause = (fun y -> Some y);
      effect_clauses =
        (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
          match eff with
          | Effect_decide -> (
              fun _ k -> match k true with Some x -> Some x | None -> k false)
          | Effect_fail -> fun _ _ -> None);
    }

let choose_all =
  handler
    {
      value_clause = (fun x -> [ x ]);
      effect_clauses =
        (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
          match eff with
          | Effect_decide -> fun _ k -> k true @ k false
          | Effect_fail -> fun _ _ -> []);
    }

(******************************************************************************)

let queens number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then value qs
    else
      choose (available (number_of_queens, x, qs)) >> fun y ->
      place (x + 1, (x, y) :: qs)
  in
  place (1, [])

let queens_one_option number_of_queens = optionalize (queens number_of_queens)

let queens_one_cps number_of_queens =
  (backtrack (queens number_of_queens)) (fun () -> assert false)

let queens_all number_of_queens = choose_all (queens number_of_queens)
