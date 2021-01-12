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

let rec loop_pure n = if n = 0 then () else loop_pure (n - 1)

let test_pure n = loop_pure n

(******************************************************************************)

type (_, _) effect += Effect_fail : (unit, 'empty) effect

let fail () = call Effect_fail () (fun _ -> assert false)

let rec loop_latent n =
  if n = 0 then value () else if n < 0 then fail () else loop_latent (n - 1)

let test_latent n = loop_latent n

(******************************************************************************)

type (_, _) effect += Effect_incr : (unit, unit) effect

let incr () = call Effect_incr () value

let rec loop_incr n =
  if n = 0 then value () else incr () >> fun _ -> loop_incr (n - 1)

let incr_handler =
  handler
    {
      value_clause = (fun y x -> x);
      effect_clauses =
        (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
          match eff with Effect_incr -> fun () k x -> k () (x + 1));
    }

let test_incr n = incr_handler (loop_incr n) 0

let rec loop_incr' n =
  if n = 0 then value () else loop_incr' (n - 1) >> fun _ -> incr ()

let test_incr' n = incr_handler (loop_incr' n) 0

(******************************************************************************)

type (_, _) effect += Effect_get : (unit, int) effect

type (_, _) effect += Effect_put : (int, unit) effect

let get () = call Effect_get () value

let put s = call Effect_put s value

let rec loop_state n =
  if n = 0 then value ()
  else
    get () >> fun x ->
    put (x + 1) >> fun () -> loop_state (n - 1)

let state_handler =
  handler
    {
      value_clause = (fun y x -> x);
      effect_clauses =
        (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
          match eff with
          | Effect_put -> fun (s' : int) (k : unit -> _) _ -> k () s'
          | Effect_get -> fun () (k : int -> _) s -> k s s);
    }

let test_state n = state_handler (loop_state n) 0
