type empty

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

let handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler = function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff in
        clause arg (fun y -> handler (k y))
  in
  handler

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let run = function Value x -> x | Call (_, _, _) -> failwith "Uncaught effect"

let ( ** ) =
  let rec pow a =
    Stdlib.(
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

let lift_unary f x = Value (f x)

let lift_binary f x = Value (fun y -> Value (f x y))

let coer_refl_ty term = term

let rec coer_computation coer comp =
  match comp with
  | Value t -> Value (coer t)
  | Call (eff, arg, k) -> Call (eff, arg, fun x -> coer_computation coer (k x))

let coer_return coer term = Value (coer term)

let coer_unsafe coer = function
  | Value v -> coer v
  | Call (_eff, _arg, _k) -> failwith "Unsafe coercion"

let force_unsafe = function
  | Value v -> v
  | Call (_eff, _arg, _k) -> failwith "Unsafe value force"

let coer_arrow coer1 coer2 f x = coer2 (f (coer1 x))

let coer_handler coer1 coer2 h x = coer2 (h (coer1 x))

let coer_hand_to_fun coer1 coer2 h x = coer2 (h (Value (coer1 x)))

let rec coer_fun_to_hand coer1 coer2 f comp =
  match comp with
  | Value t -> coer2 (f (coer1 t))
  | Call (eff, arg, k) ->
      Call (eff, arg, fun x -> coer_fun_to_hand coer1 coer2 f (k x))

let _op_0 (* < *) = ( < )

let _op_1 (* = *) = ( = )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let _op_4 (* ~- *) = ( ~- )

type (_, _) effect += Decide : (unit, bool) effect

type (_, _) effect += Fail : (unit, empty) effect

type inttuple = IntTuple of (int * int)

type intlist = IntNil | IntCons of (int * intlist)

type inttuplist = IntTupNil | IntTupCons of (inttuple * inttuplist)

type void = Void

;;
(fun (n : int) ->
  let absurd (void : empty) = match void with _ -> assert false in
  let _op_9 (* > *) (x : int) (y : int) = (_op_0 (* < *) y) x in
  let _op_13 (* <> *) (x : int) (y : int) =
    match (_op_1 (* = *) y) x with true -> false | false -> true
  in
  let abs (x : int) =
    match (_op_0 (* < *) x) 0 with true -> _op_4 (* ~- *) x | false -> x
  in
  let no_attack (q1 : inttuple) (q2 : inttuple) =
    match q1 with
    | IntTuple (x, y) -> (
        match q2 with
        | IntTuple (x', y') -> (
            match (_op_13 (* <> *) x) x' with
            | true -> (
                match (_op_13 (* <> *) y) y' with
                | true ->
                    (_op_13 (* <> *) (abs ((_op_2 (* - *) x) x')))
                      (abs ((_op_2 (* - *) y) y'))
                | false -> false)
            | false -> false))
  in
  let rec not_attacked x' (qs : inttuplist) =
    match qs with
    | IntTupNil -> true
    | IntTupCons (x, xs) -> (
        match (no_attack x') x with
        | true -> (not_attacked x') xs
        | false -> false)
  in
  let available (number_of_queens : int) (x : int) (qs : inttuplist) =
    let rec loop possible (y : int) =
      match (_op_0 (* < *) y) 1 with
      | true -> possible
      | false -> (
          match (not_attacked (IntTuple (x, y))) qs with
          | true -> (loop (IntCons (y, possible))) ((_op_2 (* - *) y) 1)
          | false -> (loop possible) ((_op_2 (* - *) y) 1))
    in
    (loop IntNil) number_of_queens
  in
  let rec choose xs =
    match xs with
    | IntNil ->
        (fun (x : unit) -> Call (Fail, x, fun (y : empty) -> Value y)) ()
        >> fun _b_68 -> Value (match _b_68 with _ -> assert false)
    | IntCons (x, xs') -> (
        (fun (x : unit) -> Call (Decide, x, fun (y : bool) -> Value y)) ()
        >> fun _b_71 -> match _b_71 with true -> Value x | false -> choose xs')
  in
  let backtrack =
    handler
      {
        value_clause =
          (fun (_x_79 : inttuplist) ->
            Value
              ((coer_arrow coer_refl_ty (coer_return coer_refl_ty))
                 (fun (_ : unit -> inttuplist computation) -> _x_79)));
        effect_clauses =
          (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
            match eff with
            | Decide ->
                fun _ l ->
                  Value
                    (fun (kf : unit -> inttuplist computation) ->
                      (((coer_arrow coer_refl_ty force_unsafe) l) true)
                        (fun (_ : unit) ->
                          (((coer_arrow coer_refl_ty force_unsafe) l) false) kf))
            | Fail ->
                fun _ l ->
                  Value (fun (kf : unit -> inttuplist computation) -> kf ())
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
  in
  let queens (number_of_queens : int) =
    let rec place x (qs : inttuplist) =
      match (_op_9 (* > *) x) number_of_queens with
      | true -> Value qs
      | false ->
          choose (((available number_of_queens) x) qs) >> fun y ->
          (place ((_op_3 (* + *) x) 1)) (IntTupCons (IntTuple (x, y), qs))
    in
    (place 1) IntTupNil
  in
  (fun (number_of_queens : int) ->
    (force_unsafe (backtrack (queens number_of_queens))) (fun (() : unit) ->
        (fun (x : unit) -> Call (Fail, x, fun (y : empty) -> Value y)) ()
        >> fun _b_100 -> Value (absurd _b_100)))
    n)
  8
