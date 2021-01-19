(*
=== GENERATED FROM loop.eff ===
commit SHA: 10c3083ed943a7b344260277712d720fe6044a42
=== BEGIN SOURCE ===

external ( = ) : int -> int -> bool = "="
external ( < ) : int -> int -> bool = "<"
external ( - ) : int -> int -> int = "-"
external ( + ) : int -> int -> int = "+"

(******************************************************************************)

let rec loop_pure n =
    if n = 0 then
        ()
    else
        loop_pure (n - 1)

let test_pure n =
    loop_pure n

(******************************************************************************)

effect Fail : unit -> empty

let rec loop_latent n =
    if n = 0 then
        ()
    else if n < 0 then
        (match #Fail () with)
    else
        loop_latent (n - 1)

let test_latent n =
    loop_latent n

(******************************************************************************)

effect Incr : unit -> unit

let rec loop_incr n =
    if n = 0 then
        ()
    else
        (#Incr (); loop_incr (n - 1))

let incr_handler = handler
| val y -> (fun x -> x)
| #Incr () k -> (fun x -> k () (x + 1))

let test_incr n =
    (with incr_handler handle loop_incr n) 0

(******************************************************************************)

let rec loop_incr' n =
    if n = 0 then
        ()
    else
        (loop_incr' (n - 1); #Incr ())

let test_incr' n =
    (with incr_handler handle loop_incr' n) 0

(******************************************************************************)

effect Get: unit -> int
effect Put: int -> unit

let rec loop_state n =
    if n = 0 then
        ()
    else
        (#Put ((#Get ()) + 1); loop_state (n - 1))

let state_handler = handler
| val y -> (fun x -> x)
| #Get () k -> (fun s -> k s s)
| #Put s' k -> (fun _ -> k () s')

let test_state n =
    (with state_handler handle loop_state n) 0

=== END SOURCE ===
*)

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
    let open Pervasives in
    function
    | 0 -> 1
    | 1 -> a
    | n ->
        let b = pow a (n / 2) in
        b * b * if n mod 2 = 0 then 1 else a
  in
  pow

let string_length _ = assert false

let to_string _ = assert false

let lift_unary f x = value (f x)

let lift_binary f x = value (fun y -> value (f x y))

;;
value "End of pervasives"

let _var_1 x = lift_binary ( = ) x

let _var_2 x = lift_binary ( < ) x

let _var_3 x = lift_binary ( - ) x

let _var_4 x = lift_binary ( + ) x

let rec _loop_pure_5 _n_6 =
  match run ((run (lift_binary ( = ) _n_6)) 0) with
  | true -> value ()
  | false -> _loop_pure_5 (run ((run (lift_binary ( - ) _n_6)) 1))

let _test_pure_11 _n_12 = _loop_pure_5 _n_12

type (_, _) effect += Effect_Fail : (unit, unit) effect

let rec _loop_latent_13 _n_14 =
  match run ((run (lift_binary ( = ) _n_14)) 0) with
  | true -> value ()
  | false -> (
      match run ((run (lift_binary ( < ) _n_14)) 0) with
      | true ->
          call Effect_Fail () (fun _result_3 ->
              match _result_3 with _ -> assert false)
      | false -> _loop_latent_13 (run ((run (lift_binary ( - ) _n_14)) 1)))

let _test_latent_22 _n_23 = _loop_latent_13 _n_23

type (_, _) effect += Effect_Incr : (unit, unit) effect

let rec _loop_incr_24 _n_25 =
  match run ((run (lift_binary ( = ) _n_25)) 0) with
  | true -> value ()
  | false ->
      call Effect_Incr () (fun _result_6 ->
          _loop_incr_24 (run ((run (lift_binary ( - ) _n_25)) 1)))

let _incr_handler_30 c =
  handler
    {
      value_clause = (fun _y_36 -> value (fun _x_37 -> value _x_37));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Incr ->
              fun (() : unit) (_k_31 : unit -> _ computation) ->
                value (fun _x_32 ->
                    _k_31 () >> fun _gen_bind_33 ->
                    _gen_bind_33 (run ((run (lift_binary ( + ) _x_32)) 1)))
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _test_incr_38 _n_39 =
  let rec _loop_incr_12 _n_25 =
    match run ((run (lift_binary ( = ) _n_25)) 0) with
    | true -> value (fun _x_17 -> value _x_17)
    | false ->
        value (fun _x_33 ->
            (run (_loop_incr_12 (run ((run (lift_binary ( - ) _n_25)) 1))))
              (run ((run (lift_binary ( + ) _x_33)) 1)))
  in
  (run (_loop_incr_12 _n_39)) 0

let rec _loop_incr'_41 _n_42 =
  match run ((run (lift_binary ( = ) _n_42)) 0) with
  | true -> value ()
  | false ->
      _loop_incr'_41 (run ((run (lift_binary ( - ) _n_42)) 1)) >> fun _ ->
      call Effect_Incr () (fun _result_36 -> value _result_36)

let _test_incr'_47 _n_48 =
  let rec _loop_incr'_42 _n_42 =
    match run ((run (lift_binary ( = ) _n_42)) 0) with
    | true -> value (fun _x_46 -> value _x_46)
    | false ->
        let rec _new_special_var_76 (_n_42, _k_val_75) =
          match run ((run (lift_binary ( = ) _n_42)) 0) with
          | true -> _k_val_75 ()
          | false ->
              _new_special_var_76
                ( run ((run (lift_binary ( - ) _n_42)) 1),
                  fun _ ->
                    value (fun _x_121 ->
                        (run (_k_val_75 ()))
                          (run ((run (lift_binary ( + ) _x_121)) 1))) )
        in
        _new_special_var_76
          ( run ((run (lift_binary ( - ) _n_42)) 1),
            fun _ ->
              value (fun _x_71 ->
                  value (run ((run (lift_binary ( + ) _x_71)) 1))) )
  in
  (run (_loop_incr'_42 _n_48)) 0

type (_, _) effect += Effect_Get : (unit, int) effect

type (_, _) effect += Effect_Put : (int, unit) effect

let rec _loop_state_50 _n_51 =
  match run ((run (lift_binary ( = ) _n_51)) 0) with
  | true -> value ()
  | false ->
      call Effect_Get () (fun _result_132 ->
          call Effect_Put
            (run ((run (lift_binary ( + ) _result_132)) 1))
            (fun _result_134 ->
              _loop_state_50 (run ((run (lift_binary ( - ) _n_51)) 1))))

let _state_handler_59 c =
  handler
    {
      value_clause = (fun _y_66 -> value (fun _x_67 -> value _x_67));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Get ->
              fun (() : unit) (_k_63 : int -> _ computation) ->
                value (fun _s_64 ->
                    _k_63 _s_64 >> fun _gen_bind_65 -> _gen_bind_65 _s_64)
          | Effect_Put ->
              fun (_s'_60 : int) (_k_61 : unit -> _ computation) ->
                value (fun _ ->
                    _k_61 () >> fun _gen_bind_62 -> _gen_bind_62 _s'_60)
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _test_state_68 _n_69 =
  let rec _loop_state_143 _n_51 =
    match run ((run (lift_binary ( = ) _n_51)) 0) with
    | true -> value (fun _x_155 -> value _x_155)
    | false ->
        value (fun _s_193 ->
            (run (_loop_state_143 (run ((run (lift_binary ( - ) _n_51)) 1))))
              (run ((run (lift_binary ( + ) _s_193)) 1)))
  in
  (run (_loop_state_143 _n_69)) 0
