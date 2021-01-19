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
"End of pervasives"

let _var_1 = ( = )

let _var_2 = ( < )

let _var_3 = ( - )

let _var_4 = ( + )

let rec _loop_pure_5 _n_6 =
  let _gen_bind_7 =
    let _gen_bind_8 = _var_1 _n_6 in
    _gen_bind_8 0
  in
  if _gen_bind_7 then ()
  else
    let _gen_bind_9 =
      let _gen_bind_10 = _var_3 _n_6 in
      _gen_bind_10 1
    in
    _loop_pure_5 _gen_bind_9

let _test_pure_11 _n_12 = _loop_pure_5 _n_12

type (_, _) effect += Effect_Fail : (unit, unit) effect

let rec _loop_latent_13 _n_14 =
  let _gen_bind_15 =
    let _gen_bind_16 = _var_1 _n_14 in
    _gen_bind_16 0
  in
  if _gen_bind_15 then value ()
  else
    let _gen_bind_17 =
      let _gen_bind_18 = _var_2 _n_14 in
      _gen_bind_18 0
    in
    if _gen_bind_17 then
      (effect Effect_Fail) () >> fun _gen_bind_19 ->
      value (match _gen_bind_19 with _ -> assert false)
    else
      let _gen_bind_20 =
        let _gen_bind_21 = _var_3 _n_14 in
        _gen_bind_21 1
      in
      _loop_latent_13 _gen_bind_20

let _test_latent_22 _n_23 = _loop_latent_13 _n_23

type (_, _) effect += Effect_Incr : (unit, unit) effect

let rec _loop_incr_24 _n_25 =
  let _gen_bind_26 =
    let _gen_bind_27 = _var_1 _n_25 in
    _gen_bind_27 0
  in
  if _gen_bind_26 then value ()
  else
    (effect Effect_Incr) () >> fun _ ->
    let _gen_bind_28 =
      let _gen_bind_29 = _var_3 _n_25 in
      _gen_bind_29 1
    in
    _loop_incr_24 _gen_bind_28

let _incr_handler_30 comp =
  handler
    {
      value_clause =
        (fun _y_36 ->
          value (fun _lift_fun_1 -> value ((fun _x_37 -> _x_37) _lift_fun_1)));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) : (a -> (b -> _) -> _) ->
          match x with
          | Effect_Incr ->
              fun (() : unit) (_k_31 : unit -> _) ->
                value (fun _x_32 ->
                    _k_31 () >> fun _gen_bind_33 ->
                    let _gen_bind_34 =
                      let _gen_bind_35 = _var_4 _x_32 in
                      _gen_bind_35 1
                    in
                    _gen_bind_33 _gen_bind_34)
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    comp

let _test_incr_38 _n_39 =
  _incr_handler_30 (_loop_incr_24 _n_39) >> fun _gen_bind_40 -> _gen_bind_40 0

let rec _loop_incr'_41 _n_42 =
  let _gen_bind_43 =
    let _gen_bind_44 = _var_1 _n_42 in
    _gen_bind_44 0
  in
  if _gen_bind_43 then value ()
  else
    (let _gen_bind_45 =
       let _gen_bind_46 = _var_3 _n_42 in
       _gen_bind_46 1
     in
     _loop_incr'_41 _gen_bind_45)
    >> fun _ -> (effect Effect_Incr) ()

let _test_incr'_47 _n_48 =
  _incr_handler_30 (_loop_incr'_41 _n_48) >> fun _gen_bind_49 -> _gen_bind_49 0

type (_, _) effect += Effect_Get : (unit, int) effect

type (_, _) effect += Effect_Put : (int, unit) effect

let rec _loop_state_50 _n_51 =
  let _gen_bind_52 =
    let _gen_bind_53 = _var_1 _n_51 in
    _gen_bind_53 0
  in
  if _gen_bind_52 then value ()
  else
    ( ( ( (effect Effect_Get) () >> fun _gen_bind_56 ->
          value (_var_4 _gen_bind_56) )
      >> fun _gen_bind_55 -> value (_gen_bind_55 1) )
    >> fun _gen_bind_54 -> (effect Effect_Put) _gen_bind_54 )
    >> fun _ ->
    let _gen_bind_57 =
      let _gen_bind_58 = _var_3 _n_51 in
      _gen_bind_58 1
    in
    _loop_state_50 _gen_bind_57

let _state_handler_59 comp =
  handler
    {
      value_clause =
        (fun _y_66 ->
          value (fun _lift_fun_2 -> value ((fun _x_67 -> _x_67) _lift_fun_2)));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) : (a -> (b -> _) -> _) ->
          match x with
          | Effect_Get ->
              fun (() : unit) (_k_63 : int -> _) ->
                value (fun _s_64 ->
                    _k_63 _s_64 >> fun _gen_bind_65 -> _gen_bind_65 _s_64)
          | Effect_Put ->
              fun (_s'_60 : int) (_k_61 : unit -> _) ->
                value (fun _ ->
                    _k_61 () >> fun _gen_bind_62 -> _gen_bind_62 _s'_60)
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    comp

let _test_state_68 _n_69 =
  _state_handler_59 (_loop_state_50 _n_69) >> fun _gen_bind_70 -> _gen_bind_70 0
