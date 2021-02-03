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

let value (x : 'a) : 'a computation = Value x

let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
    'c computation =
  Call (eff, arg, cont)

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let effect eff arg = call eff arg value

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

let lift_unary f x = value (f x)

let lift_binary f x = value (fun y -> value (f x y))

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

let _op_0 (* = *) = ( = )

let _op_1 (* < *) = ( < )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let rec loop_pure n =
  let _b_6 =
    let _b_7 = _op_0 (* = *) n in
    _b_7 0
  in
  match _b_6 with
  | true -> ()
  | false ->
      let _b_8 =
        let _b_9 = _op_2 (* - *) n in
        _b_9 1
      in
      loop_pure _b_8

let test_pure (n : int) = loop_pure n

type (_, _) effect += Fail : (unit, empty) effect

let rec loop_latent n =
  Value
    (let _b_15 = _op_0 (* = *) n in
     _b_15 0)
  >> fun _b_14 ->
  match _b_14 with
  | true -> Value ()
  | false -> (
      Value
        (let _b_17 = _op_1 (* < *) n in
         _b_17 0)
      >> fun _b_16 ->
      match _b_16 with
      | true ->
          (effect Fail) () >> fun _b_18 ->
          Value (match _b_18 with _ -> assert false)
      | false ->
          Value
            (let _b_20 = _op_2 (* - *) n in
             _b_20 1)
          >> fun _b_19 -> loop_latent _b_19)

let test_latent (n : int) = loop_latent n

type (_, _) effect += Incr : (unit, unit) effect

let rec loop_incr n =
  Value
    (let _b_26 = _op_0 (* = *) n in
     _b_26 0)
  >> fun _b_25 ->
  match _b_25 with
  | true -> Value ()
  | false ->
      (effect Incr) () >> fun _ ->
      Value
        (let _b_28 = _op_2 (* - *) n in
         _b_28 1)
      >> fun _b_27 -> loop_incr _b_27

let test_incr (n : int) =
  let _b_41 =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x_37 : unit) -> Value (fun (x : int) -> x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
                match eff with
                | Incr ->
                    fun () l ->
                      Value
                        (fun (x : int) ->
                          let _b_34 =
                            ((coer_arrow coer_refl_ty force_unsafe) l) ()
                          in
                          let _b_35 =
                            let _b_36 = _op_3 (* + *) x in
                            _b_36 1
                          in
                          _b_34 _b_35)
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (loop_incr n))
  in
  _b_41 0

let rec loop_incr' n =
  Value
    (let _b_46 = _op_0 (* = *) n in
     _b_46 0)
  >> fun _b_45 ->
  match _b_45 with
  | true -> Value ()
  | false ->
      ( Value
          (let _b_48 = _op_2 (* - *) n in
           _b_48 1)
      >> fun _b_47 -> loop_incr' _b_47 )
      >> fun _ -> (effect Incr) ()

let test_incr' (n : int) =
  let _b_61 =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x_57 : unit) -> Value (fun (x : int) -> x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
                match eff with
                | Incr ->
                    fun () l ->
                      Value
                        (fun (x : int) ->
                          let _b_54 =
                            ((coer_arrow coer_refl_ty force_unsafe) l) ()
                          in
                          let _b_55 =
                            let _b_56 = _op_3 (* + *) x in
                            _b_56 1
                          in
                          _b_54 _b_55)
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (loop_incr' n))
  in
  _b_61 0

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec loop_state n =
  Value
    (let _b_66 = _op_0 (* = *) n in
     _b_66 0)
  >> fun _b_65 ->
  match _b_65 with
  | true -> Value ()
  | false ->
      ( ( ((effect Get) () >> fun _b_69 -> Value (_op_3 (* + *) _b_69))
        >> fun _b_68 -> Value (_b_68 1) )
      >> fun _b_67 -> (effect Put) _b_67 )
      >> fun _ ->
      Value
        (let _b_71 = _op_2 (* - *) n in
         _b_71 1)
      >> fun _b_70 -> loop_state _b_70

let test_state (n : int) =
  let _b_85 =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x_81 : unit) -> Value (fun (x : int) -> x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
                match eff with
                | Get ->
                    fun () l ->
                      Value
                        (fun (s : int) ->
                          let _b_77 =
                            ((coer_arrow coer_refl_ty force_unsafe) l) s
                          in
                          _b_77 s)
                | Put ->
                    fun s' l ->
                      Value
                        (fun (_ : int) ->
                          let _b_80 =
                            ((coer_arrow coer_refl_ty force_unsafe) l) ()
                          in
                          _b_80 s')
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (loop_state n))
  in
  _b_85 0
