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

let _op_0 (* = *) = ( = )

let _op_1 (* < *) = ( < )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let rec loop_pure n =
  let _b_6 =
    coer_refl_ty
      (let _b_7 =
         coer_refl_ty
           (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
               _op_0 (* = *))
              n)
       in
       coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_7) 0))
  in
  coer_refl_ty
    (match coer_refl_ty _b_6 with
    | true -> coer_refl_ty ()
    | false ->
        coer_refl_ty
          (let _b_8 =
             coer_refl_ty
               (let _b_9 =
                  coer_refl_ty
                    (((coer_arrow coer_refl_ty
                         (coer_arrow coer_refl_ty coer_refl_ty))
                        _op_2 (* - *))
                       n)
                in
                coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_9) 1))
           in
           coer_refl_ty
             (((coer_arrow coer_refl_ty coer_refl_ty)
                 ((coer_arrow coer_refl_ty coer_refl_ty) loop_pure))
                _b_8)))

let test_pure (n : int) = ((coer_arrow coer_refl_ty coer_refl_ty) loop_pure) n

type (_, _) effect += Fail : (unit, empty) effect

let rec loop_latent n =
  (coer_return coer_refl_ty)
    (let _b_15 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n)
     in
     coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_15) 0))
  >> fun _b_14 ->
  (coer_computation coer_refl_ty)
    (match coer_refl_ty _b_14 with
    | true -> (coer_return coer_refl_ty) ()
    | false ->
        (coer_computation coer_refl_ty)
          ( (coer_return coer_refl_ty)
              (let _b_17 =
                 coer_refl_ty
                   (((coer_arrow coer_refl_ty
                        (coer_arrow coer_refl_ty coer_refl_ty))
                       _op_1 (* < *))
                      n)
               in
               coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_17) 0))
          >> fun _b_16 ->
            (coer_computation coer_refl_ty)
              (match coer_refl_ty _b_16 with
              | true ->
                  (coer_computation coer_refl_ty)
                    ( (coer_computation coer_refl_ty)
                        (((coer_arrow coer_refl_ty
                             (coer_computation coer_refl_ty)) (fun (x : unit) ->
                              Call
                                ( Fail,
                                  x,
                                  fun (y : empty) ->
                                    (coer_return coer_refl_ty) y )))
                           ())
                    >> fun _b_18 ->
                      (coer_return coer_refl_ty)
                        (match _b_18 with _ -> assert false) )
              | false ->
                  (coer_computation coer_refl_ty)
                    ( (coer_return coer_refl_ty)
                        (let _b_20 =
                           coer_refl_ty
                             (((coer_arrow coer_refl_ty
                                  (coer_arrow coer_refl_ty coer_refl_ty))
                                 _op_2 (* - *))
                                n)
                         in
                         coer_refl_ty
                           (((coer_arrow coer_refl_ty coer_refl_ty) _b_20) 1))
                    >> fun _b_19 ->
                      (coer_computation coer_refl_ty)
                        (((coer_arrow coer_refl_ty
                             (coer_computation coer_refl_ty))
                            ((coer_arrow coer_refl_ty
                                (coer_computation coer_refl_ty))
                               loop_latent))
                           _b_19) )) ))

let test_latent (n : int) =
  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty)) loop_latent) n

type (_, _) effect += Incr : (unit, unit) effect

let rec loop_incr n =
  (coer_return coer_refl_ty)
    (let _b_28 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n)
     in
     coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_28) 0))
  >> fun _b_27 ->
  (coer_computation coer_refl_ty)
    (match coer_refl_ty _b_27 with
    | true -> (coer_return coer_refl_ty) ()
    | false ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  (fun (x : unit) ->
                    Call
                      (Incr, x, fun (y : unit) -> (coer_return coer_refl_ty) y)))
                 ())
          >> fun _ ->
            (coer_computation coer_refl_ty)
              ( (coer_return coer_refl_ty)
                  (let _b_30 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_2 (* - *))
                          n)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_30) 1))
              >> fun _b_29 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         loop_incr))
                     _b_29) ) ))

let test_incr (n : int) =
  let incr_handler =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_41 : unit) ->
               Value
                 ((coer_arrow coer_refl_ty coer_refl_ty)
                    (let y = _x_41 in
                     fun (x : int) -> x)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () l ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty) (fun (x : int) ->
                            let _b_38 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l)))
                                   ())
                            in
                            coer_refl_ty
                              (let _b_39 =
                                 coer_refl_ty
                                   (let _b_40 =
                                      coer_refl_ty
                                        (((coer_arrow coer_refl_ty
                                             (coer_arrow coer_refl_ty
                                                coer_refl_ty))
                                            _op_3 (* + *))
                                           x)
                                    in
                                    coer_refl_ty
                                      (((coer_arrow coer_refl_ty coer_refl_ty)
                                          _b_40)
                                         1))
                               in
                               coer_refl_ty
                                 (((coer_arrow coer_refl_ty coer_refl_ty) _b_38)
                                    _b_39))))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
  in
  let _b_45 =
    coer_refl_ty
      ((coer_unsafe (*unsafe*) coer_refl_ty)
         (((coer_handler
              (coer_computation coer_refl_ty)
              (coer_computation (coer_arrow coer_refl_ty coer_refl_ty)))
             incr_handler)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   loop_incr)
                  n))))
  in
  coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_45) 0)

let rec loop_incr' n =
  (coer_return coer_refl_ty)
    (let _b_50 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n)
     in
     coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_50) 0))
  >> fun _b_49 ->
  (coer_computation coer_refl_ty)
    (match coer_refl_ty _b_49 with
    | true -> (coer_return coer_refl_ty) ()
    | false ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              ( (coer_return coer_refl_ty)
                  (let _b_52 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_2 (* - *))
                          n)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_52) 1))
              >> fun _b_51 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         loop_incr'))
                     _b_51) )
          >> fun _ ->
            (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  (fun (x : unit) ->
                    Call
                      (Incr, x, fun (y : unit) -> (coer_return coer_refl_ty) y)))
                 ()) ))

let test_incr' (n : int) =
  let incr_handler =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_63 : unit) ->
               Value
                 ((coer_arrow coer_refl_ty coer_refl_ty)
                    (let y = _x_63 in
                     fun (x : int) -> x)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () l ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty) (fun (x : int) ->
                            let _b_60 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l)))
                                   ())
                            in
                            coer_refl_ty
                              (let _b_61 =
                                 coer_refl_ty
                                   (let _b_62 =
                                      coer_refl_ty
                                        (((coer_arrow coer_refl_ty
                                             (coer_arrow coer_refl_ty
                                                coer_refl_ty))
                                            _op_3 (* + *))
                                           x)
                                    in
                                    coer_refl_ty
                                      (((coer_arrow coer_refl_ty coer_refl_ty)
                                          _b_62)
                                         1))
                               in
                               coer_refl_ty
                                 (((coer_arrow coer_refl_ty coer_refl_ty) _b_60)
                                    _b_61))))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
  in
  let _b_67 =
    coer_refl_ty
      ((coer_unsafe (*unsafe*) coer_refl_ty)
         (((coer_handler
              (coer_computation coer_refl_ty)
              (coer_computation (coer_arrow coer_refl_ty coer_refl_ty)))
             incr_handler)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   loop_incr')
                  n))))
  in
  coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_67) 0)

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec loop_state n =
  (coer_return coer_refl_ty)
    (let _b_72 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n)
     in
     coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_72) 0))
  >> fun _b_71 ->
  (coer_computation coer_refl_ty)
    (match coer_refl_ty _b_71 with
    | true -> (coer_return coer_refl_ty) ()
    | false ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              ( (coer_computation coer_refl_ty)
                  ( (coer_computation coer_refl_ty)
                      ( (coer_computation coer_refl_ty)
                          (((coer_arrow coer_refl_ty
                               (coer_computation coer_refl_ty))
                              (fun (x : unit) ->
                                Call
                                  ( Get,
                                    x,
                                    fun (y : int) ->
                                      (coer_return coer_refl_ty) y )))
                             ())
                      >> fun _b_75 ->
                        (coer_return coer_refl_ty)
                          (((coer_arrow coer_refl_ty
                               (coer_arrow coer_refl_ty coer_refl_ty))
                              _op_3 (* + *))
                             _b_75) )
                  >> fun _b_74 ->
                    (coer_return coer_refl_ty)
                      (((coer_arrow coer_refl_ty coer_refl_ty) _b_74) 1) )
              >> fun _b_73 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      (fun (x : int) ->
                        Call
                          ( Put,
                            x,
                            fun (y : unit) -> (coer_return coer_refl_ty) y )))
                     _b_73) )
          >> fun _ ->
            (coer_computation coer_refl_ty)
              ( (coer_return coer_refl_ty)
                  (let _b_77 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_2 (* - *))
                          n)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_77) 1))
              >> fun _b_76 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         loop_state))
                     _b_76) ) ))

let test_state (n : int) =
  let state_handler =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_91 : unit) ->
               Value
                 ((coer_arrow coer_refl_ty coer_refl_ty)
                    (let y = _x_91 in
                     fun (x : int) -> x)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Get ->
                   fun () l ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty) (fun (s : int) ->
                            let _b_87 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l)))
                                   s)
                            in
                            coer_refl_ty
                              (((coer_arrow coer_refl_ty coer_refl_ty) _b_87) s)))
               | Put ->
                   fun s' l ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty) (fun (_ : int) ->
                            let _b_90 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l)))
                                   ())
                            in
                            coer_refl_ty
                              (((coer_arrow coer_refl_ty coer_refl_ty) _b_90)
                                 s')))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
  in
  let _b_95 =
    coer_refl_ty
      ((coer_unsafe (*unsafe*) coer_refl_ty)
         (((coer_handler
              (coer_computation coer_refl_ty)
              (coer_computation (coer_arrow coer_refl_ty coer_refl_ty)))
             state_handler)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   loop_state)
                  n))))
  in
  coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_95) 0)
