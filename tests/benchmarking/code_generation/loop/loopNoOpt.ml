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

(* Manual tuple coercions, one way to do this a bit better is to use GADT and map over them *)

let coer_tuple_2 (c1, c2) (a1, a2) = (c1 a1, c2 a2)

let coer_tuple_3 (c1, c2, c3) (a1, a2, a3) = (c1 a1, c2 a2, c3 a3)

let coer_tuple_4 (c1, c2, c3, c4) (a1, a2, a3, a4) = (c1 a1, c2 a2, c3 a3, c4 a4)

let coer_tuple_5 (c1, c2, c3, c4, c5) (a1, a2, a3, a4, a5) =
  (c1 a1, c2 a2, c3 a3, c4 a4, c5 a5)

(* This should be enough *)

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

let rec loop_pure_4 n_5 =
  let _b_6 =
    coer_refl_ty
      (let _b_7 =
         coer_refl_ty
           (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
               _op_0 (* = *))
              n_5)
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
                       n_5)
                in
                coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_9) 1))
           in
           coer_refl_ty
             (((coer_arrow coer_refl_ty coer_refl_ty)
                 ((coer_arrow coer_refl_ty coer_refl_ty) loop_pure_4))
                _b_8)))

let test_pure_10 (n_11 : int) =
  ((coer_arrow coer_refl_ty coer_refl_ty) loop_pure_4) n_11

type (_, _) effect += Fail : (unit, empty) effect

let rec loop_latent_12 n_13 =
  (coer_return coer_refl_ty)
    (let _b_15 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n_13)
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
                      n_13)
               in
               coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_17) 0))
          >> fun _b_16 ->
            (coer_computation coer_refl_ty)
              (match coer_refl_ty _b_16 with
              | true ->
                  (coer_computation coer_refl_ty)
                    ( (coer_computation coer_refl_ty)
                        (((coer_arrow coer_refl_ty
                             (coer_computation coer_refl_ty))
                            (fun (x_21 : unit) ->
                              Call
                                ( Fail,
                                  x_21,
                                  fun (y_22 : empty) ->
                                    (coer_return coer_refl_ty) y_22 )))
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
                                n_13)
                         in
                         coer_refl_ty
                           (((coer_arrow coer_refl_ty coer_refl_ty) _b_20) 1))
                    >> fun _b_19 ->
                      (coer_computation coer_refl_ty)
                        (((coer_arrow coer_refl_ty
                             (coer_computation coer_refl_ty))
                            ((coer_arrow coer_refl_ty
                                (coer_computation coer_refl_ty))
                               loop_latent_12))
                           _b_19) )) ))

let test_latent_23 (n_24 : int) =
  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty)) loop_latent_12)
    n_24

type (_, _) effect += Incr : (unit, unit) effect

let rec loop_incr_25 n_26 =
  (coer_return coer_refl_ty)
    (let _b_28 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n_26)
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
                  (fun (x_31 : unit) ->
                    Call
                      ( Incr,
                        x_31,
                        fun (y_32 : unit) -> (coer_return coer_refl_ty) y_32 )))
                 ())
          >> fun _ ->
            (coer_computation coer_refl_ty)
              ( (coer_return coer_refl_ty)
                  (let _b_30 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_2 (* - *))
                          n_26)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_30) 1))
              >> fun _b_29 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         loop_incr_25))
                     _b_29) ) ))

let test_incr_33 (n_34 : int) =
  let incr_handler_35 =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_41 : unit) ->
               Value
                 ((coer_arrow coer_refl_ty coer_refl_ty)
                    (let y_42 = _x_41 in
                     fun (x_43 : int) -> x_43)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () l_46 ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty)
                          (fun (x_37 : int) ->
                            let _b_38 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l_46)))
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
                                           x_37)
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
             incr_handler_35)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   loop_incr_25)
                  n_34))))
  in
  coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_45) 0)

let rec loop_incr'_47 n_48 =
  (coer_return coer_refl_ty)
    (let _b_50 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n_48)
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
                          n_48)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_52) 1))
              >> fun _b_51 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         loop_incr'_47))
                     _b_51) )
          >> fun _ ->
            (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  (fun (x_53 : unit) ->
                    Call
                      ( Incr,
                        x_53,
                        fun (y_54 : unit) -> (coer_return coer_refl_ty) y_54 )))
                 ()) ))

let test_incr'_55 (n_56 : int) =
  let incr_handler_57 =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_63 : unit) ->
               Value
                 ((coer_arrow coer_refl_ty coer_refl_ty)
                    (let y_64 = _x_63 in
                     fun (x_65 : int) -> x_65)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () l_68 ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty)
                          (fun (x_59 : int) ->
                            let _b_60 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l_68)))
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
                                           x_59)
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
             incr_handler_57)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   loop_incr'_47)
                  n_56))))
  in
  coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_67) 0)

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec loop_state_69 n_70 =
  (coer_return coer_refl_ty)
    (let _b_72 =
       coer_refl_ty
         (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
             _op_0 (* = *))
            n_70)
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
                              (fun (x_78 : unit) ->
                                Call
                                  ( Get,
                                    x_78,
                                    fun (y_79 : int) ->
                                      (coer_return coer_refl_ty) y_79 )))
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
                      (fun (x_80 : int) ->
                        Call
                          ( Put,
                            x_80,
                            fun (y_81 : unit) -> (coer_return coer_refl_ty) y_81
                          )))
                     _b_73) )
          >> fun _ ->
            (coer_computation coer_refl_ty)
              ( (coer_return coer_refl_ty)
                  (let _b_77 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_2 (* - *))
                          n_70)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_77) 1))
              >> fun _b_76 ->
                (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         loop_state_69))
                     _b_76) ) ))

let test_state_82 (n_83 : int) =
  let state_handler_84 =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_91 : unit) ->
               Value
                 ((coer_arrow coer_refl_ty coer_refl_ty)
                    (let y_92 = _x_91 in
                     fun (x_93 : int) -> x_93)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Get ->
                   fun () l_96 ->
                     Value
                       ((coer_arrow coer_refl_ty coer_refl_ty)
                          (fun (s_86 : int) ->
                            let _b_87 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    ((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       ((coer_arrow coer_refl_ty
                                           (coer_unsafe (*unsafe*) coer_refl_ty))
                                          l_96)))
                                   s_86)
                            in
                            coer_refl_ty
                              (((coer_arrow coer_refl_ty coer_refl_ty) _b_87)
                                 s_86)))
               | Put ->
                   fun s'_88 l_97 ->
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
                                          l_97)))
                                   ())
                            in
                            coer_refl_ty
                              (((coer_arrow coer_refl_ty coer_refl_ty) _b_90)
                                 s'_88)))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
  in
  let _b_95 =
    coer_refl_ty
      ((coer_unsafe (*unsafe*) coer_refl_ty)
         (((coer_handler
              (coer_computation coer_refl_ty)
              (coer_computation (coer_arrow coer_refl_ty coer_refl_ty)))
             state_handler_84)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   loop_state_69)
                  n_83))))
  in
  coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_95) 0)
