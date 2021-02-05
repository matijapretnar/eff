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

let test_queens_5 (n_6 : int) =
  let absurd_7 (void_8 : empty) = match void_8 with _ -> assert false in
  let _op_9 (* > *) (x_10 : int) (y_11 : int) =
    let _b_12 =
      coer_refl_ty
        (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
            _op_0 (* < *))
           y_11)
    in
    coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_12) x_10)
  in
  let _op_13 (* <> *) (x_14 : int) (y_15 : int) =
    let _b_16 =
      coer_refl_ty
        (let _b_17 =
           coer_refl_ty
             (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
                 _op_1 (* = *))
                y_15)
         in
         coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_17) x_14))
    in
    coer_refl_ty
      (match coer_refl_ty _b_16 with
      | true -> coer_refl_ty false
      | false -> coer_refl_ty true)
  in
  let abs_18 (x_19 : int) =
    let _b_20 =
      coer_refl_ty
        (let _b_21 =
           coer_refl_ty
             (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
                 _op_0 (* < *))
                x_19)
         in
         coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_21) 0))
    in
    coer_refl_ty
      (match coer_refl_ty _b_20 with
      | true ->
          coer_refl_ty
            (((coer_arrow coer_refl_ty coer_refl_ty) _op_4 (* ~- *)) x_19)
      | false -> coer_refl_ty x_19)
  in
  let no_attack_22 (q1_23 : inttuple) (q2_24 : inttuple) =
    match coer_refl_ty q1_23 with
    | IntTuple (x_25, y_26) ->
        coer_refl_ty
          (match coer_refl_ty q2_24 with
          | IntTuple (x'_27, y'_28) ->
              coer_refl_ty
                (let _b_29 =
                   coer_refl_ty
                     (let _b_30 =
                        coer_refl_ty
                          (((coer_arrow coer_refl_ty
                               (coer_arrow coer_refl_ty coer_refl_ty))
                              _op_13 (* <> *))
                             x_25)
                      in
                      coer_refl_ty
                        (((coer_arrow coer_refl_ty coer_refl_ty) _b_30) x'_27))
                 in
                 coer_refl_ty
                   (match coer_refl_ty _b_29 with
                   | true ->
                       coer_refl_ty
                         (let _b_31 =
                            coer_refl_ty
                              (let _b_32 =
                                 coer_refl_ty
                                   (((coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty))
                                       _op_13 (* <> *))
                                      y_26)
                               in
                               coer_refl_ty
                                 (((coer_arrow coer_refl_ty coer_refl_ty) _b_32)
                                    y'_28))
                          in
                          coer_refl_ty
                            (match coer_refl_ty _b_31 with
                            | true ->
                                coer_refl_ty
                                  (let _b_33 =
                                     coer_refl_ty
                                       (let _b_34 =
                                          coer_refl_ty
                                            (let _b_35 =
                                               coer_refl_ty
                                                 (let _b_36 =
                                                    coer_refl_ty
                                                      (((coer_arrow coer_refl_ty
                                                           (coer_arrow
                                                              coer_refl_ty
                                                              coer_refl_ty))
                                                          _op_2 (* - *))
                                                         x_25)
                                                  in
                                                  coer_refl_ty
                                                    (((coer_arrow coer_refl_ty
                                                         coer_refl_ty)
                                                        _b_36)
                                                       x'_27))
                                             in
                                             coer_refl_ty
                                               (((coer_arrow coer_refl_ty
                                                    coer_refl_ty)
                                                   abs_18)
                                                  _b_35))
                                        in
                                        coer_refl_ty
                                          (((coer_arrow coer_refl_ty
                                               (coer_arrow coer_refl_ty
                                                  coer_refl_ty))
                                              _op_13 (* <> *))
                                             _b_34))
                                   in
                                   coer_refl_ty
                                     (let _b_37 =
                                        coer_refl_ty
                                          (let _b_38 =
                                             coer_refl_ty
                                               (let _b_39 =
                                                  coer_refl_ty
                                                    (((coer_arrow coer_refl_ty
                                                         (coer_arrow
                                                            coer_refl_ty
                                                            coer_refl_ty))
                                                        _op_2 (* - *))
                                                       y_26)
                                                in
                                                coer_refl_ty
                                                  (((coer_arrow coer_refl_ty
                                                       coer_refl_ty)
                                                      _b_39)
                                                     y'_28))
                                           in
                                           coer_refl_ty
                                             (((coer_arrow coer_refl_ty
                                                  coer_refl_ty)
                                                 abs_18)
                                                _b_38))
                                      in
                                      coer_refl_ty
                                        (((coer_arrow coer_refl_ty coer_refl_ty)
                                            _b_33)
                                           _b_37)))
                            | false -> coer_refl_ty false))
                   | false -> coer_refl_ty false)))
  in
  let rec not_attacked_40 x'_41 (qs_42 : inttuplist) =
    match coer_refl_ty qs_42 with
    | IntTupNil -> coer_refl_ty true
    | IntTupCons (x_43, xs_44) ->
        coer_refl_ty
          (let _b_45 =
             coer_refl_ty
               (let _b_46 =
                  coer_refl_ty
                    (((coer_arrow coer_refl_ty
                         (coer_arrow coer_refl_ty coer_refl_ty))
                        no_attack_22)
                       x'_41)
                in
                coer_refl_ty
                  (((coer_arrow coer_refl_ty coer_refl_ty) _b_46) x_43))
           in
           coer_refl_ty
             (match coer_refl_ty _b_45 with
             | true ->
                 coer_refl_ty
                   (let _b_47 =
                      coer_refl_ty
                        (((coer_arrow coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty))
                            ((coer_arrow coer_refl_ty
                                (coer_arrow coer_refl_ty coer_refl_ty))
                               not_attacked_40))
                           x'_41)
                    in
                    coer_refl_ty
                      (((coer_arrow coer_refl_ty coer_refl_ty) _b_47) xs_44))
             | false -> coer_refl_ty false))
  in
  let available_48 (number_of_queens_49 : int) (x_50 : int) (qs_51 : inttuplist)
      =
    let rec loop_52 possible_53 (y_54 : int) =
      let _b_55 =
        coer_refl_ty
          (let _b_56 =
             coer_refl_ty
               (((coer_arrow coer_refl_ty
                    (coer_arrow coer_refl_ty coer_refl_ty))
                   _op_0 (* < *))
                  y_54)
           in
           coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) _b_56) 1))
      in
      coer_refl_ty
        (match coer_refl_ty _b_55 with
        | true -> coer_refl_ty possible_53
        | false ->
            coer_refl_ty
              (let _b_57 =
                 coer_refl_ty
                   (let _b_58 =
                      coer_refl_ty
                        (((coer_arrow coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty))
                            not_attacked_40)
                           (IntTuple
                              (((* tuple_coer *) coer_tuple_2
                                  (coer_refl_ty, coer_refl_ty))
                                 (x_50, y_54))))
                    in
                    coer_refl_ty
                      (((coer_arrow coer_refl_ty coer_refl_ty) _b_58) qs_51))
               in
               coer_refl_ty
                 (match coer_refl_ty _b_57 with
                 | true ->
                     coer_refl_ty
                       (let _b_59 =
                          coer_refl_ty
                            (((coer_arrow coer_refl_ty
                                 (coer_arrow coer_refl_ty coer_refl_ty))
                                ((coer_arrow coer_refl_ty
                                    (coer_arrow coer_refl_ty coer_refl_ty))
                                   loop_52))
                               (IntCons (coer_refl_ty (y_54, possible_53))))
                        in
                        coer_refl_ty
                          (let _b_60 =
                             coer_refl_ty
                               (let _b_61 =
                                  coer_refl_ty
                                    (((coer_arrow coer_refl_ty
                                         (coer_arrow coer_refl_ty coer_refl_ty))
                                        _op_2 (* - *))
                                       y_54)
                                in
                                coer_refl_ty
                                  (((coer_arrow coer_refl_ty coer_refl_ty)
                                      _b_61)
                                     1))
                           in
                           coer_refl_ty
                             (((coer_arrow coer_refl_ty coer_refl_ty) _b_59)
                                _b_60)))
                 | false ->
                     coer_refl_ty
                       (let _b_62 =
                          coer_refl_ty
                            (((coer_arrow coer_refl_ty
                                 (coer_arrow coer_refl_ty coer_refl_ty))
                                ((coer_arrow coer_refl_ty
                                    (coer_arrow coer_refl_ty coer_refl_ty))
                                   loop_52))
                               possible_53)
                        in
                        coer_refl_ty
                          (let _b_63 =
                             coer_refl_ty
                               (let _b_64 =
                                  coer_refl_ty
                                    (((coer_arrow coer_refl_ty
                                         (coer_arrow coer_refl_ty coer_refl_ty))
                                        _op_2 (* - *))
                                       y_54)
                                in
                                coer_refl_ty
                                  (((coer_arrow coer_refl_ty coer_refl_ty)
                                      _b_64)
                                     1))
                           in
                           coer_refl_ty
                             (((coer_arrow coer_refl_ty coer_refl_ty) _b_62)
                                _b_63))))))
    in
    let _b_65 =
      coer_refl_ty
        (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
            loop_52)
           IntNil)
    in
    coer_refl_ty
      (((coer_arrow coer_refl_ty coer_refl_ty) _b_65) number_of_queens_49)
  in
  let rec choose_66 xs_67 =
    match coer_refl_ty xs_67 with
    | IntNil ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  (fun (x_103 : unit) ->
                    Call
                      ( Fail,
                        x_103,
                        fun (y_104 : empty) -> (coer_return coer_refl_ty) y_104
                      )))
                 ())
          >> fun _b_68 ->
            (coer_return coer_refl_ty) (match _b_68 with _ -> assert false) )
    | IntCons (x_69, xs'_70) ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  (fun (x_101 : unit) ->
                    Call
                      ( Decide,
                        x_101,
                        fun (y_102 : bool) -> (coer_return coer_refl_ty) y_102
                      )))
                 ())
          >> fun _b_71 ->
            (coer_computation coer_refl_ty)
              (match coer_refl_ty _b_71 with
              | true -> (coer_return coer_refl_ty) x_69
              | false ->
                  (coer_computation coer_refl_ty)
                    (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                        ((coer_arrow coer_refl_ty
                            (coer_computation coer_refl_ty))
                           choose_66))
                       xs'_70)) )
  in
  let backtrack_72 =
    (coer_handler
       (coer_computation coer_refl_ty)
       (coer_computation coer_refl_ty))
      (handler
         {
           value_clause =
             (fun (_x_79 : inttuplist) ->
               Value
                 ((coer_arrow
                     (coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                     (coer_return coer_refl_ty))
                    (let y_80 = _x_79 in
                     fun (_ : unit -> inttuplist computation) -> y_80)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Decide ->
                   fun _ l_105 ->
                     Value
                       ((coer_arrow
                           (coer_arrow coer_refl_ty
                              (coer_computation coer_refl_ty))
                           (coer_computation coer_refl_ty))
                          (fun (kf_74 : unit -> inttuplist computation) ->
                            (coer_return coer_refl_ty)
                              (((coer_arrow coer_refl_ty
                                   (coer_arrow
                                      (coer_arrow coer_refl_ty
                                         (coer_computation coer_refl_ty))
                                      (coer_computation coer_refl_ty)))
                                  ((coer_arrow coer_refl_ty
                                      (coer_arrow
                                         (coer_arrow coer_refl_ty
                                            (coer_computation coer_refl_ty))
                                         (coer_computation coer_refl_ty)))
                                     ((coer_arrow coer_refl_ty
                                         (coer_unsafe (*unsafe*) coer_refl_ty))
                                        l_105)))
                                 true)
                            >> fun _b_75 ->
                            (coer_computation coer_refl_ty)
                              (((coer_arrow
                                   (coer_arrow coer_refl_ty
                                      (coer_computation coer_refl_ty))
                                   (coer_computation coer_refl_ty))
                                  _b_75) (fun (_ : unit) ->
                                   (coer_return coer_refl_ty)
                                     (((coer_arrow coer_refl_ty
                                          (coer_arrow
                                             (coer_arrow coer_refl_ty
                                                (coer_computation coer_refl_ty))
                                             (coer_computation coer_refl_ty)))
                                         ((coer_arrow coer_refl_ty
                                             (coer_arrow
                                                (coer_arrow coer_refl_ty
                                                   (coer_computation
                                                      coer_refl_ty))
                                                (coer_computation coer_refl_ty)))
                                            ((coer_arrow coer_refl_ty
                                                (coer_unsafe
                                                   (*unsafe*) coer_refl_ty))
                                               l_105)))
                                        false)
                                   >> fun _b_76 ->
                                   (coer_computation coer_refl_ty)
                                     (((coer_arrow
                                          (coer_arrow coer_refl_ty
                                             (coer_computation coer_refl_ty))
                                          (coer_computation coer_refl_ty))
                                         _b_76)
                                        kf_74)))))
               | Fail ->
                   fun _ l_106 ->
                     Value
                       ((coer_arrow
                           (coer_arrow coer_refl_ty
                              (coer_computation coer_refl_ty))
                           (coer_computation coer_refl_ty))
                          (fun (kf_78 : unit -> inttuplist computation) ->
                            ((coer_arrow coer_refl_ty
                                (coer_computation coer_refl_ty))
                               kf_78)
                              ()))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
  in
  let queens_82 (number_of_queens_83 : int) =
    let rec place_84 x_85 (qs_86 : inttuplist) =
      (coer_return coer_refl_ty)
        (let _b_88 =
           coer_refl_ty
             (((coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty))
                 _op_9 (* > *))
                x_85)
         in
         coer_refl_ty
           (((coer_arrow coer_refl_ty coer_refl_ty) _b_88) number_of_queens_83))
      >> fun _b_87 ->
      (coer_computation coer_refl_ty)
        (match coer_refl_ty _b_87 with
        | true -> (coer_return coer_refl_ty) qs_86
        | false ->
            (coer_computation coer_refl_ty)
              ( (coer_computation coer_refl_ty)
                  ( (coer_return coer_refl_ty)
                      (let _b_91 =
                         coer_refl_ty
                           (let _b_92 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty
                                        (coer_arrow coer_refl_ty coer_refl_ty)))
                                    available_48)
                                   number_of_queens_83)
                            in
                            coer_refl_ty
                              (((coer_arrow coer_refl_ty
                                   (coer_arrow coer_refl_ty coer_refl_ty))
                                  _b_92)
                                 x_85))
                       in
                       coer_refl_ty
                         (((coer_arrow coer_refl_ty coer_refl_ty) _b_91) qs_86))
                  >> fun _b_90 ->
                    (coer_computation coer_refl_ty)
                      (((coer_arrow coer_refl_ty
                           (coer_computation coer_refl_ty))
                          choose_66)
                         _b_90) )
              >> fun y_89 ->
                (coer_computation coer_refl_ty)
                  ( (coer_return coer_refl_ty)
                      (let _b_94 =
                         coer_refl_ty
                           (let _b_95 =
                              coer_refl_ty
                                (((coer_arrow coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty))
                                    _op_3 (* + *))
                                   x_85)
                            in
                            coer_refl_ty
                              (((coer_arrow coer_refl_ty coer_refl_ty) _b_95) 1))
                       in
                       coer_refl_ty
                         (((coer_arrow coer_refl_ty
                              (coer_arrow coer_refl_ty
                                 (coer_computation coer_refl_ty)))
                             ((coer_arrow coer_refl_ty
                                 (coer_arrow coer_refl_ty
                                    (coer_computation coer_refl_ty)))
                                place_84))
                            _b_94))
                  >> fun _b_93 ->
                    (coer_computation coer_refl_ty)
                      (((coer_arrow coer_refl_ty
                           (coer_computation coer_refl_ty))
                          _b_93)
                         (IntTupCons
                            (((* tuple_coer *) coer_tuple_2
                                (coer_refl_ty, coer_refl_ty))
                               ( IntTuple
                                   (((* tuple_coer *) coer_tuple_2
                                       (coer_refl_ty, coer_refl_ty))
                                      (x_85, y_89)),
                                 qs_86 )))) ) ))
    in
    (coer_return coer_refl_ty)
      (((coer_arrow coer_refl_ty
           (coer_arrow coer_refl_ty (coer_computation coer_refl_ty)))
          place_84)
         1)
    >> fun _b_96 ->
    (coer_computation coer_refl_ty)
      (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty)) _b_96)
         IntTupNil)
  in
  let queens_one_cps_97 (number_of_queens_98 : int) =
    (coer_return coer_refl_ty)
      ((coer_unsafe (*unsafe*) coer_refl_ty)
         (((coer_handler
              (coer_computation coer_refl_ty)
              (coer_computation
                 (coer_arrow
                    (coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                    (coer_computation coer_refl_ty))))
             backtrack_72)
            ((coer_computation coer_refl_ty)
               (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                   queens_82)
                  number_of_queens_98))))
    >> fun _b_99 ->
    (coer_computation coer_refl_ty)
      (((coer_arrow
           (coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
           (coer_computation coer_refl_ty))
          _b_99) (fun (() : unit) ->
           (coer_computation coer_refl_ty)
             (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                 (fun (x_107 : unit) ->
                   Call
                     ( Fail,
                       x_107,
                       fun (y_108 : empty) -> (coer_return coer_refl_ty) y_108
                     )))
                ())
           >> fun _b_100 ->
           (coer_return coer_refl_ty)
             (((coer_arrow coer_refl_ty coer_refl_ty) absurd_7) _b_100)))
  in
  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty)) queens_one_cps_97)
    n_6
