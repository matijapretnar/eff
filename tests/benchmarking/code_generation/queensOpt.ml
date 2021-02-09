open OcamlHeader

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
  let _op_9 (* > *) (x_10 : int) (y_11 : int) = (_op_0 (* < *) y_11) x_10 in
  let _op_13 (* <> *) (x_14 : int) (y_15 : int) =
    match (_op_1 (* = *) y_15) x_14 with true -> false | false -> true
  in
  let abs_18 (x_19 : int) =
    match (_op_0 (* < *) x_19) 0 with
    | true -> _op_4 (* ~- *) x_19
    | false -> x_19
  in
  let no_attack_22 (q1_23 : inttuple) (q2_24 : inttuple) =
    match q1_23 with
    | IntTuple (x_25, y_26) -> (
        match q2_24 with
        | IntTuple (x'_27, y'_28) -> (
            match (_op_13 (* <> *) x_25) x'_27 with
            | true -> (
                match (_op_13 (* <> *) y_26) y'_28 with
                | true ->
                    (_op_13 (* <> *) (abs_18 ((_op_2 (* - *) x_25) x'_27)))
                      (abs_18 ((_op_2 (* - *) y_26) y'_28))
                | false -> false)
            | false -> false))
  in
  let rec not_attacked_40 x'_41 (qs_42 : inttuplist) =
    match qs_42 with
    | IntTupNil -> true
    | IntTupCons (x_43, xs_44) -> (
        match (no_attack_22 x'_41) x_43 with
        | true -> (not_attacked_40 x'_41) xs_44
        | false -> false)
  in
  let available_48 (number_of_queens_49 : int) (x_50 : int) (qs_51 : inttuplist)
      =
    let rec loop_52 possible_53 (y_54 : int) =
      match (_op_0 (* < *) y_54) 1 with
      | true -> possible_53
      | false -> (
          match (not_attacked_40 (IntTuple (x_50, y_54))) qs_51 with
          | true ->
              (loop_52 (IntCons (y_54, possible_53))) ((_op_2 (* - *) y_54) 1)
          | false -> (loop_52 possible_53) ((_op_2 (* - *) y_54) 1))
    in
    (loop_52 IntNil) number_of_queens_49
  in
  let rec choose_66 xs_67 =
    match xs_67 with
    | IntNil ->
        Call
          ( Fail,
            (),
            fun (x_0 : empty) -> Value (match x_0 with _ -> assert false) )
    | IntCons (x_69, xs'_70) ->
        Call
          ( Decide,
            (),
            fun (x_1 : bool) ->
              match x_1 with true -> Value x_69 | false -> choose_66 xs'_70 )
  in
  (let rec place_84 x_85 (qs_86 : inttuplist) =
     match (_op_9 (* > *) x_85) n_6 with
     | true -> Value qs_86
     | false ->
         choose_66 (((available_48 n_6) x_85) qs_86) >> fun y_89 ->
         (place_84 ((_op_3 (* + *) x_85) 1))
           (IntTupCons (IntTuple (x_85, y_89), qs_86))
   in
   force_unsafe
     ((handler
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
                   fun _ l_105 ->
                     Value
                       (fun (kf_74 : unit -> inttuplist computation) ->
                         (((coer_arrow coer_refl_ty force_unsafe) l_105) true)
                           (fun (_ : unit) ->
                             (((coer_arrow coer_refl_ty force_unsafe) l_105)
                                false)
                               kf_74))
               | Fail ->
                   fun _ l_106 ->
                     Value
                       (fun (kf_78 : unit -> inttuplist computation) ->
                         kf_78 ())
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        ((place_84 1) IntTupNil))) (fun (() : unit) ->
      Call (Fail, (), fun (y_108 : empty) -> Value (absurd_7 y_108)))
