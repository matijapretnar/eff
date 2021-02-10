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

let _test_queens_5 (_n_6 : int) =
  let _absurd_7 (_void_8 : empty) = match _void_8 with _ -> assert false in
  let _op_9 (* > *) (_x_10 : int) (_y_11 : int) = (_op_0 (* < *) _y_11) _x_10 in
  let _op_13 (* <> *) (_x_14 : int) (_y_15 : int) =
    match (_op_1 (* = *) _y_15) _x_14 with true -> false | false -> true
  in
  let _abs_18 (_x_19 : int) =
    match (_op_0 (* < *) _x_19) 0 with
    | true -> _op_4 (* ~- *) _x_19
    | false -> _x_19
  in
  let _no_attack_22 (_q1_23 : inttuple) (_q2_24 : inttuple) =
    match _q1_23 with
    | IntTuple (_x_25, _y_26) -> (
        match _q2_24 with
        | IntTuple (_x'_27, _y'_28) -> (
            match (_op_13 (* <> *) _x_25) _x'_27 with
            | true -> (
                match (_op_13 (* <> *) _y_26) _y'_28 with
                | true ->
                    (_op_13 (* <> *) (_abs_18 ((_op_2 (* - *) _x_25) _x'_27)))
                      (_abs_18 ((_op_2 (* - *) _y_26) _y'_28))
                | false -> false)
            | false -> false))
  in
  let rec _not_attacked_40 _x_96 (_qs_42 : inttuplist) =
    match _qs_42 with
    | IntTupNil -> true
    | IntTupCons (_x_43, _xs_44) -> (
        match (_no_attack_22 _x_96) _x_43 with
        | true -> (_not_attacked_40 _x_96) _xs_44
        | false -> false)
  in
  let _available_48 (_number_of_queens_49 : int) (_x_50 : int)
      (_qs_51 : inttuplist) =
    let rec _loop_52 _x_97 =
      let _possible_53, _y_54 = _x_97 in
      match (_op_0 (* < *) _y_54) 1 with
      | true -> _possible_53
      | false -> (
          match (_not_attacked_40 (IntTuple (_x_50, _y_54))) _qs_51 with
          | true ->
              _loop_52 (IntCons (_y_54, _possible_53), (_op_2 (* - *) _y_54) 1)
          | false -> _loop_52 (_possible_53, (_op_2 (* - *) _y_54) 1))
    in
    _loop_52 (IntNil, _number_of_queens_49)
  in
  let rec _choose_63 _x_102 =
    match _x_102 with
    | IntNil ->
        Call
          ( Fail,
            (),
            fun (_x_0 : empty) -> Value (match _x_0 with _ -> assert false) )
    | IntCons (_x_66, _xs'_67) ->
        Call
          ( Decide,
            (),
            fun (_x_1 : bool) ->
              match _x_1 with
              | true -> Value _x_66
              | false -> _choose_63 _xs'_67 )
  in
  (let rec _place_135 _x_136 =
     let _x_138, _qs_137 = _x_136 in
     match (_op_9 (* > *) _x_138) _n_6 with
     | true -> Value _qs_137
     | false ->
         _choose_63 (((_available_48 _n_6) _x_138) _qs_137) >> fun _y_140 ->
         _place_135
           ( (_op_3 (* + *) _x_138) 1,
             IntTupCons (IntTuple (_x_138, _y_140), _qs_137) )
   in
   let rec _place_147 (_x_136, _k_149) =
     let _x_138, _qs_137 = _x_136 in
     match (_op_9 (* > *) _x_138) _n_6 with
     | true -> _k_149 _qs_137
     | false ->
         force_unsafe
           ((handler
               {
                 value_clause =
                   (fun (_y_140 : int) ->
                     Value
                       (_place_147
                          ( ( (_op_3 (* + *) _x_138) 1,
                              IntTupCons (IntTuple (_x_138, _y_140), _qs_137) ),
                            fun (_x_148 : inttuplist) -> _k_149 _x_148 )));
                 effect_clauses =
                   (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
                     match eff with
                     | Decide ->
                         fun _ _l_103 ->
                           Value
                             (fun (_kf_71 : unit -> inttuplist computation) ->
                               (((coer_arrow coer_refl_ty force_unsafe) _l_103)
                                  true) (fun (_ : unit) ->
                                   (((coer_arrow coer_refl_ty force_unsafe)
                                       _l_103)
                                      false)
                                     _kf_71))
                     | Fail ->
                         fun _ _l_104 ->
                           Value
                             (fun (_kf_75 : unit -> inttuplist computation) ->
                               _kf_75 ())
                     | eff' -> fun arg k -> Call (eff', arg, k));
               })
              (_choose_63 (((_available_48 _n_6) _x_138) _qs_137)))
   in
   _place_147
     ( (1, IntTupNil),
       fun (_x_76 : inttuplist) ->
         (coer_arrow coer_refl_ty (coer_return coer_refl_ty))
           (fun (_ : unit -> inttuplist computation) -> _x_76) ))
    (fun (() : unit) ->
      Call (Fail, (), fun (_y_134 : empty) -> Value (_absurd_7 _y_134)))
