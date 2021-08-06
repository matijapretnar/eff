open OcamlHeader

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) eff_internal_effect += DivByZero : (unit, int) eff_internal_effect

let _addCase_42 =
  Add
    ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
      Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )

let addCase = _addCase_42

let rec _createZeroCase_43 _x_52 =
  match _x_52 with
  | 0 -> Sub (_addCase_42, _addCase_42)
  | _n_54 ->
      Sub
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           ( _createZeroCase_43
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _n_54) 1),
             _createZeroCase_43
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _n_54) 1) ))

let createZeroCase = _createZeroCase_43

let rec _createCase_61 _x_67 =
  match _x_67 with
  | 1 ->
      Div
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           (Num 100, _createZeroCase_43 3))
  | _ ->
      Add
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           ( _addCase_42,
             _createCase_61
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_67) 1) ))

let createCase = _createCase_61

let _bigTest_68 (_num_69 : int) =
  let rec _interp_160 (_x_100, _k_162) =
    match _x_100 with
    | Num _b_111 -> _k_162 _b_111
    | Add (_l_113, _r_112) ->
        _interp_160
          ( _l_113,
            fun (_x_186 : int) ->
              _interp_160
                ( _r_112,
                  fun (_x_305 : int) ->
                    _k_162
                      (coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_186)
                         _x_305) ) )
    | Mul (_l_118, _r_117) ->
        _interp_160
          ( _l_118,
            fun (_x_203 : int) ->
              _interp_160
                ( _r_117,
                  fun (_x_345 : int) ->
                    _k_162
                      (coer_arrow coer_refl_ty coer_refl_ty (( * ) _x_203)
                         _x_345) ) )
    | Sub (_l_123, _r_122) ->
        _interp_160
          ( _l_123,
            fun (_x_220 : int) ->
              _interp_160
                ( _r_122,
                  fun (_x_385 : int) ->
                    _k_162
                      (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_220)
                         _x_385) ) )
    | Div (_l_128, _r_127) ->
        _interp_160
          ( _r_127,
            fun (_x_267 : int) ->
              _interp_160
                ( _l_128,
                  fun (_x_407 : int) ->
                    match _x_267 with
                    | 0 -> ~-1
                    | _ ->
                        _k_162
                          (coer_arrow coer_refl_ty coer_refl_ty (( / ) _x_407)
                             _x_267) ) )
  in
  _interp_160 (_createCase_61 _num_69, fun (_x_107 : int) -> _x_107)

let bigTest = _bigTest_68

let _bigTestLoop_410 (_num_411 : int) =
  let ____finalCase_435 = _createCase_61 _num_411 in
  let rec _looper_458 _x_459 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_s_461 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_459) 0 then _s_461
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_looper_458
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_459) 1))
            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_461)
               (let rec _interp_528 (_x_454, _k_530) =
                  match _x_454 with
                  | Num _b_479 -> _k_530 _b_479
                  | Add (_l_481, _r_480) ->
                      _interp_528
                        ( _l_481,
                          fun (_x_554 : int) ->
                            _interp_528
                              ( _r_480,
                                fun (_x_673 : int) ->
                                  _k_530
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (( + ) _x_554) _x_673) ) )
                  | Mul (_l_486, _r_485) ->
                      _interp_528
                        ( _l_486,
                          fun (_x_571 : int) ->
                            _interp_528
                              ( _r_485,
                                fun (_x_713 : int) ->
                                  _k_530
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (( * ) _x_571) _x_713) ) )
                  | Sub (_l_491, _r_490) ->
                      _interp_528
                        ( _l_491,
                          fun (_x_588 : int) ->
                            _interp_528
                              ( _r_490,
                                fun (_x_753 : int) ->
                                  _k_530
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (( - ) _x_588) _x_753) ) )
                  | Div (_l_496, _r_495) ->
                      _interp_528
                        ( _r_495,
                          fun (_x_635 : int) ->
                            _interp_528
                              ( _l_496,
                                fun (_x_775 : int) ->
                                  match _x_635 with
                                  | 0 -> ~-1
                                  | _ ->
                                      _k_530
                                        (coer_arrow coer_refl_ty coer_refl_ty
                                           (( / ) _x_775) _x_635) ) )
                in
                _interp_528 (____finalCase_435, fun (_x_475 : int) -> _x_475))))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_looper_458 100) 0

let bigTestLoop = _bigTestLoop_410

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_778 (_n_779 : int) =
  coer_arrow coer_refl_ty coer_refl_ty
    (coer_arrow coer_refl_ty coer_refl_ty
       (let rec _interp_907 (_x_821, _k_909) =
          match _x_821 with
          | Num _b_838 ->
              coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) ->
                  coer_arrow coer_refl_ty coer_refl_ty
                    (coer_arrow coer_refl_ty coer_refl_ty (_k_909 _b_838))
                    (coer_arrow coer_refl_ty coer_refl_ty (( * ) _b_838) _b_838))
          | Add (_l_843, _r_842) ->
              _interp_907
                ( _l_843,
                  fun (_x_950 : int) ->
                    _interp_907
                      ( _r_842,
                        fun (_x_1098 : int) ->
                          _k_909
                            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_950)
                               _x_1098) ) )
          | Mul (_l_848, _r_847) ->
              _interp_907
                ( _l_848,
                  fun (_x_967 : int) ->
                    _interp_907
                      ( _r_847,
                        fun (_x_1138 : int) ->
                          _k_909
                            (coer_arrow coer_refl_ty coer_refl_ty (( * ) _x_967)
                               _x_1138) ) )
          | Sub (_l_853, _r_852) ->
              _interp_907
                ( _l_853,
                  fun (_x_984 : int) ->
                    _interp_907
                      ( _r_852,
                        fun (_x_1178 : int) ->
                          _k_909
                            (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_984)
                               _x_1178) ) )
          | Div (_l_858, _r_857) ->
              _interp_907
                ( _r_857,
                  fun (_x_1035 : int) ->
                    _interp_907
                      ( _l_858,
                        fun (_x_1210 : int) ->
                          match _x_1035 with
                          | 0 ->
                              coer_arrow coer_refl_ty coer_refl_ty
                                (fun (_s_1211 : int) ->
                                  coer_arrow coer_refl_ty coer_refl_ty
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (_k_909 _s_1211))
                                    _s_1211)
                          | _ ->
                              _k_909
                                (coer_arrow coer_refl_ty coer_refl_ty
                                   (( / ) _x_1210) _x_1035) ) )
        in
        _interp_907
          ( _createCase_61 _n_779,
            fun (_x_832 : int) ->
              coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) -> _x_832) )))
    _n_779

let testState = _testState_778

let _testStateLoop_1215 (_n_1216 : int) =
  let _addCase_1217 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_1218 _x_1282 =
    match _x_1282 with
    | 0 -> Sub (_addCase_1217, _addCase_1217)
    | _n_1697 ->
        Sub
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             ( _createZeroCase_1218
                 (coer_arrow coer_refl_ty coer_refl_ty (( - ) _n_1697) 1),
               _createZeroCase_1218
                 (coer_arrow coer_refl_ty coer_refl_ty (( - ) _n_1697) 1) ))
  in
  let rec _createCase_1227 _x_1283 =
    match _x_1283 with
    | 1 ->
        Div
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             (Num 100, _createZeroCase_1218 3))
    | _ ->
        Add
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             ( _addCase_1217,
               _createCase_1227
                 (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_1283) 1) ))
  in
  let ____finalCase_1294 = _createCase_1227 _n_1216 in
  let rec _looper_1295 _x_1296 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_s_1298 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_1296) 0 then _s_1298
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_looper_1295
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_1296) 1))
            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_1298)
               (coer_arrow coer_refl_ty coer_refl_ty
                  (coer_arrow coer_refl_ty coer_refl_ty
                     (let rec _interp_1388 (_x_1288, _k_1390) =
                        match _x_1288 with
                        | Num _b_1319 ->
                            coer_arrow coer_refl_ty coer_refl_ty
                              (fun (_ : int) ->
                                coer_arrow coer_refl_ty coer_refl_ty
                                  (coer_arrow coer_refl_ty coer_refl_ty
                                     (_k_1390 _b_1319))
                                  (coer_arrow coer_refl_ty coer_refl_ty
                                     (( * ) _b_1319) _b_1319))
                        | Add (_l_1324, _r_1323) ->
                            _interp_1388
                              ( _l_1324,
                                fun (_x_1431 : int) ->
                                  _interp_1388
                                    ( _r_1323,
                                      fun (_x_1579 : int) ->
                                        _k_1390
                                          (coer_arrow coer_refl_ty coer_refl_ty
                                             (( + ) _x_1431) _x_1579) ) )
                        | Mul (_l_1329, _r_1328) ->
                            _interp_1388
                              ( _l_1329,
                                fun (_x_1448 : int) ->
                                  _interp_1388
                                    ( _r_1328,
                                      fun (_x_1619 : int) ->
                                        _k_1390
                                          (coer_arrow coer_refl_ty coer_refl_ty
                                             (( * ) _x_1448) _x_1619) ) )
                        | Sub (_l_1334, _r_1333) ->
                            _interp_1388
                              ( _l_1334,
                                fun (_x_1465 : int) ->
                                  _interp_1388
                                    ( _r_1333,
                                      fun (_x_1659 : int) ->
                                        _k_1390
                                          (coer_arrow coer_refl_ty coer_refl_ty
                                             (( - ) _x_1465) _x_1659) ) )
                        | Div (_l_1339, _r_1338) ->
                            _interp_1388
                              ( _r_1338,
                                fun (_x_1516 : int) ->
                                  _interp_1388
                                    ( _l_1339,
                                      fun (_x_1691 : int) ->
                                        match _x_1516 with
                                        | 0 ->
                                            coer_arrow coer_refl_ty coer_refl_ty
                                              (fun (_s_1692 : int) ->
                                                coer_arrow coer_refl_ty
                                                  coer_refl_ty
                                                  (coer_arrow coer_refl_ty
                                                     coer_refl_ty
                                                     (_k_1390 _s_1692))
                                                  _s_1692)
                                        | _ ->
                                            _k_1390
                                              (coer_arrow coer_refl_ty
                                                 coer_refl_ty (( / ) _x_1691)
                                                 _x_1516) ) )
                      in
                      _interp_1388
                        ( ____finalCase_1294,
                          fun (_x_1313 : int) ->
                            coer_arrow coer_refl_ty coer_refl_ty
                              (fun (_ : int) -> _x_1313) )))
                  _n_1216)))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_looper_1295 100) 0

let testStateLoop = _testStateLoop_1215
