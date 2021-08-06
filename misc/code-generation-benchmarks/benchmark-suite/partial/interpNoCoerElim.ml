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
           (_createZeroCase_43 (_n_54 - 1), _createZeroCase_43 (_n_54 - 1)))

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
           (_addCase_42, _createCase_61 (_x_67 - 1)))

let createCase = _createCase_61

let _bigTest_68 (_num_69 : int) =
  let rec _interp_135 (_x_100, _k_137) =
    match _x_100 with
    | Num _b_106 -> _k_137 _b_106
    | Add (_l_108, _r_107) ->
        _interp_135
          ( _l_108,
            fun (_x_109 : int) ->
              _interp_135
                (_r_107, fun (_y_110 : int) -> _k_137 (_x_109 + _y_110)) )
    | Mul (_l_113, _r_112) ->
        _interp_135
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_135
                (_r_112, fun (_y_115 : int) -> _k_137 (_x_114 * _y_115)) )
    | Sub (_l_118, _r_117) ->
        _interp_135
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_135
                (_r_117, fun (_y_120 : int) -> _k_137 (_x_119 - _y_120)) )
    | Div (_l_123, _r_122) ->
        _interp_135
          ( _r_122,
            fun (_y_124 : int) ->
              _interp_135
                ( _l_123,
                  fun (_x_125 : int) ->
                    match _y_124 with 0 -> ~-1 | _ -> _k_137 (_x_125 / _y_124)
                ) )
  in
  _interp_135 (_createCase_61 _num_69, fun (_id_96 : int) -> _id_96)

let bigTest = _bigTest_68

let _bigTestLoop_166 (_num_167 : int) =
  let ____finalCase_191 = _createCase_61 _num_167 in
  let rec _looper_214 _x_215 (_s_217 : int) =
    if _x_215 = 0 then _s_217
    else
      _looper_214 (_x_215 - 1)
        (_s_217
        +
        let rec _interp_259 (_x_210, _k_261) =
          match _x_210 with
          | Num _b_230 -> _k_261 _b_230
          | Add (_l_232, _r_231) ->
              _interp_259
                ( _l_232,
                  fun (_x_233 : int) ->
                    _interp_259
                      (_r_231, fun (_y_234 : int) -> _k_261 (_x_233 + _y_234))
                )
          | Mul (_l_237, _r_236) ->
              _interp_259
                ( _l_237,
                  fun (_x_238 : int) ->
                    _interp_259
                      (_r_236, fun (_y_239 : int) -> _k_261 (_x_238 * _y_239))
                )
          | Sub (_l_242, _r_241) ->
              _interp_259
                ( _l_242,
                  fun (_x_243 : int) ->
                    _interp_259
                      (_r_241, fun (_y_244 : int) -> _k_261 (_x_243 - _y_244))
                )
          | Div (_l_247, _r_246) ->
              _interp_259
                ( _r_246,
                  fun (_y_248 : int) ->
                    _interp_259
                      ( _l_247,
                        fun (_x_249 : int) ->
                          match _y_248 with
                          | 0 -> ~-1
                          | _ -> _k_261 (_x_249 / _y_248) ) )
        in
        _interp_259 (____finalCase_191, fun (_id_194 : int) -> _id_194))
  in
  _looper_214 100 0

let bigTestLoop = _bigTestLoop_166

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_290 (_n_291 : int) =
  let rec _interp_387 (_x_333, _k_389) =
    match _x_333 with
    | Num _b_345 -> fun (_ : int) -> _k_389 _b_345 (_b_345 * _b_345)
    | Add (_l_350, _r_349) ->
        _interp_387
          ( _l_350,
            fun (_x_351 : int) ->
              _interp_387
                (_r_349, fun (_y_352 : int) -> _k_389 (_x_351 + _y_352)) )
    | Mul (_l_355, _r_354) ->
        _interp_387
          ( _l_355,
            fun (_x_356 : int) ->
              _interp_387
                (_r_354, fun (_y_357 : int) -> _k_389 (_x_356 * _y_357)) )
    | Sub (_l_360, _r_359) ->
        _interp_387
          ( _l_360,
            fun (_x_361 : int) ->
              _interp_387
                (_r_359, fun (_y_362 : int) -> _k_389 (_x_361 - _y_362)) )
    | Div (_l_365, _r_364) ->
        _interp_387
          ( _r_364,
            fun (_y_366 : int) ->
              _interp_387
                ( _l_365,
                  fun (_x_367 : int) ->
                    match _y_366 with
                    | 0 -> fun (_s_419 : int) -> _k_389 _s_419 _s_419
                    | _ -> _k_389 (_x_367 / _y_366) ) )
  in
  _interp_387
    (_createCase_61 _n_291, fun (_x_324 : int) (_ : int) -> _x_324)
    _n_291

let testState = _testState_290

let _testStateLoop_447 (_n_448 : int) =
  let _addCase_449 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_450 _x_514 =
    match _x_514 with
    | 0 -> Sub (_addCase_449, _addCase_449)
    | _n_649 ->
        Sub
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             (_createZeroCase_450 (_n_649 - 1), _createZeroCase_450 (_n_649 - 1)))
  in
  let rec _createCase_459 _x_515 =
    match _x_515 with
    | 1 ->
        Div
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             (Num 100, _createZeroCase_450 3))
    | _ ->
        Add
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             (_addCase_449, _createCase_459 (_x_515 - 1)))
  in
  let ____finalCase_526 = _createCase_459 _n_448 in
  let rec _looper_527 _x_528 (_s_530 : int) =
    if _x_528 = 0 then _s_530
    else
      _looper_527 (_x_528 - 1)
        (_s_530
        +
        let rec _interp_588 (_x_520, _k_590) =
          match _x_520 with
          | Num _b_546 -> fun (_ : int) -> _k_590 _b_546 (_b_546 * _b_546)
          | Add (_l_551, _r_550) ->
              _interp_588
                ( _l_551,
                  fun (_x_552 : int) ->
                    _interp_588
                      (_r_550, fun (_y_553 : int) -> _k_590 (_x_552 + _y_553))
                )
          | Mul (_l_556, _r_555) ->
              _interp_588
                ( _l_556,
                  fun (_x_557 : int) ->
                    _interp_588
                      (_r_555, fun (_y_558 : int) -> _k_590 (_x_557 * _y_558))
                )
          | Sub (_l_561, _r_560) ->
              _interp_588
                ( _l_561,
                  fun (_x_562 : int) ->
                    _interp_588
                      (_r_560, fun (_y_563 : int) -> _k_590 (_x_562 - _y_563))
                )
          | Div (_l_566, _r_565) ->
              _interp_588
                ( _r_565,
                  fun (_y_567 : int) ->
                    _interp_588
                      ( _l_566,
                        fun (_x_568 : int) ->
                          match _y_567 with
                          | 0 -> fun (_s_620 : int) -> _k_590 _s_620 _s_620
                          | _ -> _k_590 (_x_568 / _y_567) ) )
        in
        _interp_588
          (____finalCase_526, fun (_x_497 : int) (_ : int) -> _x_497)
          _n_448)
  in
  _looper_527 100 0

let testStateLoop = _testStateLoop_447
