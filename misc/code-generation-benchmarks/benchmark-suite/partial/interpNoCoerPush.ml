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
  | _n_54 -> Sub (_createZeroCase_43 (_n_54 - 1), _createZeroCase_43 (_n_54 - 1))

let createZeroCase = _createZeroCase_43

let rec _createCase_61 _x_67 =
  match _x_67 with
  | 1 -> Div (Num 100, _createZeroCase_43 3)
  | _ -> Add (_addCase_42, _createCase_61 (_x_67 - 1))

let createCase = _createCase_61

let _bigTest_73 (_num_74 : int) =
  let rec _interp_139 (_x_105, _k_141) =
    match _x_105 with
    | Num _b_111 -> _k_141 _b_111
    | Add (_l_113, _r_112) ->
        _interp_139
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_139
                (_r_112, fun (_y_115 : int) -> _k_141 (_x_114 + _y_115)) )
    | Mul (_l_118, _r_117) ->
        _interp_139
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_139
                (_r_117, fun (_y_120 : int) -> _k_141 (_x_119 * _y_120)) )
    | Sub (_l_123, _r_122) ->
        _interp_139
          ( _l_123,
            fun (_x_124 : int) ->
              _interp_139
                (_r_122, fun (_y_125 : int) -> _k_141 (_x_124 - _y_125)) )
    | Div (_l_128, _r_127) ->
        _interp_139
          ( _r_127,
            fun (_y_129 : int) ->
              _interp_139
                ( _l_128,
                  fun (_x_130 : int) ->
                    match _y_129 with 0 -> ~-1 | _ -> _k_141 (_x_130 / _y_129)
                ) )
  in
  _interp_139 (_createCase_61 _num_74, fun (_id_101 : int) -> _id_101)

let bigTest = _bigTest_73

let _bigTestLoop_158 (_num_159 : int) =
  let ____finalCase_183 = _createCase_61 _num_159 in
  let rec _looper_216 _x_217 (_s_218 : int) =
    if _x_217 = 0 then _s_218
    else
      _looper_216 (_x_217 - 1)
        (_s_218
        +
        let rec _interp_259 (_x_202, _k_261) =
          match _x_202 with
          | Num _b_231 -> _k_261 _b_231
          | Add (_l_233, _r_232) ->
              _interp_259
                ( _l_233,
                  fun (_x_234 : int) ->
                    _interp_259
                      (_r_232, fun (_y_235 : int) -> _k_261 (_x_234 + _y_235))
                )
          | Mul (_l_238, _r_237) ->
              _interp_259
                ( _l_238,
                  fun (_x_239 : int) ->
                    _interp_259
                      (_r_237, fun (_y_240 : int) -> _k_261 (_x_239 * _y_240))
                )
          | Sub (_l_243, _r_242) ->
              _interp_259
                ( _l_243,
                  fun (_x_244 : int) ->
                    _interp_259
                      (_r_242, fun (_y_245 : int) -> _k_261 (_x_244 - _y_245))
                )
          | Div (_l_248, _r_247) ->
              _interp_259
                ( _r_247,
                  fun (_y_249 : int) ->
                    _interp_259
                      ( _l_248,
                        fun (_x_250 : int) ->
                          match _y_249 with
                          | 0 -> ~-1
                          | _ -> _k_261 (_x_250 / _y_249) ) )
        in
        _interp_259 (____finalCase_183, fun (_id_186 : int) -> _id_186))
  in
  _looper_216 100 0

let bigTestLoop = _bigTestLoop_158

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_278 (_n_279 : int) =
  let rec _interp_374 (_x_321, _k_376) =
    match _x_321 with
    | Num _b_333 -> fun (_ : int) -> _k_376 _b_333 (_b_333 * _b_333)
    | Add (_l_338, _r_337) ->
        _interp_374
          ( _l_338,
            fun (_x_339 : int) ->
              _interp_374
                (_r_337, fun (_y_340 : int) -> _k_376 (_x_339 + _y_340)) )
    | Mul (_l_343, _r_342) ->
        _interp_374
          ( _l_343,
            fun (_x_344 : int) ->
              _interp_374
                (_r_342, fun (_y_345 : int) -> _k_376 (_x_344 * _y_345)) )
    | Sub (_l_348, _r_347) ->
        _interp_374
          ( _l_348,
            fun (_x_349 : int) ->
              _interp_374
                (_r_347, fun (_y_350 : int) -> _k_376 (_x_349 - _y_350)) )
    | Div (_l_353, _r_352) ->
        _interp_374
          ( _r_352,
            fun (_y_354 : int) ->
              _interp_374
                ( _l_353,
                  fun (_x_355 : int) ->
                    match _y_354 with
                    | 0 -> fun (_s_402 : int) -> _k_376 _s_402 _s_402
                    | _ -> _k_376 (_x_355 / _y_354) ) )
  in
  _interp_374
    (_createCase_61 _n_279, fun (_x_312 : int) (_ : int) -> _x_312)
    _n_279

let testState = _testState_278

let _testStateLoop_413 (_n_414 : int) =
  let _addCase_415 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_416 _x_480 =
    match _x_480 with
    | 0 -> Sub (_addCase_415, _addCase_415)
    | _n_608 ->
        Sub (_createZeroCase_416 (_n_608 - 1), _createZeroCase_416 (_n_608 - 1))
  in
  let rec _createCase_425 _x_481 =
    match _x_481 with
    | 1 -> Div (Num 100, _createZeroCase_416 3)
    | _ -> Add (_addCase_415, _createCase_425 (_x_481 - 1))
  in
  let ____finalCase_503 = _createCase_425 _n_414 in
  let rec _looper_504 _x_505 (_s_506 : int) =
    if _x_505 = 0 then _s_506
    else
      _looper_504 (_x_505 - 1)
        (_s_506
        +
        let rec _interp_563 (_x_486, _k_565) =
          match _x_486 with
          | Num _b_522 -> fun (_ : int) -> _k_565 _b_522 (_b_522 * _b_522)
          | Add (_l_527, _r_526) ->
              _interp_563
                ( _l_527,
                  fun (_x_528 : int) ->
                    _interp_563
                      (_r_526, fun (_y_529 : int) -> _k_565 (_x_528 + _y_529))
                )
          | Mul (_l_532, _r_531) ->
              _interp_563
                ( _l_532,
                  fun (_x_533 : int) ->
                    _interp_563
                      (_r_531, fun (_y_534 : int) -> _k_565 (_x_533 * _y_534))
                )
          | Sub (_l_537, _r_536) ->
              _interp_563
                ( _l_537,
                  fun (_x_538 : int) ->
                    _interp_563
                      (_r_536, fun (_y_539 : int) -> _k_565 (_x_538 - _y_539))
                )
          | Div (_l_542, _r_541) ->
              _interp_563
                ( _r_541,
                  fun (_y_543 : int) ->
                    _interp_563
                      ( _l_542,
                        fun (_x_544 : int) ->
                          match _y_543 with
                          | 0 -> fun (_s_591 : int) -> _k_565 _s_591 _s_591
                          | _ -> _k_565 (_x_544 / _y_543) ) )
        in
        _interp_563
          (____finalCase_503, fun (_x_463 : int) (_ : int) -> _x_463)
          _n_414)
  in
  _looper_504 100 0

let testStateLoop = _testStateLoop_413
