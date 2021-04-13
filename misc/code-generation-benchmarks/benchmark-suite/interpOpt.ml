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
  let rec _interp_135 (_x_105, _k_137) =
    match _x_105 with
    | Num _b_111 -> _k_137 _b_111
    | Add (_l_113, _r_112) ->
        _interp_135
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_135
                (_r_112, fun (_y_115 : int) -> _k_137 (_x_114 + _y_115)) )
    | Mul (_l_118, _r_117) ->
        _interp_135
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_135
                (_r_117, fun (_y_120 : int) -> _k_137 (_x_119 * _y_120)) )
    | Sub (_l_123, _r_122) ->
        _interp_135
          ( _l_123,
            fun (_x_124 : int) ->
              _interp_135
                (_r_122, fun (_y_125 : int) -> _k_137 (_x_124 - _y_125)) )
    | Div (_l_128, _r_127) ->
        _interp_135
          ( _r_127,
            fun (_y_129 : int) ->
              _interp_135
                ( _l_128,
                  fun (_x_130 : int) ->
                    match _y_129 with 0 -> ~-1 | _ -> _k_137 (_x_130 / _y_129)
                ) )
  in
  _interp_135 (_createCase_61 _num_74, fun (_id_101 : int) -> _id_101)

let bigTest = _bigTest_73

let _bigTestLoop_140 (_num_141 : int) =
  let ____finalCase_165 = _createCase_61 _num_141 in
  let rec _looper_198 _x_199 (_s_200 : int) =
    if _x_199 = 0 then _s_200
    else
      _looper_198 (_x_199 - 1)
        (_s_200
        +
        let rec _interp_237 (_x_184, _k_239) =
          match _x_184 with
          | Num _b_213 -> _k_239 _b_213
          | Add (_l_215, _r_214) ->
              _interp_237
                ( _l_215,
                  fun (_x_216 : int) ->
                    _interp_237
                      (_r_214, fun (_y_217 : int) -> _k_239 (_x_216 + _y_217))
                )
          | Mul (_l_220, _r_219) ->
              _interp_237
                ( _l_220,
                  fun (_x_221 : int) ->
                    _interp_237
                      (_r_219, fun (_y_222 : int) -> _k_239 (_x_221 * _y_222))
                )
          | Sub (_l_225, _r_224) ->
              _interp_237
                ( _l_225,
                  fun (_x_226 : int) ->
                    _interp_237
                      (_r_224, fun (_y_227 : int) -> _k_239 (_x_226 - _y_227))
                )
          | Div (_l_230, _r_229) ->
              _interp_237
                ( _r_229,
                  fun (_y_231 : int) ->
                    _interp_237
                      ( _l_230,
                        fun (_x_232 : int) ->
                          match _y_231 with
                          | 0 -> ~-1
                          | _ -> _k_239 (_x_232 / _y_231) ) )
        in
        _interp_237 (____finalCase_165, fun (_id_168 : int) -> _id_168))
  in
  _looper_198 100 0

let bigTestLoop = _bigTestLoop_140

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_242 (_n_243 : int) =
  let rec _interp_327 (_x_285, _k_329) =
    match _x_285 with
    | Num _b_297 -> fun (_ : int) -> _k_329 _b_297 (_b_297 * _b_297)
    | Add (_l_302, _r_301) ->
        _interp_327
          ( _l_302,
            fun (_x_303 : int) ->
              _interp_327
                (_r_301, fun (_y_304 : int) -> _k_329 (_x_303 + _y_304)) )
    | Mul (_l_307, _r_306) ->
        _interp_327
          ( _l_307,
            fun (_x_308 : int) ->
              _interp_327
                (_r_306, fun (_y_309 : int) -> _k_329 (_x_308 * _y_309)) )
    | Sub (_l_312, _r_311) ->
        _interp_327
          ( _l_312,
            fun (_x_313 : int) ->
              _interp_327
                (_r_311, fun (_y_314 : int) -> _k_329 (_x_313 - _y_314)) )
    | Div (_l_317, _r_316) ->
        _interp_327
          ( _r_316,
            fun (_y_318 : int) ->
              _interp_327
                ( _l_317,
                  fun (_x_319 : int) ->
                    match _y_318 with
                    | 0 -> fun (_s_337 : int) -> _k_329 _s_337 _s_337
                    | _ -> _k_329 (_x_319 / _y_318) ) )
  in
  _interp_327
    (_createCase_61 _n_243, fun (_x_276 : int) (_ : int) -> _x_276)
    _n_243

let testState = _testState_242

let _testStateLoop_340 (_n_341 : int) =
  let _addCase_342 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_343 _x_407 =
    match _x_407 with
    | 0 -> Sub (_addCase_342, _addCase_342)
    | _n_498 ->
        Sub (_createZeroCase_343 (_n_498 - 1), _createZeroCase_343 (_n_498 - 1))
  in
  let rec _createCase_352 _x_408 =
    match _x_408 with
    | 1 -> Div (Num 100, _createZeroCase_343 3)
    | _ -> Add (_addCase_342, _createCase_352 (_x_408 - 1))
  in
  let ____finalCase_430 = _createCase_352 _n_341 in
  let rec _looper_431 _x_432 (_s_433 : int) =
    if _x_432 = 0 then _s_433
    else
      _looper_431 (_x_432 - 1)
        (_s_433
        +
        let rec _interp_479 (_x_413, _k_481) =
          match _x_413 with
          | Num _b_449 -> fun (_ : int) -> _k_481 _b_449 (_b_449 * _b_449)
          | Add (_l_454, _r_453) ->
              _interp_479
                ( _l_454,
                  fun (_x_455 : int) ->
                    _interp_479
                      (_r_453, fun (_y_456 : int) -> _k_481 (_x_455 + _y_456))
                )
          | Mul (_l_459, _r_458) ->
              _interp_479
                ( _l_459,
                  fun (_x_460 : int) ->
                    _interp_479
                      (_r_458, fun (_y_461 : int) -> _k_481 (_x_460 * _y_461))
                )
          | Sub (_l_464, _r_463) ->
              _interp_479
                ( _l_464,
                  fun (_x_465 : int) ->
                    _interp_479
                      (_r_463, fun (_y_466 : int) -> _k_481 (_x_465 - _y_466))
                )
          | Div (_l_469, _r_468) ->
              _interp_479
                ( _r_468,
                  fun (_y_470 : int) ->
                    _interp_479
                      ( _l_469,
                        fun (_x_471 : int) ->
                          match _y_470 with
                          | 0 -> fun (_s_489 : int) -> _k_481 _s_489 _s_489
                          | _ -> _k_481 (_x_471 / _y_470) ) )
        in
        _interp_479
          (____finalCase_430, fun (_x_390 : int) (_ : int) -> _x_390)
          _n_341)
  in
  _looper_431 100 0

let testStateLoop = _testStateLoop_340
