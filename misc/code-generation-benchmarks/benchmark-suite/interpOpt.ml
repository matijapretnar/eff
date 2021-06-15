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
  let rec _interp_140 (_x_105, _k_142) =
    match _x_105 with
    | Num _b_111 -> _k_142 _b_111
    | Add (_l_113, _r_112) ->
        _interp_140
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_140
                (_r_112, fun (_y_115 : int) -> _k_142 (_x_114 + _y_115)) )
    | Mul (_l_118, _r_117) ->
        _interp_140
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_140
                (_r_117, fun (_y_120 : int) -> _k_142 (_x_119 * _y_120)) )
    | Sub (_l_123, _r_122) ->
        _interp_140
          ( _l_123,
            fun (_x_124 : int) ->
              _interp_140
                (_r_122, fun (_y_125 : int) -> _k_142 (_x_124 - _y_125)) )
    | Div (_l_128, _r_127) ->
        _interp_140
          ( _r_127,
            fun (_y_129 : int) ->
              _interp_140
                ( _l_128,
                  fun (_x_130 : int) ->
                    match _y_129 with 0 -> ~-1 | _ -> _k_142 (_x_130 / _y_129)
                ) )
  in
  _interp_140 (_createCase_61 _num_74, fun (_id_101 : int) -> _id_101)

let bigTest = _bigTest_73

let _bigTestLoop_171 (_num_172 : int) =
  let ____finalCase_196 = _createCase_61 _num_172 in
  let rec _looper_229 _x_230 (_s_231 : int) =
    if _x_230 = 0 then _s_231
    else
      _looper_229 (_x_230 - 1)
        (_s_231
        +
        let rec _interp_273 (_x_215, _k_275) =
          match _x_215 with
          | Num _b_244 -> _k_275 _b_244
          | Add (_l_246, _r_245) ->
              _interp_273
                ( _l_246,
                  fun (_x_247 : int) ->
                    _interp_273
                      (_r_245, fun (_y_248 : int) -> _k_275 (_x_247 + _y_248))
                )
          | Mul (_l_251, _r_250) ->
              _interp_273
                ( _l_251,
                  fun (_x_252 : int) ->
                    _interp_273
                      (_r_250, fun (_y_253 : int) -> _k_275 (_x_252 * _y_253))
                )
          | Sub (_l_256, _r_255) ->
              _interp_273
                ( _l_256,
                  fun (_x_257 : int) ->
                    _interp_273
                      (_r_255, fun (_y_258 : int) -> _k_275 (_x_257 - _y_258))
                )
          | Div (_l_261, _r_260) ->
              _interp_273
                ( _r_260,
                  fun (_y_262 : int) ->
                    _interp_273
                      ( _l_261,
                        fun (_x_263 : int) ->
                          match _y_262 with
                          | 0 -> ~-1
                          | _ -> _k_275 (_x_263 / _y_262) ) )
        in
        _interp_273 (____finalCase_196, fun (_id_199 : int) -> _id_199))
  in
  _looper_229 100 0

let bigTestLoop = _bigTestLoop_171

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_304 (_n_305 : int) =
  let rec _interp_401 (_x_347, _k_403) =
    match _x_347 with
    | Num _b_359 -> fun (_ : int) -> _k_403 _b_359 (_b_359 * _b_359)
    | Add (_l_364, _r_363) ->
        _interp_401
          ( _l_364,
            fun (_x_365 : int) ->
              _interp_401
                (_r_363, fun (_y_366 : int) -> _k_403 (_x_365 + _y_366)) )
    | Mul (_l_369, _r_368) ->
        _interp_401
          ( _l_369,
            fun (_x_370 : int) ->
              _interp_401
                (_r_368, fun (_y_371 : int) -> _k_403 (_x_370 * _y_371)) )
    | Sub (_l_374, _r_373) ->
        _interp_401
          ( _l_374,
            fun (_x_375 : int) ->
              _interp_401
                (_r_373, fun (_y_376 : int) -> _k_403 (_x_375 - _y_376)) )
    | Div (_l_379, _r_378) ->
        _interp_401
          ( _r_378,
            fun (_y_380 : int) ->
              _interp_401
                ( _l_379,
                  fun (_x_381 : int) ->
                    match _y_380 with
                    | 0 -> fun (_s_430 : int) -> _k_403 _s_430 _s_430
                    | _ -> _k_403 (_x_381 / _y_380) ) )
  in
  _interp_401
    (_createCase_61 _n_305, fun (_x_338 : int) (_ : int) -> _x_338)
    _n_305

let testState = _testState_304

let _testStateLoop_457 (_n_458 : int) =
  let _addCase_459 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_460 _x_524 =
    match _x_524 with
    | 0 -> Sub (_addCase_459, _addCase_459)
    | _n_670 ->
        Sub (_createZeroCase_460 (_n_670 - 1), _createZeroCase_460 (_n_670 - 1))
  in
  let rec _createCase_469 _x_525 =
    match _x_525 with
    | 1 -> Div (Num 100, _createZeroCase_460 3)
    | _ -> Add (_addCase_459, _createCase_469 (_x_525 - 1))
  in
  let ____finalCase_547 = _createCase_469 _n_458 in
  let rec _looper_548 _x_549 (_s_550 : int) =
    if _x_549 = 0 then _s_550
    else
      _looper_548 (_x_549 - 1)
        (_s_550
        +
        let rec _interp_608 (_x_530, _k_610) =
          match _x_530 with
          | Num _b_566 -> fun (_ : int) -> _k_610 _b_566 (_b_566 * _b_566)
          | Add (_l_571, _r_570) ->
              _interp_608
                ( _l_571,
                  fun (_x_572 : int) ->
                    _interp_608
                      (_r_570, fun (_y_573 : int) -> _k_610 (_x_572 + _y_573))
                )
          | Mul (_l_576, _r_575) ->
              _interp_608
                ( _l_576,
                  fun (_x_577 : int) ->
                    _interp_608
                      (_r_575, fun (_y_578 : int) -> _k_610 (_x_577 * _y_578))
                )
          | Sub (_l_581, _r_580) ->
              _interp_608
                ( _l_581,
                  fun (_x_582 : int) ->
                    _interp_608
                      (_r_580, fun (_y_583 : int) -> _k_610 (_x_582 - _y_583))
                )
          | Div (_l_586, _r_585) ->
              _interp_608
                ( _r_585,
                  fun (_y_587 : int) ->
                    _interp_608
                      ( _l_586,
                        fun (_x_588 : int) ->
                          match _y_587 with
                          | 0 -> fun (_s_637 : int) -> _k_610 _s_637 _s_637
                          | _ -> _k_610 (_x_588 / _y_587) ) )
        in
        _interp_608
          (____finalCase_547, fun (_x_507 : int) (_ : int) -> _x_507)
          _n_458)
  in
  _looper_548 100 0

let testStateLoop = _testStateLoop_457
