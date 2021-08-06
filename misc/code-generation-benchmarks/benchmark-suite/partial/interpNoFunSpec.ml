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
  let rec _interp_75 _x_105 =
    match _x_105 with
    | Num _b_111 -> Value _b_111
    | Add (_l_113, _r_112) ->
        _interp_75 _l_113 >>= fun _x_114 ->
        _interp_75 _r_112 >>= fun _y_115 -> Value (_x_114 + _y_115)
    | Mul (_l_118, _r_117) ->
        _interp_75 _l_118 >>= fun _x_119 ->
        _interp_75 _r_117 >>= fun _y_120 -> Value (_x_119 * _y_120)
    | Sub (_l_123, _r_122) ->
        _interp_75 _l_123 >>= fun _x_124 ->
        _interp_75 _r_122 >>= fun _y_125 -> Value (_x_124 - _y_125)
    | Div (_l_128, _r_127) -> (
        _interp_75 _r_127 >>= fun _y_129 ->
        _interp_75 _l_128 >>= fun _x_130 ->
        match _y_129 with
        | 0 -> Call (DivByZero, (), fun (_y_131 : int) -> Value _y_131)
        | _ -> Value (_x_130 / _y_129))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_101 : int) -> Value _id_101);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | DivByZero -> fun () _l_106 -> Value ~-1
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_interp_75 (_createCase_61 _num_74)))

let bigTest = _bigTest_73

let _bigTestLoop_162 (_num_163 : int) =
  let rec _interp_164 _x_206 =
    match _x_206 with
    | Num _b_235 -> Value _b_235
    | Add (_l_237, _r_236) ->
        _interp_164 _l_237 >>= fun _x_238 ->
        _interp_164 _r_236 >>= fun _y_239 -> Value (_x_238 + _y_239)
    | Mul (_l_242, _r_241) ->
        _interp_164 _l_242 >>= fun _x_243 ->
        _interp_164 _r_241 >>= fun _y_244 -> Value (_x_243 * _y_244)
    | Sub (_l_247, _r_246) ->
        _interp_164 _l_247 >>= fun _x_248 ->
        _interp_164 _r_246 >>= fun _y_249 -> Value (_x_248 - _y_249)
    | Div (_l_252, _r_251) -> (
        _interp_164 _r_251 >>= fun _y_253 ->
        _interp_164 _l_252 >>= fun _x_254 ->
        match _y_253 with
        | 0 -> Call (DivByZero, (), fun (_y_255 : int) -> Value _y_255)
        | _ -> Value (_x_254 / _y_253))
  in
  let ____finalCase_187 = _createCase_61 _num_163 in
  let rec _looper_220 _x_221 (_s_222 : int) =
    if _x_221 = 0 then _s_222
    else
      _looper_220 (_x_221 - 1)
        (_s_222
        + force_unsafe
            ((handler
                {
                  value_clause = (fun (_id_190 : int) -> Value _id_190);
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | DivByZero -> fun () _l_207 -> Value ~-1
                      | eff' -> fun arg k -> Call (eff', arg, k));
                })
               (_interp_164 ____finalCase_187)))
  in
  _looper_220 100 0

let bigTestLoop = _bigTestLoop_162

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_286 (_n_287 : int) =
  let rec _interp_288 _x_329 =
    match _x_329 with
    | Num _b_341 ->
        Call (Set, _b_341 * _b_341, fun (_y_344 : unit) -> Value _b_341)
    | Add (_l_346, _r_345) ->
        _interp_288 _l_346 >>= fun _x_347 ->
        _interp_288 _r_345 >>= fun _y_348 -> Value (_x_347 + _y_348)
    | Mul (_l_351, _r_350) ->
        _interp_288 _l_351 >>= fun _x_352 ->
        _interp_288 _r_350 >>= fun _y_353 -> Value (_x_352 * _y_353)
    | Sub (_l_356, _r_355) ->
        _interp_288 _l_356 >>= fun _x_357 ->
        _interp_288 _r_355 >>= fun _y_358 -> Value (_x_357 - _y_358)
    | Div (_l_361, _r_360) -> (
        _interp_288 _r_360 >>= fun _y_362 ->
        _interp_288 _l_361 >>= fun _x_363 ->
        match _y_362 with
        | 0 -> Call (Get, (), fun (_y_364 : int) -> Value _y_364)
        | _ -> Value (_x_363 / _y_362))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x_320 : int) -> Value (fun (_ : int) -> _x_320));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Get ->
                  fun () _l_330 ->
                    Value
                      (fun (_s_315 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_330 _s_315
                          _s_315)
              | Set ->
                  fun _s_317 _l_331 ->
                    Value
                      (fun (_ : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_331 () _s_317)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_interp_288 (_createCase_61 _n_287)))
    _n_287

let testState = _testState_286

let _testStateLoop_418 (_n_419 : int) =
  let _addCase_420 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_421 _x_485 =
    match _x_485 with
    | 0 -> Sub (_addCase_420, _addCase_420)
    | _n_662 ->
        Sub (_createZeroCase_421 (_n_662 - 1), _createZeroCase_421 (_n_662 - 1))
  in
  let rec _createCase_430 _x_486 =
    match _x_486 with
    | 1 -> Div (Num 100, _createZeroCase_421 3)
    | _ -> Add (_addCase_420, _createCase_430 (_x_486 - 1))
  in
  let rec _interp_436 _x_491 =
    match _x_491 with
    | Num _b_527 ->
        Call (Set, _b_527 * _b_527, fun (_y_530 : unit) -> Value _b_527)
    | Add (_l_532, _r_531) ->
        _interp_436 _l_532 >>= fun _x_533 ->
        _interp_436 _r_531 >>= fun _y_534 -> Value (_x_533 + _y_534)
    | Mul (_l_537, _r_536) ->
        _interp_436 _l_537 >>= fun _x_538 ->
        _interp_436 _r_536 >>= fun _y_539 -> Value (_x_538 * _y_539)
    | Sub (_l_542, _r_541) ->
        _interp_436 _l_542 >>= fun _x_543 ->
        _interp_436 _r_541 >>= fun _y_544 -> Value (_x_543 - _y_544)
    | Div (_l_547, _r_546) -> (
        _interp_436 _r_546 >>= fun _y_548 ->
        _interp_436 _l_547 >>= fun _x_549 ->
        match _y_548 with
        | 0 -> Call (Get, (), fun (_y_550 : int) -> Value _y_550)
        | _ -> Value (_x_549 / _y_548))
  in
  let ____finalCase_508 = _createCase_430 _n_419 in
  let rec _looper_509 _x_510 (_s_511 : int) =
    if _x_510 = 0 then _s_511
    else
      _looper_509 (_x_510 - 1)
        (_s_511
        + force_unsafe
            ((handler
                {
                  value_clause =
                    (fun (_x_468 : int) -> Value (fun (_ : int) -> _x_468));
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | Get ->
                          fun () _l_492 ->
                            Value
                              (fun (_s_463 : int) ->
                                coer_arrow coer_refl_ty force_unsafe _l_492
                                  _s_463 _s_463)
                      | Set ->
                          fun _s_465 _l_493 ->
                            Value
                              (fun (_ : int) ->
                                coer_arrow coer_refl_ty force_unsafe _l_493 ()
                                  _s_465)
                      | eff' -> fun arg k -> Call (eff', arg, k));
                })
               (_interp_436 ____finalCase_508))
            _n_419)
  in
  _looper_509 100 0

let testStateLoop = _testStateLoop_418
