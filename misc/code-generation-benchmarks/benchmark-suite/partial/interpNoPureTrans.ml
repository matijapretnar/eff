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
  | 0 -> Value (Sub (_addCase_42, _addCase_42))
  | _n_54 ->
      Value (( - ) _n_54) >>= fun _b_55 ->
      Value (_b_55 1) >>= fun _b_56 ->
      Value (_createZeroCase_43 _b_56) >>= fun _b_57 ->
      Value (( - ) _n_54) >>= fun _b_58 ->
      Value (_b_58 1) >>= fun _b_59 ->
      Value (_createZeroCase_43 _b_59) >>= fun _b_60 ->
      Value (Sub (force_unsafe _b_57, force_unsafe _b_60))

let createZeroCase = _createZeroCase_43

let rec _createCase_61 _x_67 =
  match _x_67 with
  | 1 ->
      Value (_createZeroCase_43 3) >>= fun _b_69 ->
      Value (Div (Num 100, force_unsafe _b_69))
  | _ ->
      Value (( - ) _x_67) >>= fun _b_70 ->
      Value (_b_70 1) >>= fun _b_71 ->
      Value (_createCase_61 _b_71) >>= fun _b_72 ->
      Value (Add (_addCase_42, force_unsafe _b_72))

let createCase = _createCase_61

let _bigTest_73 (_num_74 : int) =
  Value (_createCase_61 _num_74) >>= fun _finalCase_98 ->
  let rec _interp_140 (_x_105, _k_142) =
    match _x_105 with
    | Num _b_111 -> _k_142 _b_111
    | Add (_l_113, _r_112) ->
        _interp_140
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_140
                ( _r_112,
                  fun (_y_115 : int) ->
                    Value (( + ) _x_114) >>= fun _x_148 ->
                    Value (_x_148 _y_115) >>= fun _x_164 -> _k_142 _x_164 ) )
    | Mul (_l_118, _r_117) ->
        _interp_140
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_140
                ( _r_117,
                  fun (_y_120 : int) ->
                    Value (( * ) _x_119) >>= fun _x_150 ->
                    Value (_x_150 _y_120) >>= fun _x_167 -> _k_142 _x_167 ) )
    | Sub (_l_123, _r_122) ->
        _interp_140
          ( _l_123,
            fun (_x_124 : int) ->
              _interp_140
                ( _r_122,
                  fun (_y_125 : int) ->
                    Value (( - ) _x_124) >>= fun _x_152 ->
                    Value (_x_152 _y_125) >>= fun _x_170 -> _k_142 _x_170 ) )
    | Div (_l_128, _r_127) ->
        _interp_140
          ( _r_127,
            fun (_y_129 : int) ->
              _interp_140
                ( _l_128,
                  fun (_x_130 : int) ->
                    match _y_129 with
                    | 0 -> Value ~-1
                    | _ ->
                        Value (( / ) _x_130) >>= fun _x_158 ->
                        Value (_x_158 _y_129) >>= fun _x_161 -> _k_142 _x_161 )
          )
  in
  _interp_140 (force_unsafe _finalCase_98, fun (_id_101 : int) -> Value _id_101)

let bigTest = _bigTest_73

let _bigTestLoop_171 (_num_172 : int) =
  Value (_createCase_61 _num_172) >>= fun ____finalCase_196 ->
  let rec _looper_229 _x_230 (_s_231 : int) =
    Value (( = ) _x_230) >>= fun _b_232 ->
    Value (_b_232 0) >>= fun _b_233 ->
    if _b_233 then Value _s_231
    else
      Value (( - ) _x_230) >>= fun _b_234 ->
      Value (_b_234 1) >>= fun _b_235 ->
      Value (_looper_229 _b_235) >>= fun _b_236 ->
      Value (( + ) _s_231) >>= fun _b_237 ->
      Value
        (let rec _interp_273 (_x_215, _k_275) =
           match _x_215 with
           | Num _b_244 -> _k_275 _b_244
           | Add (_l_246, _r_245) ->
               _interp_273
                 ( _l_246,
                   fun (_x_247 : int) ->
                     _interp_273
                       ( _r_245,
                         fun (_y_248 : int) ->
                           Value (( + ) _x_247) >>= fun _x_281 ->
                           Value (_x_281 _y_248) >>= fun _x_297 -> _k_275 _x_297
                       ) )
           | Mul (_l_251, _r_250) ->
               _interp_273
                 ( _l_251,
                   fun (_x_252 : int) ->
                     _interp_273
                       ( _r_250,
                         fun (_y_253 : int) ->
                           Value (( * ) _x_252) >>= fun _x_283 ->
                           Value (_x_283 _y_253) >>= fun _x_300 -> _k_275 _x_300
                       ) )
           | Sub (_l_256, _r_255) ->
               _interp_273
                 ( _l_256,
                   fun (_x_257 : int) ->
                     _interp_273
                       ( _r_255,
                         fun (_y_258 : int) ->
                           Value (( - ) _x_257) >>= fun _x_285 ->
                           Value (_x_285 _y_258) >>= fun _x_303 -> _k_275 _x_303
                       ) )
           | Div (_l_261, _r_260) ->
               _interp_273
                 ( _r_260,
                   fun (_y_262 : int) ->
                     _interp_273
                       ( _l_261,
                         fun (_x_263 : int) ->
                           match _y_262 with
                           | 0 -> Value ~-1
                           | _ ->
                               Value (( / ) _x_263) >>= fun _x_291 ->
                               Value (_x_291 _y_262) >>= fun _x_294 ->
                               _k_275 _x_294 ) )
         in
         _interp_273
           (force_unsafe ____finalCase_196, fun (_id_199 : int) -> Value _id_199))
      >>= fun _b_238 ->
      Value (_b_237 (force_unsafe _b_238)) >>= fun _b_239 -> _b_236 _b_239
  in
  Value (_looper_229 100) >>= fun _b_240 -> _b_240 0

let bigTestLoop = _bigTestLoop_171

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_304 (_n_305 : int) : int computation =
  Value (_createCase_61 _n_305) >>= fun _finalCase_352 ->
  Value
    (let rec _interp_401 (_x_347, _k_403) =
       match _x_347 with
       | Num _b_359 ->
           Value (( * ) _b_359) >>= fun _x_418 ->
           Value (_x_418 _b_359) >>= fun _x_450 (_ : int) ->
           Value (_k_403 _b_359) >>= fun _b_451 -> _b_451 _x_450
       | Add (_l_364, _r_363) ->
           _interp_401
             ( _l_364,
               fun (_x_365 : int) ->
                 _interp_401
                   ( _r_363,
                     fun (_y_366 : int) ->
                       Value (( + ) _x_365) >>= fun _x_420 ->
                       Value (_x_420 _y_366) >>= fun _x_454 -> _k_403 _x_454 )
             )
       | Mul (_l_369, _r_368) ->
           _interp_401
             ( _l_369,
               fun (_x_370 : int) ->
                 _interp_401
                   ( _r_368,
                     fun (_y_371 : int) ->
                       Value (( * ) _x_370) >>= fun _x_422 ->
                       Value (_x_422 _y_371) >>= fun _x_457 -> _k_403 _x_457 )
             )
       | Sub (_l_374, _r_373) ->
           _interp_401
             ( _l_374,
               fun (_x_375 : int) ->
                 _interp_401
                   ( _r_373,
                     fun (_y_376 : int) ->
                       Value (( - ) _x_375) >>= fun _x_424 ->
                       Value (_x_424 _y_376) >>= fun _x_460 -> _k_403 _x_460 )
             )
       | Div (_l_379, _r_378) ->
           _interp_401
             ( _r_378,
               fun (_y_380 : int) ->
                 _interp_401
                   ( _l_379,
                     fun (_x_381 : int) ->
                       match _y_380 with
                       | 0 ->
                          (fun (_s_433 : int) ->
                             Value (_k_403 _s_433) >>= fun _b_434 ->
                             Value (_b_434 _s_433))
                       | _ ->
                           Value (( / ) _x_381) >>= fun _x_437 ->
                           Value (_x_437 _y_380) >>= fun _x_441 -> _k_403 _x_441
                   ) )
     in
     _interp_401
       (force_unsafe _finalCase_352, fun (_x_338 : int) (_ : int) -> _x_338))
  >>= fun _b_353 -> (force_unsafe _b_353) _n_305

let testState = _testState_304

let _testStateLoop_461 (_n_462 : int) =
  let _addCase_463 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_464 _x_528 =
    match _x_528 with
    | 0 -> Sub (_addCase_463, _addCase_463)
    | _n_678 ->
        Value (( - ) _n_678) >>= fun _b_679 ->
        Value (_b_679 1) >>= fun _b_680 ->
        Value (_createZeroCase_464 _b_680) >>= fun _b_681 ->
        Value (( - ) _n_678) >>= fun _b_682 ->
        Value (_b_682 1) >>= fun _b_683 ->
        Value (_createZeroCase_464 _b_683) >>= fun _b_684 -> Sub (_b_681, _b_684)
  in
  let rec _createCase_473 _x_529 =
    match _x_529 with
    | 1 ->
        Value (_createZeroCase_464 3) >>= fun _b_673 ->
        Value (Div (Num 100, _b_673))
    | _ ->
        Value (( - ) _x_529) >>= fun _b_674 ->
        Value (_b_674 1) >>= fun _b_675 ->
        Value (_createCase_473 _b_675) >>= fun _b_676 ->
        Value (Add (_addCase_463, force_unsafe _b_676))
  in
  Value (_createCase_473 _n_462) >>= fun ____finalCase_551 ->
  let rec _looper_552 _x_553 (_s_554 : int) =
    Value (( = ) _x_553) >>= fun _b_555 ->
    Value (_b_555 0) >>= fun _b_556 ->
    if _b_556 then Value _s_554
    else
      Value
        (let rec _interp_612 (_x_534, _k_614) =
           match _x_534 with
           | Num _b_570 ->
               Value (( * ) _b_570) >>= fun _x_629 ->
               Value (_x_629 _b_570) >>= fun _x_661 (_ : int) ->
               Value (_k_614 _b_570) >>= fun _b_662 -> _b_662 _x_661
           | Add (_l_575, _r_574) ->
               _interp_612
                 ( _l_575,
                   fun (_x_576 : int) ->
                     _interp_612
                       ( _r_574,
                         fun (_y_577 : int) ->
                           Value (( + ) _x_576) >>= fun _x_631 ->
                           Value (_x_631 _y_577) >>= fun _x_665 -> _k_614 _x_665
                       ) )
           | Mul (_l_580, _r_579) ->
               _interp_612
                 ( _l_580,
                   fun (_x_581 : int) ->
                     _interp_612
                       ( _r_579,
                         fun (_y_582 : int) ->
                           Value (( * ) _x_581) >>= fun _x_633 ->
                           Value (_x_633 _y_582) >>= fun _x_668 -> _k_614 _x_668
                       ) )
           | Sub (_l_585, _r_584) ->
               _interp_612
                 ( _l_585,
                   fun (_x_586 : int) ->
                     _interp_612
                       ( _r_584,
                         fun (_y_587 : int) ->
                           Value (( - ) _x_586) >>= fun _x_635 ->
                           Value (_x_635 _y_587) >>= fun _x_671 -> _k_614 _x_671
                       ) )
           | Div (_l_590, _r_589) ->
               _interp_612
                 ( _r_589,
                   fun (_y_591 : int) ->
                     _interp_612
                       ( _l_590,
                         fun (_x_592 : int) ->
                           match _y_591 with
                           | 0 ->
                               fun (_s_644 : int) ->
                                 Value (_k_614 _s_644) >>= fun _b_645 ->
                                 _b_645 _s_644
                           | _ ->
                               Value (( / ) _x_592) >>= fun _x_648 ->
                               Value (_x_648 _y_591) >>= fun _x_652 ->
                               _k_614 _x_652 ) )
         in
         _interp_612
           ( force_unsafe ____finalCase_551,
             fun (_x_511 : int) (_ : int) -> _x_511 ))
      >>= fun _b_557 ->
      Value ((force_unsafe _b_557) _n_462) >>= fun _x_558 ->
      Value (( - ) _x_553) >>= fun _b_559 ->
      Value (_b_559 1) >>= fun _b_560 ->
      Value (_looper_552 _b_560) >>= fun _b_561 ->
      Value (( + ) _s_554) >>= fun _b_562 ->
      Value (_b_562 _x_558) >>= fun _b_563 -> _b_561 _b_563
  in
  Value (_looper_552 100) >>= fun _b_564 -> _b_564 0

let testStateLoop = _testStateLoop_461
