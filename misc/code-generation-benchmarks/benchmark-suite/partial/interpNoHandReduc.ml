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
  let rec _interp_133 _x_105 =
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
         (match _x_105 with
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
             | _ -> Value (_x_130 / _y_129))))
  in
  _interp_133 (_createCase_61 _num_74)

let bigTest = _bigTest_73

let _bigTestLoop_134 (_num_135 : int) =
  let rec _interp_136 _x_178 =
    match _x_178 with
    | Num _b_207 -> Value _b_207
    | Add (_l_209, _r_208) ->
        _interp_136 _l_209 >>= fun _x_210 ->
        _interp_136 _r_208 >>= fun _y_211 -> Value (_x_210 + _y_211)
    | Mul (_l_214, _r_213) ->
        _interp_136 _l_214 >>= fun _x_215 ->
        _interp_136 _r_213 >>= fun _y_216 -> Value (_x_215 * _y_216)
    | Sub (_l_219, _r_218) ->
        _interp_136 _l_219 >>= fun _x_220 ->
        _interp_136 _r_218 >>= fun _y_221 -> Value (_x_220 - _y_221)
    | Div (_l_224, _r_223) -> (
        _interp_136 _r_223 >>= fun _y_225 ->
        _interp_136 _l_224 >>= fun _x_226 ->
        match _y_225 with
        | 0 -> Call (DivByZero, (), fun (_y_227 : int) -> Value _y_227)
        | _ -> Value (_x_226 / _y_225))
  in
  let ____finalCase_159 = _createCase_61 _num_135 in
  let rec _looper_192 _x_193 (_s_194 : int) =
    if _x_193 = 0 then _s_194
    else
      _looper_192 (_x_193 - 1)
        (_s_194
        +
        let rec _interp_229 _x_178 =
          force_unsafe
            ((handler
                {
                  value_clause = (fun (_id_162 : int) -> Value _id_162);
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | DivByZero -> fun () _l_179 -> Value ~-1
                      | eff' -> fun arg k -> Call (eff', arg, k));
                })
               (match _x_178 with
               | Num _b_207 -> Value _b_207
               | Add (_l_209, _r_208) ->
                   _interp_136 _l_209 >>= fun _x_210 ->
                   _interp_136 _r_208 >>= fun _y_211 -> Value (_x_210 + _y_211)
               | Mul (_l_214, _r_213) ->
                   _interp_136 _l_214 >>= fun _x_215 ->
                   _interp_136 _r_213 >>= fun _y_216 -> Value (_x_215 * _y_216)
               | Sub (_l_219, _r_218) ->
                   _interp_136 _l_219 >>= fun _x_220 ->
                   _interp_136 _r_218 >>= fun _y_221 -> Value (_x_220 - _y_221)
               | Div (_l_224, _r_223) -> (
                   _interp_136 _r_223 >>= fun _y_225 ->
                   _interp_136 _l_224 >>= fun _x_226 ->
                   match _y_225 with
                   | 0 ->
                       Call (DivByZero, (), fun (_y_227 : int) -> Value _y_227)
                   | _ -> Value (_x_226 / _y_225))))
        in
        _interp_229 ____finalCase_159)
  in
  _looper_192 100 0

let bigTestLoop = _bigTestLoop_134

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_230 (_n_231 : int) =
  let rec _interp_232 _x_273 =
    match _x_273 with
    | Num _b_285 ->
        Call (Set, _b_285 * _b_285, fun (_y_288 : unit) -> Value _b_285)
    | Add (_l_290, _r_289) ->
        _interp_232 _l_290 >>= fun _x_291 ->
        _interp_232 _r_289 >>= fun _y_292 -> Value (_x_291 + _y_292)
    | Mul (_l_295, _r_294) ->
        _interp_232 _l_295 >>= fun _x_296 ->
        _interp_232 _r_294 >>= fun _y_297 -> Value (_x_296 * _y_297)
    | Sub (_l_300, _r_299) ->
        _interp_232 _l_300 >>= fun _x_301 ->
        _interp_232 _r_299 >>= fun _y_302 -> Value (_x_301 - _y_302)
    | Div (_l_305, _r_304) -> (
        _interp_232 _r_304 >>= fun _y_306 ->
        _interp_232 _l_305 >>= fun _x_307 ->
        match _y_306 with
        | 0 -> Call (Get, (), fun (_y_308 : int) -> Value _y_308)
        | _ -> Value (_x_307 / _y_306))
  in
  let rec _interp_310 _x_273 =
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x_264 : int) -> Value (fun (_ : int) -> _x_264));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Get ->
                    fun () _l_274 ->
                      Value
                        (fun (_s_259 : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_274 _s_259
                            _s_259)
                | Set ->
                    fun _s_261 _l_275 ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_275 () _s_261)
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (match _x_273 with
         | Num _b_285 ->
             Call (Set, _b_285 * _b_285, fun (_y_288 : unit) -> Value _b_285)
         | Add (_l_290, _r_289) ->
             _interp_232 _l_290 >>= fun _x_291 ->
             _interp_232 _r_289 >>= fun _y_292 -> Value (_x_291 + _y_292)
         | Mul (_l_295, _r_294) ->
             _interp_232 _l_295 >>= fun _x_296 ->
             _interp_232 _r_294 >>= fun _y_297 -> Value (_x_296 * _y_297)
         | Sub (_l_300, _r_299) ->
             _interp_232 _l_300 >>= fun _x_301 ->
             _interp_232 _r_299 >>= fun _y_302 -> Value (_x_301 - _y_302)
         | Div (_l_305, _r_304) -> (
             _interp_232 _r_304 >>= fun _y_306 ->
             _interp_232 _l_305 >>= fun _x_307 ->
             match _y_306 with
             | 0 -> Call (Get, (), fun (_y_308 : int) -> Value _y_308)
             | _ -> Value (_x_307 / _y_306))))
  in
  _interp_310 (_createCase_61 _n_231) _n_231

let testState = _testState_230

let _testStateLoop_311 (_n_312 : int) =
  let _addCase_313 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createZeroCase_314 _x_378 =
    match _x_378 with
    | 0 -> Sub (_addCase_313, _addCase_313)
    | _n_453 ->
        Sub (_createZeroCase_314 (_n_453 - 1), _createZeroCase_314 (_n_453 - 1))
  in
  let rec _createCase_323 _x_379 =
    match _x_379 with
    | 1 -> Div (Num 100, _createZeroCase_314 3)
    | _ -> Add (_addCase_313, _createCase_323 (_x_379 - 1))
  in
  let rec _interp_329 _x_384 =
    match _x_384 with
    | Num _b_420 ->
        Call (Set, _b_420 * _b_420, fun (_y_423 : unit) -> Value _b_420)
    | Add (_l_425, _r_424) ->
        _interp_329 _l_425 >>= fun _x_426 ->
        _interp_329 _r_424 >>= fun _y_427 -> Value (_x_426 + _y_427)
    | Mul (_l_430, _r_429) ->
        _interp_329 _l_430 >>= fun _x_431 ->
        _interp_329 _r_429 >>= fun _y_432 -> Value (_x_431 * _y_432)
    | Sub (_l_435, _r_434) ->
        _interp_329 _l_435 >>= fun _x_436 ->
        _interp_329 _r_434 >>= fun _y_437 -> Value (_x_436 - _y_437)
    | Div (_l_440, _r_439) -> (
        _interp_329 _r_439 >>= fun _y_441 ->
        _interp_329 _l_440 >>= fun _x_442 ->
        match _y_441 with
        | 0 -> Call (Get, (), fun (_y_443 : int) -> Value _y_443)
        | _ -> Value (_x_442 / _y_441))
  in
  let ____finalCase_401 = _createCase_323 _n_312 in
  let rec _looper_402 _x_403 (_s_404 : int) =
    if _x_403 = 0 then _s_404
    else
      _looper_402 (_x_403 - 1)
        (_s_404
        +
        let rec _interp_445 _x_384 =
          force_unsafe
            ((handler
                {
                  value_clause =
                    (fun (_x_361 : int) -> Value (fun (_ : int) -> _x_361));
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | Get ->
                          fun () _l_385 ->
                            Value
                              (fun (_s_356 : int) ->
                                coer_arrow coer_refl_ty force_unsafe _l_385
                                  _s_356 _s_356)
                      | Set ->
                          fun _s_358 _l_386 ->
                            Value
                              (fun (_ : int) ->
                                coer_arrow coer_refl_ty force_unsafe _l_386 ()
                                  _s_358)
                      | eff' -> fun arg k -> Call (eff', arg, k));
                })
               (match _x_384 with
               | Num _b_420 ->
                   Call
                     (Set, _b_420 * _b_420, fun (_y_423 : unit) -> Value _b_420)
               | Add (_l_425, _r_424) ->
                   _interp_329 _l_425 >>= fun _x_426 ->
                   _interp_329 _r_424 >>= fun _y_427 -> Value (_x_426 + _y_427)
               | Mul (_l_430, _r_429) ->
                   _interp_329 _l_430 >>= fun _x_431 ->
                   _interp_329 _r_429 >>= fun _y_432 -> Value (_x_431 * _y_432)
               | Sub (_l_435, _r_434) ->
                   _interp_329 _l_435 >>= fun _x_436 ->
                   _interp_329 _r_434 >>= fun _y_437 -> Value (_x_436 - _y_437)
               | Div (_l_440, _r_439) -> (
                   _interp_329 _r_439 >>= fun _y_441 ->
                   _interp_329 _l_440 >>= fun _x_442 ->
                   match _y_441 with
                   | 0 -> Call (Get, (), fun (_y_443 : int) -> Value _y_443)
                   | _ -> Value (_x_442 / _y_441))))
        in
        _interp_445 ____finalCase_401 _n_312)
  in
  _looper_402 100 0

let testStateLoop = _testStateLoop_311
