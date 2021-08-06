open OcamlHeader

type (_, _) eff_internal_effect += TripleFlip : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect +=
  | TripleFail : (unit, empty) eff_internal_effect

type triple_int_list =
  | TripleCons of ((int * int * int) * triple_int_list)
  | TripleNil

let rec _op_42 (* @ *) _x_49 (_ys_51 : triple_int_list) =
  match _x_49 with
  | TripleNil -> _ys_51
  | TripleCons (_x_53, _xs_52) ->
      TripleCons (_x_53, _op_42 (* @ *) _xs_52 _ys_51)

let _op_42 (* @ *) = _op_42 (* @ *)

let _testTriple_56 (_n_57 : int) (_s_58 : int) =
  let rec _choice_198 _x_199 =
    if _x_199 < 1 then
      Call
        ( TripleFail,
          (),
          fun (_y_202 : empty) -> Value (match _y_202 with _ -> assert false) )
    else
      Call
        ( TripleFlip,
          (),
          fun (_y_203 : bool) ->
            if _y_203 then Value _x_199 else _choice_198 (_x_199 - 1) )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_221 : triple_int_list) -> Value _id_221);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | TripleFail -> fun _ _l_222 -> Value TripleNil
              | TripleFlip ->
                  fun () _l_223 ->
                    Value
                      (_op_42 (* @ *)
                         (coer_arrow coer_refl_ty force_unsafe _l_223 true)
                         (coer_arrow coer_refl_ty force_unsafe _l_223 false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ( _choice_198 _n_57 >>= fun _i_206 ->
         _choice_198 (_i_206 - 1) >>= fun _j_209 ->
         _choice_198 (_j_209 - 1) >>= fun _k_212 ->
         (if _i_206 + _j_209 + _k_212 = _s_58 then Value (_i_206, _j_209, _k_212)
         else
           Call
             ( TripleFail,
               (),
               fun (_y_220 : empty) ->
                 Value (match _y_220 with _ -> assert false) ))
         >>= fun _r_219 -> Value (TripleCons (_r_219, TripleNil)) ))

let testTriple = _testTriple_56

let _handleTripleWrap_228 ((_x_229, _y_230) : int * int) =
  _testTriple_56 _x_229 _y_230

let handleTripleWrap = _handleTripleWrap_228

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_232 _x_241 (_x_243 : intlist) =
  match _x_243 with
  | End -> End
  | Lst (_x_245, _xs_244) ->
      if _x_241 _x_245 then Lst (_x_245, _filter_232 _x_241 _xs_244)
      else _filter_232 _x_241 _xs_244

let filter = _filter_232

let rec _forall_250 _x_257 (_x_259 : queen_list) =
  match _x_259 with
  | Nil -> true
  | Cons (_x_261, _xs_260) -> _x_257 _x_261 && _forall_250 _x_257 _xs_260

let forall = _forall_250

let _no_attack_264 ((_x_265, _y_266) : int * int)
    ((_x'_267, _y'_268) : int * int) =
  _x_265 <> _x'_267 && _y_266 <> _y'_268
  && abs (_x_265 - _x'_267) <> abs (_y_266 - _y'_268)

let no_attack = _no_attack_264

let _available_280 (_x_281 : int) (_qs_282 : queen_list) (_l_283 : intlist) =
  _filter_232
    (fun (_y_285 : int) ->
      _forall_250 (_no_attack_264 (_x_281, _y_285)) _qs_282)
    _l_283

let available = _available_280

let _find_solution_288 (_n_289 : int) =
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_301 : option) -> Value _id_301);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Select ->
                  fun _lst_290 _l_327 ->
                    Value
                      (let rec _loop_292 _x_326 (_x_357 : intlist) =
                         match _x_357 with
                         | End -> None
                         | Lst (_x_359, _xs_358) -> (
                             match _x_326 _x_359 with
                             | None -> _loop_292 _x_326 _xs_358
                             | Some _x_362 -> Some _x_362)
                       in
                       _loop_292
                         (coer_arrow coer_refl_ty force_unsafe _l_327)
                         _lst_290)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (let rec _init_303 _x_328 (_acc_350 : intlist) =
          if _x_328 = 0 then _acc_350
          else _init_303 (_x_328 - 1) (Lst (_x_328, _acc_350))
        in
        let ____l_311 = _init_303 _n_289 End in
        let rec _place_313 (_x_314, _qs_315) =
          if _x_314 = _n_289 + 1 then Value (Some _qs_315)
          else
            Call
              ( Select,
                _available_280 _x_314 _qs_315 ____l_311,
                fun (_y_333 : int) ->
                  _place_313 (_x_314 + 1, Cons ((_x_314, _y_333), _qs_315)) )
        in
        _place_313 (1, Nil)))

let find_solution = _find_solution_288

let _queens_all_363 (_number_of_queens_364 : int) =
  _find_solution_288 _number_of_queens_364

let queens_all = _queens_all_363

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_365 _x_375 =
  Call
    ( CountGet,
      (),
      fun (_y_379 : int) ->
        if _y_379 = 0 then Value _y_379
        else Call (CountPut, _y_379 - 1, fun (_y_377 : unit) -> _count_365 ())
    )

let count = _count_365

let _testCount_380 (_m_381 : int) =
  let rec _count_398 _x_375 =
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x_389 : int) -> Value (fun (_x_391 : int) -> _x_391));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | CountGet ->
                    fun () _l_394 ->
                      Value
                        (fun (_s_384 : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_394 _s_384
                            _s_384)
                | CountPut ->
                    fun _s_386 _l_395 ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_395 () _s_386)
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (Call
            ( CountGet,
              (),
              fun (_y_379 : int) ->
                if _y_379 = 0 then Value _y_379
                else
                  Call
                    (CountPut, _y_379 - 1, fun (_y_404 : unit) -> _count_365 ())
            )))
  in
  _count_398 () _m_381

let testCount = _testCount_380

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_405 (_n_406 : int) =
  let rec _generateFromTo_407 (_l_408, _u_409) =
    if _l_408 > _u_409 then Value ()
    else
      Call
        ( GeneratorYield,
          _l_408,
          fun (_y_449 : unit) -> _generateFromTo_407 (_l_408 + 1, _u_409) )
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_422 : unit) -> Value (fun (_s_424 : int) -> _s_424));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | GeneratorPut ->
                  fun _s'_415 _l_436 ->
                    Value
                      (fun (_s_417 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_436 () _s'_415)
              | GeneratorGet ->
                  fun _ _l_437 ->
                    Value
                      (fun (_s_420 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_437 _s_420
                          _s_420)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ((handler
           {
             value_clause = (fun (_id_431 : unit) -> Value _id_431);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | GeneratorYield ->
                     fun _e_426 _l_442 ->
                       Call
                         ( GeneratorGet,
                           (),
                           fun (_y_446 : int) ->
                             Call
                               ( GeneratorPut,
                                 _y_446 + _e_426,
                                 fun (_y_444 : unit) -> _l_442 () ) )
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_generateFromTo_407 (1, _n_406))))
    0

let testGenerator = _testGenerator_405
