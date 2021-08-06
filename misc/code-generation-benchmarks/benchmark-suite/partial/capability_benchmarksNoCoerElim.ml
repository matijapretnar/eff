open OcamlHeader

type (_, _) eff_internal_effect += TripleFlip : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect +=
  | TripleFail : (unit, empty) eff_internal_effect

type triple_int_list =
  | TripleCons of ((int * int * int) * triple_int_list)
  | TripleNil

let rec _op_42 (* @ *) _x_49 =
  coer_arrow coer_refl_ty coer_refl_ty (fun (_ys_51 : triple_int_list) ->
      match _x_49 with
      | TripleNil -> _ys_51
      | TripleCons (_x_53, _xs_52) ->
          TripleCons
            (coer_tuple_2
               (coer_refl_ty, coer_refl_ty)
               ( _x_53,
                 coer_arrow coer_refl_ty coer_refl_ty
                   (_op_42 (* @ *) _xs_52)
                   _ys_51 )))

let _op_42 (* @ *) = _op_42 (* @ *)

let _testTriple_56 (_n_57 : int) (_s_58 : int) =
  let rec _choice_266 _x_267 =
    coer_computation coer_refl_ty
      (coer_return coer_refl_ty
         (coer_arrow coer_refl_ty coer_refl_ty (( < ) _x_267)))
    >>= fun _b_269 ->
    coer_computation coer_refl_ty (coer_return coer_refl_ty (_b_269 1))
    >>= fun _b_270 ->
    coer_computation coer_refl_ty
      (coer_computation coer_refl_ty
         (if _b_270 then
          Call
            ( TripleFail,
              (),
              fun (_y_271 : empty) ->
                coer_computation coer_refl_ty
                  (coer_return coer_refl_ty
                     (match _y_271 with _ -> assert false)) )
         else
           Call
             ( TripleFlip,
               (),
               fun (_y_272 : bool) ->
                 coer_computation coer_refl_ty
                   (coer_computation coer_refl_ty
                      (if _y_272 then coer_return coer_refl_ty _x_267
                      else
                        coer_computation coer_refl_ty
                          (coer_return coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty
                                (( - ) _x_267)))
                        >>= fun _b_273 ->
                        coer_computation coer_refl_ty
                          (coer_return coer_refl_ty (_b_273 1))
                        >>= fun _b_274 ->
                        coer_computation coer_refl_ty
                          (coer_computation coer_refl_ty
                             (coer_computation coer_refl_ty (_choice_266 _b_274)))))
             )))
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_290 : int * int * int) ->
              Value
                (TripleCons
                   (coer_tuple_2
                      ( coer_tuple_3 (coer_refl_ty, coer_refl_ty, coer_refl_ty),
                        coer_refl_ty )
                      ( coer_tuple_3
                          (coer_refl_ty, coer_refl_ty, coer_refl_ty)
                          _x_290,
                        TripleNil ))));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | TripleFail -> fun _ _l_291 -> Value TripleNil
              | TripleFlip ->
                  fun () _l_292 ->
                    Value
                      (coer_arrow coer_refl_ty coer_refl_ty
                         (_op_42 (* @ *)
                            (coer_arrow coer_refl_ty force_unsafe _l_292 true))
                         (coer_arrow coer_refl_ty force_unsafe _l_292 false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (coer_arrow coer_refl_ty
          (coer_computation coer_refl_ty)
          (coer_arrow coer_refl_ty
             (coer_computation
                (coer_tuple_3 (coer_refl_ty, coer_refl_ty, coer_refl_ty)))
             (fun (_s_275 : int) ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty (_choice_266 _n_57))
               >>= fun _i_276 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_return coer_refl_ty
                       (coer_arrow coer_refl_ty coer_refl_ty (( - ) _i_276))))
               >>= fun _b_277 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_return coer_refl_ty (_b_277 1)))
               >>= fun _b_278 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_computation coer_refl_ty (_choice_266 _b_278))))
               >>= fun _j_279 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty
                          (coer_arrow coer_refl_ty coer_refl_ty (( - ) _j_279)))))
               >>= fun _b_280 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty (_b_280 1))))
               >>= fun _b_281 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_computation coer_refl_ty
                          (coer_computation coer_refl_ty (_choice_266 _b_281)))))
               >>= fun _k_282 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty
                          (coer_arrow coer_refl_ty coer_refl_ty (( + ) _i_276)))))
               >>= fun _b_283 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty (_b_283 _j_279))))
               >>= fun _b_284 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty
                          (coer_arrow coer_refl_ty coer_refl_ty (( + ) _b_284)))))
               >>= fun _b_285 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty (_b_285 _k_282))))
               >>= fun _b_286 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty
                          (coer_arrow coer_refl_ty coer_refl_ty (( = ) _b_286)))))
               >>= fun _b_287 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_return coer_refl_ty (_b_287 _s_275))))
               >>= fun _b_288 ->
               coer_computation coer_refl_ty
                 (coer_computation coer_refl_ty
                    (coer_computation coer_refl_ty
                       (coer_computation coer_refl_ty
                          (if _b_288 then
                           coer_return
                             (coer_tuple_3
                                (coer_refl_ty, coer_refl_ty, coer_refl_ty))
                             (_i_276, _j_279, _k_282)
                          else
                            Call
                              ( TripleFail,
                                (),
                                fun (_y_289 : empty) ->
                                  coer_computation
                                    (coer_tuple_3
                                       (coer_refl_ty, coer_refl_ty, coer_refl_ty))
                                    (coer_return coer_refl_ty
                                       (coer_tuple_3
                                          ( coer_refl_ty,
                                            coer_refl_ty,
                                            coer_refl_ty )
                                          (match _y_289 with
                                          | _ -> assert false))) )))))))
          _s_58))

let testTriple = _testTriple_56

let _handleTripleWrap_297 ((_x_298, _y_299) : int * int) =
  coer_arrow coer_refl_ty coer_refl_ty (_testTriple_56 _x_298) _y_299

let handleTripleWrap = _handleTripleWrap_297

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_301 _x_310 =
  let _p_302 = coer_arrow coer_refl_ty coer_refl_ty _x_310 in
  coer_arrow coer_refl_ty coer_refl_ty (fun (_x_303 : intlist) ->
      match _x_303 with
      | End -> End
      | Lst (_x_304, _xs_305) ->
          if _p_302 _x_304 then
            Lst
              (coer_tuple_2
                 (coer_refl_ty, coer_refl_ty)
                 ( _x_304,
                   coer_arrow coer_refl_ty coer_refl_ty
                     (_filter_301 (coer_arrow coer_refl_ty coer_refl_ty _p_302))
                     _xs_305 ))
          else
            coer_arrow coer_refl_ty coer_refl_ty
              (_filter_301 (coer_arrow coer_refl_ty coer_refl_ty _p_302))
              _xs_305)

let filter = _filter_301

let rec _forall_311 _x_318 =
  let _p_312 = coer_arrow coer_refl_ty coer_refl_ty _x_318 in
  coer_arrow coer_refl_ty coer_refl_ty (fun (_x_313 : queen_list) ->
      match _x_313 with
      | Nil -> true
      | Cons (_x_314, _xs_315) ->
          _p_312 (coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_314)
          && coer_arrow coer_refl_ty coer_refl_ty
               (_forall_311
                  (coer_arrow
                     (coer_tuple_2 (coer_refl_ty, coer_refl_ty))
                     coer_refl_ty _p_312))
               _xs_315)

let forall = _forall_311

let _no_attack_319 ((_x_320, _y_321) : int * int)
    ((_x'_322, _y'_323) : int * int) =
  coer_arrow coer_refl_ty coer_refl_ty (( <> ) _x_320) _x'_322
  && coer_arrow coer_refl_ty coer_refl_ty (( <> ) _y_321) _y'_323
  && coer_arrow coer_refl_ty coer_refl_ty
       (( <> )
          (abs (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_320) _x'_322)))
       (abs (coer_arrow coer_refl_ty coer_refl_ty (( - ) _y_321) _y'_323))

let no_attack = _no_attack_319

let _available_335 (_x_336 : int) (_qs_337 : queen_list) (_l_338 : intlist) =
  coer_arrow coer_refl_ty coer_refl_ty
    (_filter_301
       (coer_arrow coer_refl_ty coer_refl_ty (fun (_y_340 : int) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_forall_311
                 (coer_arrow
                    (coer_tuple_2 (coer_refl_ty, coer_refl_ty))
                    coer_refl_ty
                    (coer_arrow coer_refl_ty coer_refl_ty
                       (_no_attack_319
                          (coer_tuple_2
                             (coer_refl_ty, coer_refl_ty)
                             (_x_336, _y_340))))))
              _qs_337)))
    _l_338

let available = _available_335

let _find_solution_343 (_n_344 : int) =
  let rec _init_358 _x_383 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_acc_360 : intlist) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_383) 0 then _acc_360
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_init_358 (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_383) 1))
            (Lst (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_383, _acc_360))))
  in
  let rec _place_1430 (_x_1432, _k_1431) =
    let _x_1434, _qs_1433 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_1432 in
    if
      coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_1434)
        (coer_arrow coer_refl_ty coer_refl_ty (( + ) _n_344) 1)
    then _k_1431 (Some _qs_1433)
    else
      let rec _loop_1442 _x_1443 =
        let _k_1444 = coer_arrow coer_refl_ty coer_refl_ty _x_1443 in
        coer_arrow coer_refl_ty coer_refl_ty (fun (_x_1445 : intlist) ->
            match _x_1445 with
            | End -> None
            | Lst (_x_1447, _xs_1446) -> (
                match _k_1444 _x_1447 with
                | None ->
                    coer_arrow coer_refl_ty coer_refl_ty
                      (_loop_1442
                         (coer_arrow coer_refl_ty coer_refl_ty _k_1444))
                      _xs_1446
                | Some _x_1450 -> Some _x_1450))
      in
      coer_arrow coer_refl_ty coer_refl_ty
        (_loop_1442
           (coer_arrow coer_refl_ty coer_refl_ty
              (coer_arrow coer_refl_ty coer_refl_ty (fun (_y_1452 : int) ->
                   _place_1430
                     ( coer_tuple_2
                         (coer_refl_ty, coer_refl_ty)
                         ( coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_1434) 1,
                           Cons
                             (coer_tuple_2
                                ( coer_tuple_2 (coer_refl_ty, coer_refl_ty),
                                  coer_refl_ty )
                                ((_x_1434, _y_1452), _qs_1433)) ),
                       fun (_x_1455 : option) -> _k_1431 _x_1455 )))))
        (coer_arrow coer_refl_ty coer_refl_ty
           (coer_arrow coer_refl_ty
              (coer_arrow coer_refl_ty coer_refl_ty)
              (_available_335 _x_1434) _qs_1433)
           (coer_arrow coer_refl_ty coer_refl_ty (_init_358 _n_344) End))
  in
  _place_1430 ((1, Nil), fun (_x_1456 : option) -> _x_1456)

let find_solution = _find_solution_343

let _queens_all_1457 (_number_of_queens_1458 : int) =
  _find_solution_343 _number_of_queens_1458

let queens_all = _queens_all_1457

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_1459 _x_1469 =
  Call
    ( CountGet,
      (),
      fun (_y_1473 : int) ->
        coer_computation coer_refl_ty
          ( coer_computation coer_refl_ty
              (coer_return coer_refl_ty
                 (coer_arrow coer_refl_ty coer_refl_ty (( = ) _y_1473)))
          >>= fun _b_1462 ->
            coer_computation coer_refl_ty (coer_return coer_refl_ty (_b_1462 0))
            >>= fun _b_1461 ->
            coer_computation coer_refl_ty
              (coer_computation coer_refl_ty
                 (if _b_1461 then coer_return coer_refl_ty _y_1473
                 else
                   coer_computation coer_refl_ty
                     (coer_computation coer_refl_ty
                        (coer_return coer_refl_ty
                           (coer_arrow coer_refl_ty coer_refl_ty (( - ) _y_1473))))
                   >>= fun _b_1464 ->
                   coer_computation coer_refl_ty
                     (coer_computation coer_refl_ty
                        (coer_return coer_refl_ty (_b_1464 1)))
                   >>= fun _b_1463 ->
                   Call
                     ( CountPut,
                       _b_1463,
                       fun (_y_1471 : unit) ->
                         coer_computation coer_refl_ty
                           (coer_computation coer_refl_ty
                              (coer_computation coer_refl_ty (_count_1459 ())))
                     ))) ) )

let count = _count_1459

let _testCount_1474 (_m_1475 : int) =
  coer_arrow coer_refl_ty coer_refl_ty
    (coer_arrow coer_refl_ty coer_refl_ty
       (let rec _count_1506 (_x_1469, _k_1508) =
          coer_arrow coer_refl_ty coer_refl_ty (fun (_s_1634 : int) ->
              coer_arrow coer_refl_ty coer_refl_ty
                (coer_arrow coer_refl_ty coer_refl_ty
                   (if coer_arrow coer_refl_ty coer_refl_ty (( = ) _s_1634) 0
                   then _k_1508 _s_1634
                   else
                     coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) ->
                         coer_arrow coer_refl_ty coer_refl_ty
                           (coer_arrow coer_refl_ty coer_refl_ty
                              (_count_1506
                                 ((), fun (_x_1643 : int) -> _k_1508 _x_1643)))
                           (coer_arrow coer_refl_ty coer_refl_ty (( - ) _s_1634)
                              1))))
                _s_1634)
        in
        _count_1506
          ( (),
            fun (_x_1648 : int) ->
              coer_arrow coer_refl_ty coer_refl_ty (fun (_x_1485 : int) ->
                  _x_1485) )))
    _m_1475

let testCount = _testCount_1474

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_1649 (_n_1650 : int) =
  coer_arrow coer_refl_ty coer_refl_ty
    (let rec _generateFromTo_1874 ((_x_1679, _k_1724), _k_1876) =
       let _l_1652, _u_1653 =
         coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_1679
       in
       if coer_arrow coer_refl_ty coer_refl_ty (( > ) _l_1652) _u_1653 then
         force_unsafe
           ((handler
               {
                 value_clause =
                   (fun (_x_2069 : unit) -> Value (_k_1876 _x_2069));
                 effect_clauses =
                   (fun (type a b) (eff : (a, b) eff_internal_effect) :
                        (a -> (b -> _) -> _) ->
                     match eff with
                     | GeneratorPut ->
                         fun _s'_2070 _l_2071 ->
                           Value
                             (coer_arrow coer_refl_ty coer_refl_ty
                                (fun (_s_2072 : int) ->
                                  coer_arrow coer_refl_ty coer_refl_ty
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (coer_arrow coer_refl_ty force_unsafe
                                          _l_2071 ()))
                                    _s'_2070))
                     | GeneratorGet ->
                         fun _ _l_2074 ->
                           Value
                             (coer_arrow coer_refl_ty coer_refl_ty
                                (fun (_s_2075 : int) ->
                                  coer_arrow coer_refl_ty coer_refl_ty
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (coer_arrow coer_refl_ty force_unsafe
                                          _l_2074 _s_2075))
                                    _s_2075))
                     | eff' -> fun arg k -> Call (eff', arg, k));
               })
              (_k_1724 ()))
       else
         coer_arrow coer_refl_ty coer_refl_ty (fun (_s_2077 : int) ->
             coer_arrow coer_refl_ty coer_refl_ty
               (coer_arrow coer_refl_ty coer_refl_ty
                  (coer_arrow coer_refl_ty coer_refl_ty (fun (_s_2080 : int) ->
                       coer_arrow coer_refl_ty coer_refl_ty
                         (coer_arrow coer_refl_ty coer_refl_ty
                            (_generateFromTo_1874
                               ( ( coer_tuple_2
                                     (coer_refl_ty, coer_refl_ty)
                                     ( coer_arrow coer_refl_ty coer_refl_ty
                                         (( + ) _l_1652) 1,
                                       _u_1653 ),
                                   fun (_x_2084 : unit) -> _k_1724 _x_2084 ),
                                 fun (_x_2085 : unit) -> _k_1876 _x_2085 )))
                         (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_2077)
                            _l_1652))))
               _s_2077)
     in
     _generateFromTo_1874
       ( ( coer_tuple_2 (coer_refl_ty, coer_refl_ty) (1, _n_1650),
           fun (_x_1695 : unit) -> coer_return coer_refl_ty _x_1695 ),
         fun (_x_1704 : unit) ->
           coer_arrow coer_refl_ty coer_refl_ty (fun (_s_1668 : int) -> _s_1668)
       ))
    0

let testGenerator = _testGenerator_1649
