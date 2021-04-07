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
  let rec _choice_316 _x_317 =
    if _x_317 < 1 then
      Call
        ( TripleFail,
          (),
          fun (_y_320 : empty) -> Value (match _y_320 with _ -> assert false) )
    else
      Call
        ( TripleFlip,
          (),
          fun (_y_321 : bool) ->
            if _y_321 then Value _x_317 else _choice_316 (_x_317 - 1) )
  in
  let rec _choice_324 _x_325 =
    if _x_325 < 1 then TripleNil
    else
      let _l_328 (_y_332 : bool) =
        if _y_332 then
          let rec _choice_335 _x_336 =
            if _x_336 < 1 then TripleNil
            else
              let _l_339 (_y_343 : bool) =
                if _y_343 then
                  let rec _choice_346 _x_347 =
                    if _x_347 < 1 then TripleNil
                    else
                      let _l_350 (_y_354 : bool) =
                        if _y_354 then
                          force_unsafe
                            ((handler
                                {
                                  value_clause =
                                    (fun (_r_362 : int * int * int) ->
                                      Value (TripleCons (_r_362, TripleNil)));
                                  effect_clauses =
                                    (fun (type a b)
                                         (eff : (a, b) eff_internal_effect) :
                                         (a -> (b -> _) -> _) ->
                                      match eff with
                                      | TripleFail ->
                                          fun _ _l_363 -> Value TripleNil
                                      | TripleFlip ->
                                          fun () _l_364 ->
                                            Value
                                              (_op_42 (* @ *)
                                                 (coer_arrow coer_refl_ty
                                                    force_unsafe _l_364 true)
                                                 (coer_arrow coer_refl_ty
                                                    force_unsafe _l_364 false))
                                      | eff' -> fun arg k -> Call (eff', arg, k));
                                })
                               (if _x_325 + _x_336 + _x_347 = _s_58 then
                                Value (_x_325, _x_336, _x_347)
                               else
                                 Call
                                   ( TripleFail,
                                     (),
                                     fun (_y_361 : empty) ->
                                       Value
                                         (match _y_361 with _ -> assert false)
                                   )))
                        else _choice_346 (_x_347 - 1)
                      in
                      _op_42 (* @ *) (_l_350 true) (_l_350 false)
                  in
                  _choice_346 (_x_336 - 1)
                else _choice_335 (_x_336 - 1)
              in
              _op_42 (* @ *) (_l_339 true) (_l_339 false)
          in
          _choice_335 (_x_325 - 1)
        else _choice_324 (_x_325 - 1)
      in
      _op_42 (* @ *) (_l_328 true) (_l_328 false)
  in
  _choice_324 _n_57

let testTriple = _testTriple_56

let _handleTripleWrap_375 ((_x_376, _y_377) : int * int) =
  _testTriple_56 _x_376 _y_377

let handleTripleWrap = _handleTripleWrap_375

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_379 _x_388 (_x_390 : intlist) =
  match _x_390 with
  | End -> End
  | Lst (_x_392, _xs_391) ->
      if _x_388 _x_392 then Lst (_x_392, _filter_379 _x_388 _xs_391)
      else _filter_379 _x_388 _xs_391

let filter = _filter_379

let rec _forall_397 _x_404 (_x_406 : queen_list) =
  match _x_406 with
  | Nil -> true
  | Cons (_x_408, _xs_407) -> _x_404 _x_408 && _forall_397 _x_404 _xs_407

let forall = _forall_397

let _no_attack_411 ((_x_412, _y_413) : int * int)
    ((_x'_414, _y'_415) : int * int) =
  _x_412 <> _x'_414 && _y_413 <> _y'_415
  && abs (_x_412 - _x'_414) <> abs (_y_413 - _y'_415)

let no_attack = _no_attack_411

let _available_427 (_x_428 : int) (_qs_429 : queen_list) (_l_430 : intlist) =
  _filter_379
    (fun (_y_432 : int) ->
      _forall_397 (_no_attack_411 (_x_428, _y_432)) _qs_429)
    _l_430

let available = _available_427

let _find_solution_435 (_n_436 : int) =
  let rec _init_450 _x_477 (_acc_501 : intlist) =
    if _x_477 = 0 then _acc_501
    else _init_450 (_x_477 - 1) (Lst (_x_477, _acc_501))
  in
  let rec _place_460 _x_480 (_qs_488 : queen_list) =
    if _x_480 = _n_436 + 1 then Value (Some _qs_488)
    else
      Call
        ( Select,
          _available_427 _x_480 _qs_488 (_init_450 _n_436 End),
          fun (_y_496 : int) ->
            _place_460 (_x_480 + 1) (Cons ((_x_480, _y_496), _qs_488)) )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_448 : option) -> Value _id_448);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Select ->
                  fun _lst_437 _l_476 ->
                    Value
                      (let rec _loop_439 _x_475 (_x_508 : intlist) =
                         match _x_508 with
                         | End -> None
                         | Lst (_x_510, _xs_509) -> (
                             match _x_475 _x_510 with
                             | None -> _loop_439 _x_475 _xs_509
                             | Some _x_513 -> Some _x_513)
                       in
                       _loop_439
                         (coer_arrow coer_refl_ty force_unsafe _l_476)
                         _lst_437)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_place_460 1 Nil))

let find_solution = _find_solution_435

let _queens_all_514 (_number_of_queens_515 : int) =
  _find_solution_435 _number_of_queens_515

let queens_all = _queens_all_514

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_516 _x_526 =
  Call
    ( CountGet,
      (),
      fun (_y_530 : int) ->
        if _y_530 = 0 then Value _y_530
        else Call (CountPut, _y_530 - 1, fun (_y_528 : unit) -> _count_516 ())
    )

let count = _count_516

let _testCount_531 (_m_532 : int) =
  (let rec _count_549 _x_526 (_s_562 : int) =
     (if _s_562 = 0 then fun (_x_567 : int) -> _x_567
     else fun (_ : int) -> _count_549 () (_s_562 - 1))
       _s_562
   in
   _count_549 ())
    _m_532

let testCount = _testCount_531

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_571 (_n_572 : int) =
  let rec _generateFromTo_573 (_l_574, _u_575) =
    if _l_574 > _u_575 then Value ()
    else
      Call
        ( GeneratorYield,
          _l_574,
          fun (_y_617 : unit) -> _generateFromTo_573 (_l_574 + 1, _u_575) )
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_588 : unit) ->
              Value (fun (_s_615 : int) -> (_s_615, _x_588)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | GeneratorPut ->
                  fun (_s'_581 : int) _l_602 ->
                    Value
                      (fun (_s_583 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_602 () _s'_581)
              | GeneratorGet ->
                  fun _ _l_603 ->
                    Value
                      (fun (_s_586 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_603 _s_586
                          _s_586)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ((handler
           {
             value_clause = (fun (_id_597 : unit) -> Value _id_597);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | GeneratorYield ->
                     fun _e_592 _l_608 ->
                       Call
                         ( GeneratorGet,
                           (),
                           fun (_y_612 : int) ->
                             Call
                               ( GeneratorPut,
                                 _y_612 + _e_592,
                                 fun (_y_610 : unit) -> _l_608 () ) )
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_generateFromTo_573 (1, _n_572))))
    0

let testGenerator = _testGenerator_571
