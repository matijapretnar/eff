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
  let rec _init_450 _x_475 (_acc_497 : intlist) =
    if _x_475 = 0 then _acc_497
    else _init_450 (_x_475 - 1) (Lst (_x_475, _acc_497))
  in
  let _l_458 = _init_450 _n_436 End in
  let rec _place_460 (_x_461, _qs_462) =
    if _x_461 = _n_436 + 1 then Value (Some _qs_462)
    else
      Call
        ( Select,
          _available_427 _x_461 _qs_462 _l_458,
          fun (_y_480 : int) ->
            _place_460 (_x_461 + 1, Cons ((_x_461, _y_480), _qs_462)) )
  in
  let rec _place_510 (_x_461, _qs_462) =
    if _x_461 = _n_436 + 1 then Some _qs_462
    else
      let rec _loop_523 _x_524 (_x_525 : intlist) =
        match _x_525 with
        | End -> None
        | Lst (_x_527, _xs_526) -> (
            match _x_524 _x_527 with
            | None -> _loop_523 _x_524 _xs_526
            | Some _x_530 -> Some _x_530)
      in
      _loop_523
        (fun (_y_532 : int) ->
          _place_510 (_x_461 + 1, Cons ((_x_461, _y_532), _qs_462)))
        (_available_427 _x_461 _qs_462 _l_458)
  in
  _place_510 (1, Nil)

let find_solution = _find_solution_435

let _queens_all_535 (_number_of_queens_536 : int) =
  _find_solution_435 _number_of_queens_536

let queens_all = _queens_all_535

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_537 _x_547 =
  Call
    ( CountGet,
      (),
      fun (_y_551 : int) ->
        if _y_551 = 0 then Value _y_551
        else Call (CountPut, _y_551 - 1, fun (_y_549 : unit) -> _count_537 ())
    )

let count = _count_537

let _testCount_552 (_m_553 : int) =
  (let rec _count_570 _x_547 (_s_583 : int) =
     (if _s_583 = 0 then fun (_x_588 : int) -> _x_588
     else fun (_ : int) -> _count_570 () (_s_583 - 1))
       _s_583
   in
   _count_570 ())
    _m_553

let testCount = _testCount_552

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_592 (_n_593 : int) =
  let rec _generateFromTo_594 (_l_595, _u_596) =
    if _l_595 > _u_596 then Value ()
    else
      Call
        ( GeneratorYield,
          _l_595,
          fun (_y_638 : unit) -> _generateFromTo_594 (_l_595 + 1, _u_596) )
  in
  (let rec _generateFromTo_646 (_l_595, _u_596) =
     if _l_595 > _u_596 then Value ()
     else
       Call
         ( GeneratorGet,
           (),
           fun (_y_654 : int) ->
             Call
               ( GeneratorPut,
                 _y_654 + _l_595,
                 fun (_y_657 : unit) -> _generateFromTo_646 (_l_595 + 1, _u_596)
               ) )
   in
   let rec _generateFromTo_660 (_l_595, _u_596) (_x_0 : int) =
     if _l_595 > _u_596 then (_x_0, ())
     else _generateFromTo_660 (_l_595 + 1, _u_596) (_x_0 + _l_595)
   in
   _generateFromTo_660 (1, _n_593))
    0

let testGenerator = _testGenerator_592
