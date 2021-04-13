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
  let rec _choice_244 _x_245 =
    if _x_245 < 1 then TripleNil
    else
      let _l_248 (_y_252 : bool) =
        if _y_252 then
          let rec _choice_255 _x_256 =
            if _x_256 < 1 then TripleNil
            else
              let _l_259 (_y_263 : bool) =
                if _y_263 then
                  let rec _choice_266 _x_267 =
                    if _x_267 < 1 then TripleNil
                    else
                      let _l_270 (_y_274 : bool) =
                        if _y_274 then
                          if _x_245 + _x_256 + _x_267 = _s_58 then
                            TripleCons ((_x_245, _x_256, _x_267), TripleNil)
                          else TripleNil
                        else _choice_266 (_x_267 - 1)
                      in
                      _op_42 (* @ *) (_l_270 true) (_l_270 false)
                  in
                  _choice_266 (_x_256 - 1)
                else _choice_255 (_x_256 - 1)
              in
              _op_42 (* @ *) (_l_259 true) (_l_259 false)
          in
          _choice_255 (_x_245 - 1)
        else _choice_244 (_x_245 - 1)
      in
      _op_42 (* @ *) (_l_248 true) (_l_248 false)
  in
  _choice_244 _n_57

let testTriple = _testTriple_56

let _handleTripleWrap_288 ((_x_289, _y_290) : int * int) =
  _testTriple_56 _x_289 _y_290

let handleTripleWrap = _handleTripleWrap_288

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_292 _x_301 (_x_303 : intlist) =
  match _x_303 with
  | End -> End
  | Lst (_x_305, _xs_304) ->
      if _x_301 _x_305 then Lst (_x_305, _filter_292 _x_301 _xs_304)
      else _filter_292 _x_301 _xs_304

let filter = _filter_292

let rec _forall_310 _x_317 (_x_319 : queen_list) =
  match _x_319 with
  | Nil -> true
  | Cons (_x_321, _xs_320) -> _x_317 _x_321 && _forall_310 _x_317 _xs_320

let forall = _forall_310

let _no_attack_324 ((_x_325, _y_326) : int * int)
    ((_x'_327, _y'_328) : int * int) =
  _x_325 <> _x'_327 && _y_326 <> _y'_328
  && abs (_x_325 - _x'_327) <> abs (_y_326 - _y'_328)

let no_attack = _no_attack_324

let _available_340 (_x_341 : int) (_qs_342 : queen_list) (_l_343 : intlist) =
  _filter_292
    (fun (_y_345 : int) ->
      _forall_310 (_no_attack_324 (_x_341, _y_345)) _qs_342)
    _l_343

let available = _available_340

let _find_solution_348 (_n_349 : int) =
  let rec _init_363 _x_388 (_acc_410 : intlist) =
    if _x_388 = 0 then _acc_410
    else _init_363 (_x_388 - 1) (Lst (_x_388, _acc_410))
  in
  let ____l_371 = _init_363 _n_349 End in
  let rec _place_423 (_x_374, _qs_375) =
    if _x_374 = _n_349 + 1 then Some _qs_375
    else
      let rec _loop_436 _x_437 (_x_438 : intlist) =
        match _x_438 with
        | End -> None
        | Lst (_x_440, _xs_439) -> (
            match _x_437 _x_440 with
            | None -> _loop_436 _x_437 _xs_439
            | Some _x_443 -> Some _x_443)
      in
      _loop_436
        (fun (_y_445 : int) ->
          _place_423 (_x_374 + 1, Cons ((_x_374, _y_445), _qs_375)))
        (_available_340 _x_374 _qs_375 ____l_371)
  in
  _place_423 (1, Nil)

let find_solution = _find_solution_348

let _queens_all_448 (_number_of_queens_449 : int) =
  _find_solution_348 _number_of_queens_449

let queens_all = _queens_all_448

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_450 _x_460 =
  Call
    ( CountGet,
      (),
      fun (_y_464 : int) ->
        if _y_464 = 0 then Value _y_464
        else Call (CountPut, _y_464 - 1, fun (_y_462 : unit) -> _count_450 ())
    )

let count = _count_450

let _testCount_465 (_m_466 : int) =
  (let rec _count_483 _x_460 (_s_496 : int) =
     if _s_496 = 0 then _s_496 else _count_483 () (_s_496 - 1)
   in
   _count_483 ())
    _m_466

let testCount = _testCount_465

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_505 (_n_506 : int) =
  (let rec _generateFromTo_571 (_l_508, _u_509) (_x_1 : int) =
     if _l_508 > _u_509 then _x_1
     else _generateFromTo_571 (_l_508 + 1, _u_509) (_x_1 + _l_508)
   in
   _generateFromTo_571 (1, _n_506))
    0

let testGenerator = _testGenerator_505
