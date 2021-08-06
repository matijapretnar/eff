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
  let rec _choice_195 _x_196 =
    if _x_196 < 1 then
      Call (TripleFail, (), fun (_y_199 : empty) -> Value _y_199)
      >>= fun _b_198 -> Value (match _b_198 with _ -> assert false)
    else
      Call (TripleFlip, (), fun (_y_203 : bool) -> Value _y_203)
      >>= fun _b_200 -> if _b_200 then Value _x_196 else _choice_195 (_x_196 - 1)
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_r_206 : int * int * int) ->
              Value (TripleCons (_r_206, TripleNil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | TripleFail -> fun _ _l_207 -> Value TripleNil
              | TripleFlip ->
                  fun () _l_208 ->
                    Value
                      (_op_42 (* @ *)
                         (coer_arrow coer_refl_ty force_unsafe _l_208 true)
                         (coer_arrow coer_refl_ty force_unsafe _l_208 false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ( _choice_195 _n_57 >>= fun _i_213 ->
         _choice_195 (_i_213 - 1) >>= fun _j_214 ->
         _choice_195 (_j_214 - 1) >>= fun _k_215 ->
         if _i_213 + _j_214 + _k_215 = _s_58 then Value (_i_213, _j_214, _k_215)
         else
           Call (TripleFail, (), fun (_y_218 : empty) -> Value _y_218)
           >>= fun _b_217 -> Value (match _b_217 with _ -> assert false) ))

let testTriple = _testTriple_56

let _handleTripleWrap_229 ((_x_230, _y_231) : int * int) =
  _testTriple_56 _x_230 _y_231

let handleTripleWrap = _handleTripleWrap_229

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_233 _x_242 (_x_244 : intlist) =
  match _x_244 with
  | End -> End
  | Lst (_x_246, _xs_245) ->
      if _x_242 _x_246 then Lst (_x_246, _filter_233 _x_242 _xs_245)
      else _filter_233 _x_242 _xs_245

let filter = _filter_233

let rec _forall_251 _x_258 (_x_260 : queen_list) =
  match _x_260 with
  | Nil -> true
  | Cons (_x_262, _xs_261) -> _x_258 _x_262 && _forall_251 _x_258 _xs_261

let forall = _forall_251

let _no_attack_265 ((_x_266, _y_267) : int * int)
    ((_x'_268, _y'_269) : int * int) =
  _x_266 <> _x'_268 && _y_267 <> _y'_269
  && abs (_x_266 - _x'_268) <> abs (_y_267 - _y'_269)

let no_attack = _no_attack_265

let _available_281 (_x_282 : int) (_qs_283 : queen_list) (_l_284 : intlist) =
  _filter_233
    (fun (_y_286 : int) ->
      _forall_251 (_no_attack_265 (_x_282, _y_286)) _qs_283)
    _l_284

let available = _available_281

let _find_solution_289 (_n_290 : int) =
  let rec _init_304 _x_329 (_acc_349 : intlist) =
    if _x_329 = 0 then _acc_349
    else _init_304 (_x_329 - 1) (Lst (_x_329, _acc_349))
  in
  let rec _place_448 (_x_450, _qs_449) =
    if _x_450 = _n_290 + 1 then Some _qs_449
    else
      let rec _loop_458 _x_459 (_x_460 : intlist) =
        match _x_460 with
        | End -> None
        | Lst (_x_462, _xs_461) -> (
            match _x_459 _x_462 with
            | None -> _loop_458 _x_459 _xs_461
            | Some _x_465 -> Some _x_465)
      in
      _loop_458
        (fun (_y_467 : int) ->
          _place_448 (_x_450 + 1, Cons ((_x_450, _y_467), _qs_449)))
        (_available_281 _x_450 _qs_449 (_init_304 _n_290 End))
  in
  _place_448 (1, Nil)

let find_solution = _find_solution_289

let _queens_all_470 (_number_of_queens_471 : int) =
  _find_solution_289 _number_of_queens_471

let queens_all = _queens_all_470

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_472 _x_482 =
  Call (CountGet, (), fun (_y_486 : int) -> Value _y_486) >>= fun _i_473 ->
  if _i_473 = 0 then Value _i_473
  else
    Call (CountPut, _i_473 - 1, fun (_y_484 : unit) -> Value _y_484)
    >>= fun _ -> _count_472 ()

let count = _count_472

let _testCount_487 (_m_488 : int) =
  let rec _count_505 _x_482 (_s_554 : int) =
    if _s_554 = 0 then _s_554 else _count_505 () (_s_554 - 1)
  in
  _count_505 () _m_488

let testCount = _testCount_487

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_563 (_n_564 : int) =
  let rec _generateFromTo_565 (_l_566, _u_567) =
    if _l_566 > _u_567 then Value ()
    else
      Call (GeneratorYield, _l_566, fun (_y_606 : unit) -> Value _y_606)
      >>= fun _ -> _generateFromTo_565 (_l_566 + 1, _u_567)
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_580 : unit) -> Value (fun (_s_582 : int) -> _s_582));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | GeneratorPut ->
                  fun _s'_573 _l_594 ->
                    Value
                      (fun (_s_575 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_594 () _s'_573)
              | GeneratorGet ->
                  fun _ _l_595 ->
                    Value
                      (fun (_s_578 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_595 _s_578
                          _s_578)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ((handler
           {
             value_clause = (fun (_id_589 : unit) -> Value _id_589);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | GeneratorYield ->
                     fun _e_584 _l_600 ->
                       ( ( ( Call
                               ( GeneratorGet,
                                 (),
                                 fun (_y_604 : int) -> Value _y_604 )
                           >>= fun _b_588 -> Value (( + ) _b_588) )
                         >>= fun _b_587 -> Value (_b_587 _e_584) )
                       >>= fun _b_586 ->
                         Call
                           ( GeneratorPut,
                             _b_586,
                             fun (_y_602 : unit) -> Value _y_602 ) )
                       >>= fun _ -> _l_600 ()
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_generateFromTo_565 (1, _n_564))))
    0

let testGenerator = _testGenerator_563
