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
      TripleCons
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           (_x_53, _op_42 (* @ *) _xs_52 _ys_51))

let _op_42 (* @ *) = _op_42 (* @ *)

let _testTriple_56 (_n_57 : int) (_s_58 : int) =
  let rec _choice_194 _x_195 =
    coer_return coer_refl_ty (( < ) _x_195) >>= fun _b_197 ->
    coer_return coer_refl_ty (_b_197 1) >>= fun _b_198 ->
    if _b_198 then
      Call
        ( TripleFail,
          (),
          fun (_y_199 : empty) ->
            coer_computation coer_refl_ty
              (coer_return coer_refl_ty (match _y_199 with _ -> assert false))
        )
    else
      Call
        ( TripleFlip,
          (),
          fun (_y_200 : bool) ->
            if _y_200 then coer_return coer_refl_ty _x_195
            else
              coer_return coer_refl_ty (( - ) _x_195) >>= fun _b_201 ->
              coer_return coer_refl_ty (_b_201 1) >>= fun _b_202 ->
              _choice_194 _b_202 )
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_r_218 : int * int * int) ->
              Value
                (TripleCons
                   (coer_tuple_2
                      ( coer_tuple_3 (coer_refl_ty, coer_refl_ty, coer_refl_ty),
                        coer_refl_ty )
                      (_r_218, TripleNil))));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | TripleFail -> fun _ _l_219 -> Value TripleNil
              | TripleFlip ->
                  fun () _l_220 ->
                    Value
                      (_op_42 (* @ *)
                         (coer_arrow coer_refl_ty force_unsafe _l_220 true)
                         (coer_arrow coer_refl_ty force_unsafe _l_220 false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ( _choice_194 _n_57 >>= fun _i_204 ->
         coer_return coer_refl_ty (( - ) _i_204) >>= fun _b_205 ->
         coer_return coer_refl_ty (_b_205 1) >>= fun _b_206 ->
         _choice_194 _b_206 >>= fun _j_207 ->
         coer_return coer_refl_ty (( - ) _j_207) >>= fun _b_208 ->
         coer_return coer_refl_ty (_b_208 1) >>= fun _b_209 ->
         _choice_194 _b_209 >>= fun _k_210 ->
         coer_computation coer_refl_ty (coer_return coer_refl_ty (( + ) _i_204))
         >>= fun _b_211 ->
         coer_computation coer_refl_ty
           (coer_return coer_refl_ty (_b_211 _j_207))
         >>= fun _b_212 ->
         coer_computation coer_refl_ty (coer_return coer_refl_ty (( + ) _b_212))
         >>= fun _b_213 ->
         coer_computation coer_refl_ty
           (coer_return coer_refl_ty (_b_213 _k_210))
         >>= fun _b_214 ->
         coer_computation coer_refl_ty (coer_return coer_refl_ty (( = ) _b_214))
         >>= fun _b_215 ->
         coer_computation coer_refl_ty (coer_return coer_refl_ty (_b_215 _s_58))
         >>= fun _b_216 ->
         coer_computation coer_refl_ty
           (if _b_216 then
            coer_return
              (coer_tuple_3 (coer_refl_ty, coer_refl_ty, coer_refl_ty))
              (_i_204, _j_207, _k_210)
           else
             Call
               ( TripleFail,
                 (),
                 fun (_y_217 : empty) ->
                   coer_return coer_refl_ty
                     (match _y_217 with _ -> assert false) )) ))

let testTriple = _testTriple_56

let _handleTripleWrap_225 ((_x_226, _y_227) : int * int) =
  _testTriple_56 _x_226 _y_227

let handleTripleWrap = _handleTripleWrap_225

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_229 _x_238 =
  let _p_230 = coer_arrow coer_refl_ty coer_refl_ty _x_238 in
  fun (_x_231 : intlist) ->
    match _x_231 with
    | End -> End
    | Lst (_x_232, _xs_233) ->
        if _p_230 _x_232 then
          Lst
            (coer_tuple_2
               (coer_refl_ty, coer_refl_ty)
               ( _x_232,
                 _filter_229
                   (coer_arrow coer_refl_ty coer_refl_ty _p_230)
                   _xs_233 ))
        else _filter_229 (coer_arrow coer_refl_ty coer_refl_ty _p_230) _xs_233

let filter = _filter_229

let rec _forall_239 _x_246 =
  let _p_240 = coer_arrow coer_refl_ty coer_refl_ty _x_246 in
  fun (_x_241 : queen_list) ->
    match _x_241 with
    | Nil -> true
    | Cons (_x_242, _xs_243) ->
        _p_240 (coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_242)
        && _forall_239
             (coer_arrow
                (coer_tuple_2 (coer_refl_ty, coer_refl_ty))
                coer_refl_ty _p_240)
             _xs_243

let forall = _forall_239

let _no_attack_247 ((_x_248, _y_249) : int * int)
    ((_x'_250, _y'_251) : int * int) =
  _x_248 <> _x'_250 && _y_249 <> _y'_251
  && abs (_x_248 - _x'_250) <> abs (_y_249 - _y'_251)

let no_attack = _no_attack_247

let _available_263 (_x_264 : int) (_qs_265 : queen_list) (_l_266 : intlist) =
  _filter_229
    (coer_arrow coer_refl_ty coer_refl_ty (fun (_y_268 : int) ->
         _forall_239
           (coer_arrow
              (coer_tuple_2 (coer_refl_ty, coer_refl_ty))
              coer_refl_ty
              (_no_attack_247
                 (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_264, _y_268))))
           _qs_265))
    _l_266

let available = _available_263

let _find_solution_271 (_n_272 : int) =
  let rec _init_286 _x_311 (_acc_288 : intlist) =
    if _x_311 = 0 then _acc_288
    else
      _init_286 (_x_311 - 1)
        (Lst (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_311, _acc_288)))
  in
  let rec _place_502 _x_503 =
    let _x_505, _qs_504 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_503 in
    if _x_505 = _n_272 + 1 then Some _qs_504
    else
      let rec _loop_513 _x_514 =
        let _k_515 = coer_arrow coer_refl_ty coer_refl_ty _x_514 in
        fun (_x_516 : intlist) ->
          match _x_516 with
          | End -> None
          | Lst (_x_518, _xs_517) -> (
              match _k_515 _x_518 with
              | None ->
                  _loop_513
                    (coer_arrow coer_refl_ty coer_refl_ty _k_515)
                    _xs_517
              | Some _x_521 -> Some _x_521)
      in
      _loop_513
        (coer_arrow coer_refl_ty coer_refl_ty
           (coer_arrow coer_refl_ty coer_refl_ty (fun (_y_523 : int) ->
                _place_502
                  (coer_tuple_2
                     (coer_refl_ty, coer_refl_ty)
                     ( _x_505 + 1,
                       Cons
                         (coer_tuple_2
                            ( coer_tuple_2 (coer_refl_ty, coer_refl_ty),
                              coer_refl_ty )
                            ((_x_505, _y_523), _qs_504)) )))))
        (_available_263 _x_505 _qs_504 (_init_286 _n_272 End))
  in
  _place_502 (1, Nil)

let find_solution = _find_solution_271

let _queens_all_526 (_number_of_queens_527 : int) =
  _find_solution_271 _number_of_queens_527

let queens_all = _queens_all_526

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_528 _x_538 =
  Call
    ( CountGet,
      (),
      fun (_y_542 : int) ->
        coer_return coer_refl_ty (( = ) _y_542) >>= fun _b_531 ->
        coer_return coer_refl_ty (_b_531 0) >>= fun _b_530 ->
        if _b_530 then coer_return coer_refl_ty _y_542
        else
          coer_computation coer_refl_ty
            (coer_return coer_refl_ty (( - ) _y_542))
          >>= fun _b_533 ->
          coer_computation coer_refl_ty (coer_return coer_refl_ty (_b_533 1))
          >>= fun _b_532 ->
          Call (CountPut, _b_532, fun (_y_540 : unit) -> _count_528 ()) )

let count = _count_528

let _testCount_543 (_m_544 : int) =
  let rec _count_561 _x_538 (_s_598 : int) =
    (if _s_598 = 0 then fun (_x_604 : int) -> _x_604
    else fun (_ : int) -> _count_561 () (_s_598 - 1))
      _s_598
  in
  _count_561 () _m_544

let testCount = _testCount_543

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_608 (_n_609 : int) =
  let rec _generateFromTo_694 _x_638 =
    let _l_611, _u_612 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_638 in
    if _l_611 > _u_612 then fun (_s_761 : int) -> _s_761
    else fun (_s_762 : int) ->
      _generateFromTo_694
        (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_l_611 + 1, _u_612))
        (_s_762 + _l_611)
  in
  _generateFromTo_694 (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (1, _n_609)) 0

let testGenerator = _testGenerator_608
