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
  let rec _choice_12392 _x_12393 =
    if _x_12393 < 1 then
      Call
        ( TripleFail,
          (),
          fun (_y_12396 : empty) ->
            Value (match _y_12396 with _ -> assert false) )
    else
      Call
        ( TripleFlip,
          (),
          fun (_y_12397 : bool) ->
            if _y_12397 then Value _x_12393 else _choice_12392 (_x_12393 - 1) )
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_i_12400 : int) ->
              Value
                (force_unsafe
                   ((handler
                       {
                         value_clause =
                           (fun (_j_12403 : int) ->
                             Value
                               (force_unsafe
                                  ((handler
                                      {
                                        value_clause =
                                          (fun (_k_12406 : int) ->
                                            Value
                                              (if
                                               _i_12400 + _j_12403 + _k_12406
                                               = _s_58
                                              then
                                               TripleCons
                                                 ( (_i_12400, _j_12403, _k_12406),
                                                   TripleNil )
                                              else TripleNil));
                                        effect_clauses =
                                          (fun (type a b)
                                               (eff :
                                                 (a, b) eff_internal_effect) :
                                               (a -> (b -> _) -> _) ->
                                            match eff with
                                            | TripleFail ->
                                                fun _ _l_12413 ->
                                                  Value TripleNil
                                            | TripleFlip ->
                                                fun () _l_12414 ->
                                                  Value
                                                    (_op_42 (* @ *)
                                                       (coer_arrow coer_refl_ty
                                                          force_unsafe _l_12414
                                                          true)
                                                       (coer_arrow coer_refl_ty
                                                          force_unsafe _l_12414
                                                          false))
                                            | eff' ->
                                                fun arg k -> Call (eff', arg, k));
                                      })
                                     (_choice_12392 (_j_12403 - 1)))));
                         effect_clauses =
                           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                (a -> (b -> _) -> _) ->
                             match eff with
                             | TripleFail -> fun _ _l_12418 -> Value TripleNil
                             | TripleFlip ->
                                 fun () _l_12419 ->
                                   Value
                                     (_op_42 (* @ *)
                                        (coer_arrow coer_refl_ty force_unsafe
                                           _l_12419 true)
                                        (coer_arrow coer_refl_ty force_unsafe
                                           _l_12419 false))
                             | eff' -> fun arg k -> Call (eff', arg, k));
                       })
                      (_choice_12392 (_i_12400 - 1)))));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | TripleFail -> fun _ _l_12423 -> Value TripleNil
              | TripleFlip ->
                  fun () _l_12424 ->
                    Value
                      (_op_42 (* @ *)
                         (coer_arrow coer_refl_ty force_unsafe _l_12424 true)
                         (coer_arrow coer_refl_ty force_unsafe _l_12424 false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_choice_12392 _n_57))

let testTriple = _testTriple_56

let _handleTripleWrap_15175 ((_x_15176, _y_15177) : int * int) =
  _testTriple_56 _x_15176 _y_15177

let handleTripleWrap = _handleTripleWrap_15175

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_15179 _x_15188 (_x_15190 : intlist) =
  match _x_15190 with
  | End -> End
  | Lst (_x_15192, _xs_15191) ->
      if _x_15188 _x_15192 then Lst (_x_15192, _filter_15179 _x_15188 _xs_15191)
      else _filter_15179 _x_15188 _xs_15191

let filter = _filter_15179

let rec _forall_15197 _x_15204 (_x_15206 : queen_list) =
  match _x_15206 with
  | Nil -> true
  | Cons (_x_15208, _xs_15207) ->
      _x_15204 _x_15208 && _forall_15197 _x_15204 _xs_15207

let forall = _forall_15197

let _no_attack_15211 ((_x_15212, _y_15213) : int * int)
    ((_x'_15214, _y'_15215) : int * int) =
  _x_15212 <> _x'_15214 && _y_15213 <> _y'_15215
  && abs (_x_15212 - _x'_15214) <> abs (_y_15213 - _y'_15215)

let no_attack = _no_attack_15211

let _available_15227 (_x_15228 : int) (_qs_15229 : queen_list)
    (_l_15230 : intlist) =
  _filter_15179
    (fun (_y_15232 : int) ->
      _forall_15197 (_no_attack_15211 (_x_15228, _y_15232)) _qs_15229)
    _l_15230

let available = _available_15227

let _find_solution_15235 (_n_15236 : int) =
  let rec _init_15250 _x_15275 (_acc_15297 : intlist) =
    if _x_15275 = 0 then _acc_15297
    else _init_15250 (_x_15275 - 1) (Lst (_x_15275, _acc_15297))
  in
  let rec _place_17718 (_x_17720, _qs_17719) =
    if _x_17720 = _n_15236 + 1 then Value (Some _qs_17719)
    else
      Call
        ( Select,
          _available_15227 _x_17720 _qs_17719 (_init_15250 _n_15236 End),
          fun (_y_17728 : int) ->
            _place_17718 (_x_17720 + 1, Cons ((_x_17720, _y_17728), _qs_17719))
        )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_17731 : option) -> Value _id_17731);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Select ->
                  fun _lst_17732 _l_17733 ->
                    Value
                      (let rec _loop_17734 _x_17735 (_x_17736 : intlist) =
                         match _x_17736 with
                         | End -> None
                         | Lst (_x_17738, _xs_17737) -> (
                             match _x_17735 _x_17738 with
                             | None -> _loop_17734 _x_17735 _xs_17737
                             | Some _x_17741 -> Some _x_17741)
                       in
                       _loop_17734
                         (coer_arrow coer_refl_ty force_unsafe _l_17733)
                         _lst_17732)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_place_17718 (1, Nil)))

let find_solution = _find_solution_15235

let _queens_all_18251 (_number_of_queens_18252 : int) =
  _find_solution_15235 _number_of_queens_18252

let queens_all = _queens_all_18251

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_18253 _x_18263 =
  Call
    ( CountGet,
      (),
      fun (_y_18267 : int) ->
        if _y_18267 = 0 then Value _y_18267
        else
          Call (CountPut, _y_18267 - 1, fun (_y_18265 : unit) -> _count_18253 ())
    )

let count = _count_18253

let _testCount_18268 (_m_18269 : int) =
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_18277 : int) -> Value (fun (_x_18279 : int) -> _x_18279));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | CountGet ->
                  fun () _l_18282 ->
                    Value
                      (fun (_s_18272 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_18282 _s_18272
                          _s_18272)
              | CountPut ->
                  fun _s_18274 _l_18283 ->
                    Value
                      (fun (_ : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_18283 ()
                          _s_18274)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_count_18253 ()))
    _m_18269

let testCount = _testCount_18268

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_25367 (_n_25368 : int) =
  let rec _generateFromTo_25369 (_l_25370, _u_25371) =
    if _l_25370 > _u_25371 then Value ()
    else
      Call
        ( GeneratorYield,
          _l_25370,
          fun (_y_25412 : unit) -> _generateFromTo_25369 (_l_25370 + 1, _u_25371)
        )
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_25384 : unit) -> Value (fun (_s_25386 : int) -> _s_25386));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | GeneratorPut ->
                  fun _s'_25377 _l_25398 ->
                    Value
                      (fun (_s_25379 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_25398 ()
                          _s'_25377)
              | GeneratorGet ->
                  fun _ _l_25399 ->
                    Value
                      (fun (_s_25382 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_25399 _s_25382
                          _s_25382)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ((handler
           {
             value_clause = (fun (_x_25410 : unit) -> Value _x_25410);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | GeneratorYield ->
                     fun _e_25388 _l_25404 ->
                       Call
                         ( GeneratorGet,
                           (),
                           fun (_y_25408 : int) ->
                             Call
                               ( GeneratorPut,
                                 _y_25408 + _e_25388,
                                 fun (_y_25406 : unit) -> _l_25404 () ) )
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_generateFromTo_25369 (1, _n_25368))))
    0

let testGenerator = _testGenerator_25367
