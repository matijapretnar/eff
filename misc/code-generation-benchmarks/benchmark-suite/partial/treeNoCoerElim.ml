open OcamlHeader

type tree = Empty | Node of (tree * int * tree)

type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect

let _tester_42 (_k_43 : int) =
  let _leaf_44 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_a_45 : int) ->
        Node
          (coer_tuple_3
             (coer_refl_ty, coer_refl_ty, coer_refl_ty)
             (Empty, _a_45 * _k_43, Empty)))
  in
  let _bot_48 =
    coer_arrow coer_refl_ty (coer_arrow coer_refl_ty coer_refl_ty)
      (fun (_t_49 : tree) (_t2_50 : tree) ->
        Node
          ( Node
              (coer_tuple_3
                 (coer_refl_ty, coer_refl_ty, coer_refl_ty)
                 ( Node
                     (coer_tuple_3
                        (coer_refl_ty, coer_refl_ty, coer_refl_ty)
                        (_t_49, 0, _t2_50)),
                   2,
                   _leaf_44 13 )),
            5,
            Node
              (coer_tuple_3
                 (coer_refl_ty, coer_refl_ty, coer_refl_ty)
                 ( _leaf_44 9,
                   7,
                   Node
                     ( _t2_50,
                       3,
                       Node
                         (coer_tuple_3
                            (coer_refl_ty, coer_refl_ty, coer_refl_ty)
                            (_leaf_44 3, 5, _t2_50)) ) )) ))
  in
  _bot_48
    (Node
       (coer_tuple_3
          (coer_refl_ty, coer_refl_ty, coer_refl_ty)
          ( _bot_48 (_leaf_44 3) (_leaf_44 4),
            10,
            _bot_48 (_leaf_44 1) (_leaf_44 3) )))
    (_bot_48
       (Node
          (coer_tuple_3
             (coer_refl_ty, coer_refl_ty, coer_refl_ty)
             ( _bot_48 (_leaf_44 3) (_leaf_44 4),
               10,
               _bot_48 (_leaf_44 1) (_leaf_44 3) )))
       (_leaf_44 10))

let tester = _tester_42

let _max_88 (_a_89 : int) (_b_90 : int) = if _a_89 > _b_90 then _a_89 else _b_90

let max = _max_88

let _effect_max_93 (_m_94 : int) =
  let rec _find_max_141 (_x_115, _k_143) =
    match _x_115 with
    | Empty -> _k_143 0
    | Node (Empty, _x_123, Empty) -> _k_143 _x_123
    | Node (_left_126, _x_125, _right_124) ->
        let _l_116 (_y_127 : bool) =
          if _y_127 then
            _find_max_141
              (_left_126, fun (_next_128 : int) -> _k_143 (_x_125 + _next_128))
          else
            _find_max_141
              (_right_124, fun (_next_128 : int) -> _k_143 (_x_125 + _next_128))
        in
        _max_88 (_l_116 true) (_l_116 false)
  in
  _find_max_141 (_tester_42 _m_94, fun (_x_110 : int) -> _x_110)

let effect_max = _effect_max_93

let _test_max_160 (_m_161 : int) = _effect_max_93 _m_161

let test_max = _test_max_160

let _op_162 (_x_163 : int) (_y_164 : int) = _x_163 - (3 * _y_164)

let op = _op_162

let _max_168 (_a_169 : int) (_b_170 : int) =
  if _a_169 > _b_170 then _a_169 else _b_170

let max = _max_168

type intlist = Nil | Cons of (int * intlist)

let rec _op_173 (* @ *) _x_180 (_ys_182 : intlist) =
  match _x_180 with
  | Nil -> _ys_182
  | Cons (_x_184, _xs_183) ->
      Cons
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           (_x_184, _op_173 (* @ *) _xs_183 _ys_182))

let _op_173 (* @ *) = _op_173 (* @ *)

let _test_general_187 (_m_188 : int) =
  let rec _maxl_189 _x_219 (_x_191 : intlist) =
    match _x_191 with
    | Nil -> _x_219
    | Cons (_x_192, _xs_193) -> _maxl_189 (_max_168 _x_192 _x_219) _xs_193
  in
  _maxl_189 0
    (let rec _explore_255 (_x_222, _k_257) =
       match _x_222 with
       | Empty -> _k_257 0
       | Node (_left_238, _x_237, _right_236) ->
           let _l_223 (_y_239 : bool) =
             if _y_239 then
               _explore_255
                 ( _left_238,
                   fun (_b_272 : int) -> _k_257 (_op_162 _x_237 _b_272) )
             else
               _explore_255
                 ( _right_236,
                   fun (_b_276 : int) -> _k_257 (_op_162 _x_237 _b_276) )
           in
           _op_173 (* @ *) (_l_223 true) (_l_223 false)
     in
     _explore_255
       ( _tester_42 _m_188,
         fun (_x_214 : int) ->
           Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_214, Nil)) ))

let test_general = _test_general_187

let _test_general_loop_278 (_m_279 : int) =
  let rec _maxl_280 _x_322 (_x_282 : intlist) =
    match _x_282 with
    | Nil -> _x_322
    | Cons (_x_283, _xs_284) -> _maxl_280 (_max_168 _x_283 _x_322) _xs_284
  in
  let ____t_288 = _tester_42 _m_279 in
  let rec _looper_330 _x_331 (_s_333 : int) =
    if _x_331 = 0 then _s_333
    else
      _looper_330 (_x_331 - 1)
        (_s_333
        + _maxl_280 0
            (let rec _explore_372 (_x_325, _k_374) =
               match _x_325 with
               | Empty -> _k_374 0
               | Node (_left_355, _x_354, _right_353) ->
                   let _l_326 (_y_356 : bool) =
                     if _y_356 then
                       _explore_372
                         ( _left_355,
                           fun (_b_389 : int) -> _k_374 (_op_162 _x_354 _b_389)
                         )
                     else
                       _explore_372
                         ( _right_353,
                           fun (_b_393 : int) -> _k_374 (_op_162 _x_354 _b_393)
                         )
                   in
                   _op_173 (* @ *) (_l_326 true) (_l_326 false)
             in
             _explore_372
               ( ____t_288,
                 fun (_x_305 : int) ->
                   Cons
                     (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_305, Nil))
               )))
  in
  _looper_330 100 0

let test_general_loop = _test_general_loop_278

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_395 (_void_396 : float) = match _void_396 with _ -> assert false

let absurd = _absurd_395

let _test_leaf_state_397 (_m_398 : int) =
  let rec _maxl_399 _x_450 (_x_401 : intlist) =
    match _x_401 with
    | Nil -> _x_450
    | Cons (_x_402, _xs_403) -> _maxl_399 (_max_168 _x_402 _x_450) _xs_403
  in
  let rec _populate_leafs_407 _x_451 (_n_409 : int) =
    if _x_451 = _n_409 then Nil
    else
      Cons
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           (_x_451 * 3, _populate_leafs_407 (_x_451 + 1) _n_409))
  in
  _maxl_399 0
    (let rec _explore_498 (_x_456, _k_500) =
       match _x_456 with
       | Empty -> Call (Get, (), fun (_y_481 : int) -> _k_500 _y_481)
       | Node (_left_484, _x_483, _right_482) ->
           let _l_457 (_y_485 : bool) =
             if _y_485 then
               coer_return coer_refl_ty (_op_162 _x_483) >>= fun _x_529 ->
               _explore_498
                 ( _left_484,
                   fun (_b_530 : int) ->
                     coer_return coer_refl_ty (_x_529 _b_530) >>= fun _x_531 ->
                     _k_500 _x_531 )
             else
               coer_return coer_refl_ty (_op_162 _x_483) >>= fun _x_549 ->
               _explore_498
                 ( _right_482,
                   fun (_b_550 : int) ->
                     coer_return coer_refl_ty (_x_549 _b_550) >>= fun _x_551 ->
                     _k_500 _x_551 )
           in
           _l_457 true >>= fun _b_433 ->
           coer_return coer_refl_ty (_op_173 (* @ *) _b_433) >>= fun _b_432 ->
           _l_457 false >>= fun _b_434 ->
           coer_return coer_refl_ty (_b_432 _b_434)
     in
     let rec _explore_552 (_x_456, _k_500) =
       match _x_456 with
       | Empty -> (
           fun (_s_554 : intlist) ->
             match _s_554 with
             | Cons (_x_556, _rest_555) ->
                 force_unsafe
                   ((handler
                       {
                         value_clause =
                           (fun (_x_559 : intlist) ->
                             Value (fun (_ : intlist) -> _x_559));
                         effect_clauses =
                           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                (a -> (b -> _) -> _) ->
                             match eff with
                             | Get ->
                                 fun () _l_560 ->
                                   Value
                                     (fun (_s_561 : intlist) ->
                                       match _s_561 with
                                       | Cons (_x_563, _rest_562) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_560 _x_563 _rest_562
                                       | Nil -> Nil)
                             | eff' -> fun arg k -> Call (eff', arg, k));
                       })
                      (_k_500 _x_556))
                   _rest_555
             | Nil -> Nil)
       | Node (_left_484, _x_483, _right_482) ->
           let _l_457 (_y_485 : bool) =
             if _y_485 then
               coer_return coer_refl_ty (_op_162 _x_483) >>= fun _x_529 ->
               _explore_498
                 ( _left_484,
                   fun (_b_530 : int) ->
                     coer_return coer_refl_ty (_x_529 _b_530) >>= fun _x_531 ->
                     _k_500 _x_531 )
             else
               coer_return coer_refl_ty (_op_162 _x_483) >>= fun _x_549 ->
               _explore_498
                 ( _right_482,
                   fun (_b_550 : int) ->
                     coer_return coer_refl_ty (_x_549 _b_550) >>= fun _x_551 ->
                     _k_500 _x_551 )
           in
           force_unsafe
             ((handler
                 {
                   value_clause =
                     (fun (_b_433 : intlist) ->
                       Value
                         (force_unsafe
                            ((handler
                                {
                                  value_clause =
                                    (fun (_b_569 : intlist) ->
                                      Value
                                        (fun (_ : intlist) ->
                                          _op_173 (* @ *) _b_433 _b_569));
                                  effect_clauses =
                                    (fun (type a b)
                                         (eff : (a, b) eff_internal_effect) :
                                         (a -> (b -> _) -> _) ->
                                      match eff with
                                      | Get ->
                                          fun () _l_571 ->
                                            Value
                                              (fun (_s_572 : intlist) ->
                                                match _s_572 with
                                                | Cons (_x_574, _rest_573) ->
                                                    coer_arrow coer_refl_ty
                                                      force_unsafe _l_571 _x_574
                                                      _rest_573
                                                | Nil -> Nil)
                                      | eff' -> fun arg k -> Call (eff', arg, k));
                                })
                               (_l_457 false))));
                   effect_clauses =
                     (fun (type a b) (eff : (a, b) eff_internal_effect) :
                          (a -> (b -> _) -> _) ->
                       match eff with
                       | Get ->
                           fun () _l_470 ->
                             Value
                               (fun (_s_471 : intlist) ->
                                 match _s_471 with
                                 | Cons (_x_473, _rest_472) ->
                                     coer_arrow coer_refl_ty force_unsafe _l_470
                                       _x_473 _rest_472
                                 | Nil -> Nil)
                       | eff' -> fun arg k -> Call (eff', arg, k));
                 })
                (_l_457 true))
     in
     _explore_552
       ( _tester_42 _m_398,
         fun (_x_435 : int) ->
           coer_return coer_refl_ty
             (Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_435, Nil))) )
       (_populate_leafs_407 0 154))

let test_leaf_state = _test_leaf_state_397

let _test_leaf_state_loop_2589 (_m_2590 : int) =
  let rec _maxl_2591 _x_2654 (_x_2593 : intlist) =
    match _x_2593 with
    | Nil -> _x_2654
    | Cons (_x_2594, _xs_2595) -> _maxl_2591 (_max_168 _x_2594 _x_2654) _xs_2595
  in
  let rec _populate_leafs_2599 _x_2655 (_n_2601 : int) =
    if _x_2655 = _n_2601 then Nil
    else
      Cons
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           (_x_2655 * 3, _populate_leafs_2599 (_x_2655 + 1) _n_2601))
  in
  let ____leafs_2610 = _populate_leafs_2599 0 154 in
  let ____t_2612 = _tester_42 _m_2590 in
  let rec _looper_2684 _x_2685 (_s_2687 : int) =
    if _x_2685 = 0 then _s_2687
    else
      _looper_2684 (_x_2685 - 1)
        (_s_2687
        + _maxl_2591 0
            (let rec _explore_2729 (_x_2660, _k_2731) =
               match _x_2660 with
               | Empty -> Call (Get, (), fun (_y_2712 : int) -> _k_2731 _y_2712)
               | Node (_left_2715, _x_2714, _right_2713) ->
                   let _l_2661 (_y_2716 : bool) =
                     if _y_2716 then
                       coer_return coer_refl_ty (_op_162 _x_2714)
                       >>= fun _x_2760 ->
                       _explore_2729
                         ( _left_2715,
                           fun (_b_2761 : int) ->
                             coer_return coer_refl_ty (_x_2760 _b_2761)
                             >>= fun _x_2762 -> _k_2731 _x_2762 )
                     else
                       coer_return coer_refl_ty (_op_162 _x_2714)
                       >>= fun _x_2780 ->
                       _explore_2729
                         ( _right_2713,
                           fun (_b_2781 : int) ->
                             coer_return coer_refl_ty (_x_2780 _b_2781)
                             >>= fun _x_2782 -> _k_2731 _x_2782 )
                   in
                   _l_2661 true >>= fun _b_2625 ->
                   coer_return coer_refl_ty (_op_173 (* @ *) _b_2625)
                   >>= fun _b_2624 ->
                   _l_2661 false >>= fun _b_2626 ->
                   coer_return coer_refl_ty (_b_2624 _b_2626)
             in
             let rec _explore_2783 (_x_2660, _k_2731) =
               match _x_2660 with
               | Empty -> (
                   fun (_s_2785 : intlist) ->
                     match _s_2785 with
                     | Cons (_x_2787, _rest_2786) ->
                         force_unsafe
                           ((handler
                               {
                                 value_clause =
                                   (fun (_x_2790 : intlist) ->
                                     Value (fun (_ : intlist) -> _x_2790));
                                 effect_clauses =
                                   (fun (type a b)
                                        (eff : (a, b) eff_internal_effect) :
                                        (a -> (b -> _) -> _) ->
                                     match eff with
                                     | Get ->
                                         fun () _l_2791 ->
                                           Value
                                             (fun (_s_2792 : intlist) ->
                                               match _s_2792 with
                                               | Cons (_x_2794, _rest_2793) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l_2791
                                                     _x_2794 _rest_2793
                                               | Nil -> Nil)
                                     | eff' -> fun arg k -> Call (eff', arg, k));
                               })
                              (_k_2731 _x_2787))
                           _rest_2786
                     | Nil -> Nil)
               | Node (_left_2715, _x_2714, _right_2713) ->
                   let _l_2661 (_y_2716 : bool) =
                     if _y_2716 then
                       coer_return coer_refl_ty (_op_162 _x_2714)
                       >>= fun _x_2760 ->
                       _explore_2729
                         ( _left_2715,
                           fun (_b_2761 : int) ->
                             coer_return coer_refl_ty (_x_2760 _b_2761)
                             >>= fun _x_2762 -> _k_2731 _x_2762 )
                     else
                       coer_return coer_refl_ty (_op_162 _x_2714)
                       >>= fun _x_2780 ->
                       _explore_2729
                         ( _right_2713,
                           fun (_b_2781 : int) ->
                             coer_return coer_refl_ty (_x_2780 _b_2781)
                             >>= fun _x_2782 -> _k_2731 _x_2782 )
                   in
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_b_2625 : intlist) ->
                               Value
                                 (force_unsafe
                                    ((handler
                                        {
                                          value_clause =
                                            (fun (_b_2800 : intlist) ->
                                              Value
                                                (fun (_ : intlist) ->
                                                  _op_173 (* @ *) _b_2625
                                                    _b_2800));
                                          effect_clauses =
                                            (fun (type a b)
                                                 (eff :
                                                   (a, b) eff_internal_effect) :
                                                 (a -> (b -> _) -> _) ->
                                              match eff with
                                              | Get ->
                                                  fun () _l_2802 ->
                                                    Value
                                                      (fun (_s_2803 : intlist) ->
                                                        match _s_2803 with
                                                        | Cons
                                                            (_x_2805, _rest_2804)
                                                          ->
                                                            coer_arrow
                                                              coer_refl_ty
                                                              force_unsafe
                                                              _l_2802 _x_2805
                                                              _rest_2804
                                                        | Nil -> Nil)
                                              | eff' ->
                                                  fun arg k ->
                                                    Call (eff', arg, k));
                                        })
                                       (_l_2661 false))));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect)
                                  : (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l_2700 ->
                                     Value
                                       (fun (_s_2701 : intlist) ->
                                         match _s_2701 with
                                         | Cons (_x_2703, _rest_2702) ->
                                             coer_arrow coer_refl_ty
                                               force_unsafe _l_2700 _x_2703
                                               _rest_2702
                                         | Nil -> Nil)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_l_2661 true))
             in
             _explore_2783
               ( ____t_2612,
                 fun (_x_2627 : int) ->
                   coer_return coer_refl_ty
                     (Cons
                        (coer_tuple_2
                           (coer_refl_ty, coer_refl_ty)
                           (_x_2627, Nil))) )
               ____leafs_2610))
  in
  _looper_2684 100 0

let test_leaf_state_loop = _test_leaf_state_loop_2589

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_4820 (_m_4821 : int) =
  let rec _maxl_4822 _x_4864 (_x_4824 : intlist) =
    match _x_4824 with
    | Nil -> _x_4864
    | Cons (_x_4825, _xs_4826) -> _maxl_4822 (_max_168 _x_4825 _x_4864) _xs_4826
  in
  _maxl_4822 0
    (let rec _explore_4922 (_x_4871, _k_4924) =
       match _x_4871 with
       | Empty -> Call (Get, (), fun (_y_4902 : int) -> _k_4924 _y_4902)
       | Node (_left_4905, _x_4904, _right_4903) ->
           coer_return coer_refl_ty (( * ) _x_4904) >>= fun _x_4979 ->
           coer_return coer_refl_ty (_x_4979 _x_4904) >>= fun _x_5021 ->
           Call
             ( Set,
               _x_5021,
               fun (_y_5022 : unit) ->
                 let _l_5023 (_y_5027 : bool) =
                   if _y_5027 then
                     coer_return coer_refl_ty (_op_162 _x_4904)
                     >>= fun _x_5028 ->
                     _explore_4922
                       ( _left_4905,
                         fun (_b_5029 : int) ->
                           coer_return coer_refl_ty (_x_5028 _b_5029)
                           >>= fun _x_5030 -> _k_4924 _x_5030 )
                   else
                     coer_return coer_refl_ty (_op_162 _x_4904)
                     >>= fun _x_5031 ->
                     _explore_4922
                       ( _right_4903,
                         fun (_b_5032 : int) ->
                           coer_return coer_refl_ty (_x_5031 _b_5032)
                           >>= fun _x_5033 -> _k_4924 _x_5033 )
                 in
                 _l_5023 true >>= fun _b_5024 ->
                 coer_return coer_refl_ty (_op_173 (* @ *) _b_5024)
                 >>= fun _b_5025 ->
                 _l_5023 false >>= fun _b_5026 ->
                 coer_return coer_refl_ty (_b_5025 _b_5026) )
     in
     let rec _explore_5034 (_x_4871, _k_4924) =
       match _x_4871 with
       | Empty ->
           fun (_s_5036 : int) ->
             force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_5039 : intlist) ->
                         Value (fun (_ : int) -> _x_5039));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_5040 ->
                               Value
                                 (fun (_s_5041 : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_5040
                                     _s_5041 _s_5041)
                         | Set ->
                             fun _s_5043 _l_5044 ->
                               Value
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_5044
                                     () _s_5043)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (_k_4924 _s_5036))
               _s_5036
       | Node (_left_4905, _x_4904, _right_4903) ->
           fun (_ : int) ->
             (let _l_5372 (_y_5389 : bool) =
                if _y_5389 then
                  coer_return coer_refl_ty (_op_162 _x_4904) >>= fun _x_5390 ->
                  _explore_4922
                    ( _left_4905,
                      fun (_b_5391 : int) ->
                        coer_return coer_refl_ty (_x_5390 _b_5391)
                        >>= fun _x_5392 -> _k_4924 _x_5392 )
                else
                  coer_return coer_refl_ty (_op_162 _x_4904) >>= fun _x_5393 ->
                  _explore_4922
                    ( _right_4903,
                      fun (_b_5394 : int) ->
                        coer_return coer_refl_ty (_x_5393 _b_5394)
                        >>= fun _x_5395 -> _k_4924 _x_5395 )
              in
              force_unsafe
                ((handler
                    {
                      value_clause =
                        (fun (_b_5373 : intlist) ->
                          Value
                            (force_unsafe
                               ((handler
                                   {
                                     value_clause =
                                       (fun (_b_5375 : intlist) ->
                                         Value
                                           (fun (_ : int) ->
                                             _op_173 (* @ *) _b_5373 _b_5375));
                                     effect_clauses =
                                       (fun (type a b)
                                            (eff : (a, b) eff_internal_effect) :
                                            (a -> (b -> _) -> _) ->
                                         match eff with
                                         | Get ->
                                             fun () _l_5377 ->
                                               Value
                                                 (fun (_s_5378 : int) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l_5377
                                                     _s_5378 _s_5378)
                                         | Set ->
                                             fun _s_5380 _l_5381 ->
                                               Value
                                                 (fun (_ : int) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l_5381 ()
                                                     _s_5380)
                                         | eff' ->
                                             fun arg k -> Call (eff', arg, k));
                                   })
                                  (_l_5372 false))));
                      effect_clauses =
                        (fun (type a b) (eff : (a, b) eff_internal_effect) :
                             (a -> (b -> _) -> _) ->
                          match eff with
                          | Get ->
                              fun () _l_5383 ->
                                Value
                                  (fun (_s_5384 : int) ->
                                    coer_arrow coer_refl_ty force_unsafe _l_5383
                                      _s_5384 _s_5384)
                          | Set ->
                              fun _s_5386 _l_5387 ->
                                Value
                                  (fun (_ : int) ->
                                    coer_arrow coer_refl_ty force_unsafe _l_5387
                                      () _s_5386)
                          | eff' -> fun arg k -> Call (eff', arg, k));
                    })
                   (_l_5372 true)))
               (_x_4904 * _x_4904)
     in
     _explore_5034
       ( _tester_42 _m_4821,
         fun (_x_4847 : int) ->
           coer_return coer_refl_ty
             (Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_4847, Nil)))
       )
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_4820

let _test_leaf_state_update_loop_21611 (_m_21612 : int) =
  let rec _maxl_21613 _x_21667 (_x_21615 : intlist) =
    match _x_21615 with
    | Nil -> _x_21667
    | Cons (_x_21616, _xs_21617) ->
        _maxl_21613 (_max_168 _x_21616 _x_21667) _xs_21617
  in
  let ____t_21621 = _tester_42 _m_21612 in
  let rec _looper_21700 _x_21701 (_s_21703 : int) =
    if _x_21701 = 0 then _s_21703
    else
      _looper_21700 (_x_21701 - 1)
        (_s_21703
        + _maxl_21613 0
            (let rec _explore_21752 (_x_21674, _k_21754) =
               match _x_21674 with
               | Empty ->
                   Call (Get, (), fun (_y_21732 : int) -> _k_21754 _y_21732)
               | Node (_left_21735, _x_21734, _right_21733) ->
                   coer_return coer_refl_ty (( * ) _x_21734) >>= fun _x_21809 ->
                   coer_return coer_refl_ty (_x_21809 _x_21734)
                   >>= fun _x_21851 ->
                   Call
                     ( Set,
                       _x_21851,
                       fun (_y_21852 : unit) ->
                         let _l_21853 (_y_21857 : bool) =
                           if _y_21857 then
                             coer_return coer_refl_ty (_op_162 _x_21734)
                             >>= fun _x_21858 ->
                             _explore_21752
                               ( _left_21735,
                                 fun (_b_21859 : int) ->
                                   coer_return coer_refl_ty (_x_21858 _b_21859)
                                   >>= fun _x_21860 -> _k_21754 _x_21860 )
                           else
                             coer_return coer_refl_ty (_op_162 _x_21734)
                             >>= fun _x_21861 ->
                             _explore_21752
                               ( _right_21733,
                                 fun (_b_21862 : int) ->
                                   coer_return coer_refl_ty (_x_21861 _b_21862)
                                   >>= fun _x_21863 -> _k_21754 _x_21863 )
                         in
                         _l_21853 true >>= fun _b_21854 ->
                         coer_return coer_refl_ty (_op_173 (* @ *) _b_21854)
                         >>= fun _b_21855 ->
                         _l_21853 false >>= fun _b_21856 ->
                         coer_return coer_refl_ty (_b_21855 _b_21856) )
             in
             let rec _explore_21864 (_x_21674, _k_21754) =
               match _x_21674 with
               | Empty ->
                   fun (_s_21866 : int) ->
                     force_unsafe
                       ((handler
                           {
                             value_clause =
                               (fun (_x_21869 : intlist) ->
                                 Value (fun (_ : int) -> _x_21869));
                             effect_clauses =
                               (fun (type a b)
                                    (eff : (a, b) eff_internal_effect) :
                                    (a -> (b -> _) -> _) ->
                                 match eff with
                                 | Get ->
                                     fun () _l_21870 ->
                                       Value
                                         (fun (_s_21871 : int) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_21870 _s_21871 _s_21871)
                                 | Set ->
                                     fun _s_21873 _l_21874 ->
                                       Value
                                         (fun (_ : int) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_21874 () _s_21873)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (_k_21754 _s_21866))
                       _s_21866
               | Node (_left_21735, _x_21734, _right_21733) ->
                   fun (_ : int) ->
                     (let _l_22202 (_y_22219 : bool) =
                        if _y_22219 then
                          coer_return coer_refl_ty (_op_162 _x_21734)
                          >>= fun _x_22220 ->
                          _explore_21752
                            ( _left_21735,
                              fun (_b_22221 : int) ->
                                coer_return coer_refl_ty (_x_22220 _b_22221)
                                >>= fun _x_22222 -> _k_21754 _x_22222 )
                        else
                          coer_return coer_refl_ty (_op_162 _x_21734)
                          >>= fun _x_22223 ->
                          _explore_21752
                            ( _right_21733,
                              fun (_b_22224 : int) ->
                                coer_return coer_refl_ty (_x_22223 _b_22224)
                                >>= fun _x_22225 -> _k_21754 _x_22225 )
                      in
                      force_unsafe
                        ((handler
                            {
                              value_clause =
                                (fun (_b_22203 : intlist) ->
                                  Value
                                    (force_unsafe
                                       ((handler
                                           {
                                             value_clause =
                                               (fun (_b_22205 : intlist) ->
                                                 Value
                                                   (fun (_ : int) ->
                                                     _op_173 (* @ *) _b_22203
                                                       _b_22205));
                                             effect_clauses =
                                               (fun (type a b)
                                                    (eff :
                                                      (a, b) eff_internal_effect)
                                                    : (a -> (b -> _) -> _) ->
                                                 match eff with
                                                 | Get ->
                                                     fun () _l_22207 ->
                                                       Value
                                                         (fun (_s_22208 : int) ->
                                                           coer_arrow
                                                             coer_refl_ty
                                                             force_unsafe
                                                             _l_22207 _s_22208
                                                             _s_22208)
                                                 | Set ->
                                                     fun _s_22210 _l_22211 ->
                                                       Value
                                                         (fun (_ : int) ->
                                                           coer_arrow
                                                             coer_refl_ty
                                                             force_unsafe
                                                             _l_22211 ()
                                                             _s_22210)
                                                 | eff' ->
                                                     fun arg k ->
                                                       Call (eff', arg, k));
                                           })
                                          (_l_22202 false))));
                              effect_clauses =
                                (fun (type a b)
                                     (eff : (a, b) eff_internal_effect) :
                                     (a -> (b -> _) -> _) ->
                                  match eff with
                                  | Get ->
                                      fun () _l_22213 ->
                                        Value
                                          (fun (_s_22214 : int) ->
                                            coer_arrow coer_refl_ty force_unsafe
                                              _l_22213 _s_22214 _s_22214)
                                  | Set ->
                                      fun _s_22216 _l_22217 ->
                                        Value
                                          (fun (_ : int) ->
                                            coer_arrow coer_refl_ty force_unsafe
                                              _l_22217 () _s_22216)
                                  | eff' -> fun arg k -> Call (eff', arg, k));
                            })
                           (_l_22202 true)))
                       (_x_21734 * _x_21734)
             in
             _explore_21864
               ( ____t_21621,
                 fun (_x_21638 : int) ->
                   coer_return coer_refl_ty
                     (Cons
                        (coer_tuple_2
                           (coer_refl_ty, coer_refl_ty)
                           (_x_21638, Nil))) )
               ~-1))
  in
  _looper_21700 100 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_21611

let _test_leaf_state_update_merged_handler_38441 (_m_38442 : int) =
  let rec _maxl_38443 _x_38484 (_x_38445 : intlist) =
    match _x_38445 with
    | Nil -> _x_38484
    | Cons (_x_38446, _xs_38447) ->
        _maxl_38443 (_max_168 _x_38446 _x_38484) _xs_38447
  in
  _maxl_38443 0
    (let rec _explore_38534 (_x_38491, _k_38536) =
       match _x_38491 with
       | Empty -> fun (_s_38545 : int) -> _k_38536 _s_38545 _s_38545
       | Node (_left_38512, _x_38511, _right_38510) ->
           fun (_ : int) ->
             (let _l_38666 (_y_38673 : bool) =
                if _y_38673 then
                  _explore_38534
                    ( _left_38512,
                      fun (_b_38675 : int) ->
                        _k_38536 (_op_162 _x_38511 _b_38675) )
                else
                  _explore_38534
                    ( _right_38510,
                      fun (_b_38678 : int) ->
                        _k_38536 (_op_162 _x_38511 _b_38678) )
              in
              fun (_s_38667 : int) ->
                _op_173
                  (* @ *) (_l_38666 true _s_38667)
                  (_l_38666 false _s_38667))
               (_x_38511 * _x_38511)
     in
     _explore_38534
       ( _tester_42 _m_38442,
         fun (_x_38477 : int) (_ : int) ->
           Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_38477, Nil)) )
       ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_38441

let _test_leaf_state_update_merged_handler_loop_38680 (_m_38681 : int) =
  let rec _maxl_38682 _x_38735 (_x_38684 : intlist) =
    match _x_38684 with
    | Nil -> _x_38735
    | Cons (_x_38685, _xs_38686) ->
        _maxl_38682 (_max_168 _x_38685 _x_38735) _xs_38686
  in
  let ____t_38690 = _tester_42 _m_38681 in
  let rec _looper_38749 _x_38750 (_s_38752 : int) =
    if _x_38750 = 0 then _s_38752
    else
      _looper_38749 (_x_38750 - 1)
        (_s_38752
        + _maxl_38682 0
            (let rec _explore_38799 (_x_38742, _k_38801) =
               match _x_38742 with
               | Empty -> fun (_s_38810 : int) -> _k_38801 _s_38810 _s_38810
               | Node (_left_38777, _x_38776, _right_38775) ->
                   fun (_ : int) ->
                     (let _l_38931 (_y_38938 : bool) =
                        if _y_38938 then
                          _explore_38799
                            ( _left_38777,
                              fun (_b_38940 : int) ->
                                _k_38801 (_op_162 _x_38776 _b_38940) )
                        else
                          _explore_38799
                            ( _right_38775,
                              fun (_b_38943 : int) ->
                                _k_38801 (_op_162 _x_38776 _b_38943) )
                      in
                      fun (_s_38932 : int) ->
                        _op_173
                          (* @ *) (_l_38931 true _s_38932)
                          (_l_38931 false _s_38932))
                       (_x_38776 * _x_38776)
             in
             _explore_38799
               ( ____t_38690,
                 fun (_x_38716 : int) (_ : int) ->
                   Cons
                     (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_38716, Nil))
               )
               ~-1))
  in
  _looper_38749 100 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_38680
