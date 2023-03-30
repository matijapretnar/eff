open OcamlHeader

type tree = Empty | Node of (tree * int * tree)
type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect

let _tester_42 (_k_43 : int) =
  let _leaf_44 (_a_45 : int) = Node (Empty, _a_45 * _k_43, Empty) in
  let _bot_48 (_t_49 : tree) (_t2_50 : tree) =
    Node
      ( Node (Node (_t_49, 0, _t2_50), 2, _leaf_44 13),
        5,
        Node (_leaf_44 9, 7, Node (_t2_50, 3, Node (_leaf_44 3, 5, _t2_50))) )
  in
  _bot_48
    (Node
       (_bot_48 (_leaf_44 3) (_leaf_44 4), 10, _bot_48 (_leaf_44 1) (_leaf_44 3)))
    (_bot_48
       (Node
          ( _bot_48 (_leaf_44 3) (_leaf_44 4),
            10,
            _bot_48 (_leaf_44 1) (_leaf_44 3) ))
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
  | Cons (_x_184, _xs_183) -> Cons (_x_184, _op_173 (* @ *) _xs_183 _ys_182)

let _op_173 (* @ *) = _op_173 (* @ *)

let _test_general_187 (_m_188 : int) =
  let rec _maxl_189 _x_219 (_x_279 : intlist) =
    match _x_279 with
    | Nil -> _x_219
    | Cons (_x_281, _xs_280) -> _maxl_189 (_max_168 _x_281 _x_219) _xs_280
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
     _explore_255 (_tester_42 _m_188, fun (_x_214 : int) -> Cons (_x_214, Nil)))

let test_general = _test_general_187

let _test_general_loop_285 (_m_286 : int) =
  let rec _maxl_287 _x_329 (_x_414 : intlist) =
    match _x_414 with
    | Nil -> _x_329
    | Cons (_x_416, _xs_415) -> _maxl_287 (_max_168 _x_416 _x_329) _xs_415
  in
  let ____t_295 = _tester_42 _m_286 in
  let rec _looper_349 _x_350 (_s_351 : int) =
    if _x_350 = 0 then _s_351
    else
      _looper_349 (_x_350 - 1)
        (_s_351
        + _maxl_287 0
            (let rec _explore_390 (_x_332, _k_392) =
               match _x_332 with
               | Empty -> _k_392 0
               | Node (_left_373, _x_372, _right_371) ->
                   let _l_333 (_y_374 : bool) =
                     if _y_374 then
                       _explore_390
                         ( _left_373,
                           fun (_b_407 : int) -> _k_392 (_op_162 _x_372 _b_407)
                         )
                     else
                       _explore_390
                         ( _right_371,
                           fun (_b_411 : int) -> _k_392 (_op_162 _x_372 _b_411)
                         )
                   in
                   _op_173 (* @ *) (_l_333 true) (_l_333 false)
             in
             _explore_390 (____t_295, fun (_x_312 : int) -> Cons (_x_312, Nil)))
        )
  in
  _looper_349 100 0

let test_general_loop = _test_general_loop_285

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_420 (_void_421 : float) = match _void_421 with _ -> assert false
let absurd = _absurd_420

let _test_leaf_state_422 (_m_423 : int) =
  let rec _maxl_424 _x_475 (_x_1533 : intlist) =
    match _x_1533 with
    | Nil -> _x_475
    | Cons (_x_1535, _xs_1534) -> _maxl_424 (_max_168 _x_1535 _x_475) _xs_1534
  in
  let rec _populate_leafs_432 _x_476 (_n_634 : int) =
    if _x_476 = _n_634 then Nil
    else Cons (_x_476 * 3, _populate_leafs_432 (_x_476 + 1) _n_634)
  in
  _maxl_424 0
    (let rec _explore_523 (_x_481, _k_525) =
       match _x_481 with
       | Empty -> Call (Get, (), fun (_y_506 : int) -> _k_525 _y_506)
       | Node (_left_509, _x_508, _right_507) ->
           let _l_482 (_y_510 : bool) =
             if _y_510 then
               _explore_523
                 ( _left_509,
                   fun (_b_555 : int) -> _k_525 (_op_162 _x_508 _b_555) )
             else
               _explore_523
                 ( _right_507,
                   fun (_b_575 : int) -> _k_525 (_op_162 _x_508 _b_575) )
           in
           _l_482 true >>= fun _b_458 ->
           _l_482 false >>= fun _b_459 -> Value (_op_173 (* @ *) _b_458 _b_459)
     in
     let rec _explore_577 (_x_481, _k_525) =
       match _x_481 with
       | Empty -> (
           fun (_s_579 : intlist) ->
             match _s_579 with
             | Cons (_x_581, _rest_580) ->
                 force_unsafe
                   ((handler
                       {
                         value_clause =
                           (fun (_x_584 : intlist) ->
                             Value (fun (_ : intlist) -> _x_584));
                         effect_clauses =
                           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                (a -> (b -> _) -> _) ->
                             match eff with
                             | Get ->
                                 fun () _l_585 ->
                                   Value
                                     (fun (_s_586 : intlist) ->
                                       match _s_586 with
                                       | Cons (_x_588, _rest_587) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_585 _x_588 _rest_587
                                       | Nil -> Nil)
                             | eff' -> fun arg k -> Call (eff', arg, k));
                       })
                      (_k_525 _x_581))
                   _rest_580
             | Nil -> Nil)
       | Node (_left_509, _x_508, _right_507) ->
           let _l_482 (_y_510 : bool) =
             if _y_510 then
               _explore_523
                 ( _left_509,
                   fun (_b_555 : int) -> _k_525 (_op_162 _x_508 _b_555) )
             else
               _explore_523
                 ( _right_507,
                   fun (_b_575 : int) -> _k_525 (_op_162 _x_508 _b_575) )
           in
           force_unsafe
             ((handler
                 {
                   value_clause =
                     (fun (_b_458 : intlist) ->
                       Value
                         (force_unsafe
                            ((handler
                                {
                                  value_clause =
                                    (fun (_b_594 : intlist) ->
                                      Value
                                        (fun (_ : intlist) ->
                                          _op_173 (* @ *) _b_458 _b_594));
                                  effect_clauses =
                                    (fun (type a b)
                                         (eff : (a, b) eff_internal_effect) :
                                         (a -> (b -> _) -> _) ->
                                      match eff with
                                      | Get ->
                                          fun () _l_596 ->
                                            Value
                                              (fun (_s_597 : intlist) ->
                                                match _s_597 with
                                                | Cons (_x_599, _rest_598) ->
                                                    coer_arrow coer_refl_ty
                                                      force_unsafe _l_596 _x_599
                                                      _rest_598
                                                | Nil -> Nil)
                                      | eff' -> fun arg k -> Call (eff', arg, k));
                                })
                               (_l_482 false))));
                   effect_clauses =
                     (fun (type a b) (eff : (a, b) eff_internal_effect) :
                          (a -> (b -> _) -> _) ->
                       match eff with
                       | Get ->
                           fun () _l_495 ->
                             Value
                               (fun (_s_496 : intlist) ->
                                 match _s_496 with
                                 | Cons (_x_498, _rest_497) ->
                                     coer_arrow coer_refl_ty force_unsafe _l_495
                                       _x_498 _rest_497
                                 | Nil -> Nil)
                       | eff' -> fun arg k -> Call (eff', arg, k));
                 })
                (_l_482 true))
     in
     _explore_577
       (_tester_42 _m_423, fun (_x_460 : int) -> Value (Cons (_x_460, Nil)))
       (_populate_leafs_432 0 154))

let test_leaf_state = _test_leaf_state_422

let _test_leaf_state_loop_2631 (_m_2632 : int) =
  let rec _maxl_2633 _x_2696 (_x_3792 : intlist) =
    match _x_3792 with
    | Nil -> _x_2696
    | Cons (_x_3794, _xs_3793) -> _maxl_2633 (_max_168 _x_3794 _x_2696) _xs_3793
  in
  let rec _populate_leafs_2641 _x_2697 (_n_2893 : int) =
    if _x_2697 = _n_2893 then Nil
    else Cons (_x_2697 * 3, _populate_leafs_2641 (_x_2697 + 1) _n_2893)
  in
  let ____leafs_2652 = _populate_leafs_2641 0 154 in
  let ____t_2654 = _tester_42 _m_2632 in
  let rec _looper_2738 _x_2739 (_s_2740 : int) =
    if _x_2739 = 0 then _s_2740
    else
      _looper_2738 (_x_2739 - 1)
        (_s_2740
        + _maxl_2633 0
            (let rec _explore_2782 (_x_2702, _k_2784) =
               match _x_2702 with
               | Empty -> Call (Get, (), fun (_y_2765 : int) -> _k_2784 _y_2765)
               | Node (_left_2768, _x_2767, _right_2766) ->
                   let _l_2703 (_y_2769 : bool) =
                     if _y_2769 then
                       _explore_2782
                         ( _left_2768,
                           fun (_b_2814 : int) ->
                             _k_2784 (_op_162 _x_2767 _b_2814) )
                     else
                       _explore_2782
                         ( _right_2766,
                           fun (_b_2834 : int) ->
                             _k_2784 (_op_162 _x_2767 _b_2834) )
                   in
                   _l_2703 true >>= fun _b_2667 ->
                   _l_2703 false >>= fun _b_2668 ->
                   Value (_op_173 (* @ *) _b_2667 _b_2668)
             in
             let rec _explore_2836 (_x_2702, _k_2784) =
               match _x_2702 with
               | Empty -> (
                   fun (_s_2838 : intlist) ->
                     match _s_2838 with
                     | Cons (_x_2840, _rest_2839) ->
                         force_unsafe
                           ((handler
                               {
                                 value_clause =
                                   (fun (_x_2843 : intlist) ->
                                     Value (fun (_ : intlist) -> _x_2843));
                                 effect_clauses =
                                   (fun (type a b)
                                        (eff : (a, b) eff_internal_effect) :
                                        (a -> (b -> _) -> _) ->
                                     match eff with
                                     | Get ->
                                         fun () _l_2844 ->
                                           Value
                                             (fun (_s_2845 : intlist) ->
                                               match _s_2845 with
                                               | Cons (_x_2847, _rest_2846) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l_2844
                                                     _x_2847 _rest_2846
                                               | Nil -> Nil)
                                     | eff' -> fun arg k -> Call (eff', arg, k));
                               })
                              (_k_2784 _x_2840))
                           _rest_2839
                     | Nil -> Nil)
               | Node (_left_2768, _x_2767, _right_2766) ->
                   let _l_2703 (_y_2769 : bool) =
                     if _y_2769 then
                       _explore_2782
                         ( _left_2768,
                           fun (_b_2814 : int) ->
                             _k_2784 (_op_162 _x_2767 _b_2814) )
                     else
                       _explore_2782
                         ( _right_2766,
                           fun (_b_2834 : int) ->
                             _k_2784 (_op_162 _x_2767 _b_2834) )
                   in
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_b_2667 : intlist) ->
                               Value
                                 (force_unsafe
                                    ((handler
                                        {
                                          value_clause =
                                            (fun (_b_2853 : intlist) ->
                                              Value
                                                (fun (_ : intlist) ->
                                                  _op_173 (* @ *) _b_2667
                                                    _b_2853));
                                          effect_clauses =
                                            (fun (type a b)
                                                 (eff :
                                                   (a, b) eff_internal_effect) :
                                                 (a -> (b -> _) -> _) ->
                                              match eff with
                                              | Get ->
                                                  fun () _l_2855 ->
                                                    Value
                                                      (fun (_s_2856 : intlist) ->
                                                        match _s_2856 with
                                                        | Cons
                                                            (_x_2858, _rest_2857)
                                                          ->
                                                            coer_arrow
                                                              coer_refl_ty
                                                              force_unsafe
                                                              _l_2855 _x_2858
                                                              _rest_2857
                                                        | Nil -> Nil)
                                              | eff' ->
                                                  fun arg k ->
                                                    Call (eff', arg, k));
                                        })
                                       (_l_2703 false))));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect)
                                  : (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l_2753 ->
                                     Value
                                       (fun (_s_2754 : intlist) ->
                                         match _s_2754 with
                                         | Cons (_x_2756, _rest_2755) ->
                                             coer_arrow coer_refl_ty
                                               force_unsafe _l_2753 _x_2756
                                               _rest_2755
                                         | Nil -> Nil)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_l_2703 true))
             in
             _explore_2836
               (____t_2654, fun (_x_2669 : int) -> Value (Cons (_x_2669, Nil)))
               ____leafs_2652))
  in
  _looper_2738 100 0

let test_leaf_state_loop = _test_leaf_state_loop_2631

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_4890 (_m_4891 : int) =
  let rec _maxl_4892 _x_4934 (_x_5594 : intlist) =
    match _x_5594 with
    | Nil -> _x_4934
    | Cons (_x_5596, _xs_5595) -> _maxl_4892 (_max_168 _x_5596 _x_4934) _xs_5595
  in
  _maxl_4892 0
    (let rec _explore_4992 (_x_4941, _k_4994) =
       match _x_4941 with
       | Empty -> Call (Get, (), fun (_y_4972 : int) -> _k_4994 _y_4972)
       | Node (_left_4975, _x_4974, _right_4973) ->
           Call
             ( Set,
               _x_4974 * _x_4974,
               fun (_y_5092 : unit) ->
                 let _l_5093 (_y_5097 : bool) =
                   if _y_5097 then
                     _explore_4992
                       ( _left_4975,
                         fun (_b_5099 : int) ->
                           _k_4994 (_op_162 _x_4974 _b_5099) )
                   else
                     _explore_4992
                       ( _right_4973,
                         fun (_b_5102 : int) ->
                           _k_4994 (_op_162 _x_4974 _b_5102) )
                 in
                 _l_5093 true >>= fun _b_5094 ->
                 _l_5093 false >>= fun _b_5096 ->
                 Value (_op_173 (* @ *) _b_5094 _b_5096) )
     in
     let rec _explore_5104 (_x_4941, _k_4994) (_x_0 : int) =
       match _x_4941 with
       | Empty ->
           force_unsafe
             ((handler
                 {
                   value_clause =
                     (fun (_x_5109 : intlist) ->
                       Value (fun (_ : int) -> _x_5109));
                   effect_clauses =
                     (fun (type a b) (eff : (a, b) eff_internal_effect) :
                          (a -> (b -> _) -> _) ->
                       match eff with
                       | Get ->
                           fun () _l_5110 ->
                             Value
                               (fun (_s_5111 : int) ->
                                 coer_arrow coer_refl_ty force_unsafe _l_5110
                                   _s_5111 _s_5111)
                       | Set ->
                           fun _s_5113 _l_5114 ->
                             Value
                               (fun (_ : int) ->
                                 coer_arrow coer_refl_ty force_unsafe _l_5114 ()
                                   _s_5113)
                       | eff' -> fun arg k -> Call (eff', arg, k));
                 })
                (_k_4994 _x_0))
             _x_0
       | Node (_left_4975, _x_4974, _right_4973) ->
           (let _l_5442 (_y_5459 : bool) =
              if _y_5459 then
                _explore_4992
                  ( _left_4975,
                    fun (_b_5461 : int) -> _k_4994 (_op_162 _x_4974 _b_5461) )
              else
                _explore_4992
                  ( _right_4973,
                    fun (_b_5464 : int) -> _k_4994 (_op_162 _x_4974 _b_5464) )
            in
            force_unsafe
              ((handler
                  {
                    value_clause =
                      (fun (_b_5443 : intlist) ->
                        Value
                          (force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_b_5445 : intlist) ->
                                       Value
                                         (fun (_ : int) ->
                                           _op_173 (* @ *) _b_5443 _b_5445));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l_5447 ->
                                             Value
                                               (fun (_s_5448 : int) ->
                                                 coer_arrow coer_refl_ty
                                                   force_unsafe _l_5447 _s_5448
                                                   _s_5448)
                                       | Set ->
                                           fun _s_5450 _l_5451 ->
                                             Value
                                               (fun (_ : int) ->
                                                 coer_arrow coer_refl_ty
                                                   force_unsafe _l_5451 ()
                                                   _s_5450)
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_l_5442 false))));
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | Get ->
                            fun () _l_5453 ->
                              Value
                                (fun (_s_5454 : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _l_5453
                                    _s_5454 _s_5454)
                        | Set ->
                            fun _s_5456 _l_5457 ->
                              Value
                                (fun (_ : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _l_5457
                                    () _s_5456)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  })
                 (_l_5442 true)))
             (_x_4974 * _x_4974)
     in
     _explore_5104
       (_tester_42 _m_4891, fun (_x_4917 : int) -> Value (Cons (_x_4917, Nil)))
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_4890

let _test_leaf_state_update_loop_21688 (_m_21689 : int) =
  let rec _maxl_21690 _x_21744 (_x_22443 : intlist) =
    match _x_22443 with
    | Nil -> _x_21744
    | Cons (_x_22445, _xs_22444) ->
        _maxl_21690 (_max_168 _x_22445 _x_21744) _xs_22444
  in
  let ____t_21698 = _tester_42 _m_21689 in
  let rec _looper_21790 _x_21791 (_s_21792 : int) =
    if _x_21791 = 0 then _s_21792
    else
      _looper_21790 (_x_21791 - 1)
        (_s_21792
        + _maxl_21690 0
            (let rec _explore_21841 (_x_21751, _k_21843) =
               match _x_21751 with
               | Empty ->
                   Call (Get, (), fun (_y_21821 : int) -> _k_21843 _y_21821)
               | Node (_left_21824, _x_21823, _right_21822) ->
                   Call
                     ( Set,
                       _x_21823 * _x_21823,
                       fun (_y_21941 : unit) ->
                         let _l_21942 (_y_21946 : bool) =
                           if _y_21946 then
                             _explore_21841
                               ( _left_21824,
                                 fun (_b_21948 : int) ->
                                   _k_21843 (_op_162 _x_21823 _b_21948) )
                           else
                             _explore_21841
                               ( _right_21822,
                                 fun (_b_21951 : int) ->
                                   _k_21843 (_op_162 _x_21823 _b_21951) )
                         in
                         _l_21942 true >>= fun _b_21943 ->
                         _l_21942 false >>= fun _b_21945 ->
                         Value (_op_173 (* @ *) _b_21943 _b_21945) )
             in
             let rec _explore_21953 (_x_21751, _k_21843) (_x_1 : int) =
               match _x_21751 with
               | Empty ->
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_x_21958 : intlist) ->
                               Value (fun (_ : int) -> _x_21958));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect)
                                  : (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l_21959 ->
                                     Value
                                       (fun (_s_21960 : int) ->
                                         coer_arrow coer_refl_ty force_unsafe
                                           _l_21959 _s_21960 _s_21960)
                               | Set ->
                                   fun _s_21962 _l_21963 ->
                                     Value
                                       (fun (_ : int) ->
                                         coer_arrow coer_refl_ty force_unsafe
                                           _l_21963 () _s_21962)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_k_21843 _x_1))
                     _x_1
               | Node (_left_21824, _x_21823, _right_21822) ->
                   (let _l_22291 (_y_22308 : bool) =
                      if _y_22308 then
                        _explore_21841
                          ( _left_21824,
                            fun (_b_22310 : int) ->
                              _k_21843 (_op_162 _x_21823 _b_22310) )
                      else
                        _explore_21841
                          ( _right_21822,
                            fun (_b_22313 : int) ->
                              _k_21843 (_op_162 _x_21823 _b_22313) )
                    in
                    force_unsafe
                      ((handler
                          {
                            value_clause =
                              (fun (_b_22292 : intlist) ->
                                Value
                                  (force_unsafe
                                     ((handler
                                         {
                                           value_clause =
                                             (fun (_b_22294 : intlist) ->
                                               Value
                                                 (fun (_ : int) ->
                                                   _op_173 (* @ *) _b_22292
                                                     _b_22294));
                                           effect_clauses =
                                             (fun (type a b)
                                                  (eff :
                                                    (a, b) eff_internal_effect)
                                                  : (a -> (b -> _) -> _) ->
                                               match eff with
                                               | Get ->
                                                   fun () _l_22296 ->
                                                     Value
                                                       (fun (_s_22297 : int) ->
                                                         coer_arrow coer_refl_ty
                                                           force_unsafe _l_22296
                                                           _s_22297 _s_22297)
                                               | Set ->
                                                   fun _s_22299 _l_22300 ->
                                                     Value
                                                       (fun (_ : int) ->
                                                         coer_arrow coer_refl_ty
                                                           force_unsafe _l_22300
                                                           () _s_22299)
                                               | eff' ->
                                                   fun arg k ->
                                                     Call (eff', arg, k));
                                         })
                                        (_l_22291 false))));
                            effect_clauses =
                              (fun (type a b) (eff : (a, b) eff_internal_effect)
                                   : (a -> (b -> _) -> _) ->
                                match eff with
                                | Get ->
                                    fun () _l_22302 ->
                                      Value
                                        (fun (_s_22303 : int) ->
                                          coer_arrow coer_refl_ty force_unsafe
                                            _l_22302 _s_22303 _s_22303)
                                | Set ->
                                    fun _s_22305 _l_22306 ->
                                      Value
                                        (fun (_ : int) ->
                                          coer_arrow coer_refl_ty force_unsafe
                                            _l_22306 () _s_22305)
                                | eff' -> fun arg k -> Call (eff', arg, k));
                          })
                         (_l_22291 true)))
                     (_x_21823 * _x_21823)
             in
             _explore_21953
               ( ____t_21698,
                 fun (_x_21715 : int) -> Value (Cons (_x_21715, Nil)) )
               ~-1))
  in
  _looper_21790 100 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_21688

let _test_leaf_state_update_merged_handler_38537 (_m_38538 : int) =
  let rec _maxl_38539 _x_38580 (_x_38777 : intlist) =
    match _x_38777 with
    | Nil -> _x_38580
    | Cons (_x_38779, _xs_38778) ->
        _maxl_38539 (_max_168 _x_38779 _x_38580) _xs_38778
  in
  _maxl_38539 0
    (let rec _explore_38630 (_x_38587, _k_38632) (_x_2 : int) =
       match _x_38587 with
       | Empty -> _k_38632 _x_2 _x_2
       | Node (_left_38608, _x_38607, _right_38606) ->
           (let _l_38762 (_y_38769 : bool) =
              if _y_38769 then
                _explore_38630
                  ( _left_38608,
                    fun (_b_38771 : int) -> _k_38632 (_op_162 _x_38607 _b_38771)
                  )
              else
                _explore_38630
                  ( _right_38606,
                    fun (_b_38774 : int) -> _k_38632 (_op_162 _x_38607 _b_38774)
                  )
            in
            fun (_s_38763 : int) ->
              _op_173 (* @ *) (_l_38762 true _s_38763) (_l_38762 false _s_38763))
             (_x_38607 * _x_38607)
     in
     _explore_38630
       ( _tester_42 _m_38538,
         fun (_x_38573 : int) (_ : int) -> Cons (_x_38573, Nil) )
       ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_38537

let _test_leaf_state_update_merged_handler_loop_38783 (_m_38784 : int) =
  let rec _maxl_38785 _x_38838 (_x_39062 : intlist) =
    match _x_39062 with
    | Nil -> _x_38838
    | Cons (_x_39064, _xs_39063) ->
        _maxl_38785 (_max_168 _x_39064 _x_38838) _xs_39063
  in
  let ____t_38793 = _tester_42 _m_38784 in
  let rec _looper_38866 _x_38867 (_s_38868 : int) =
    if _x_38867 = 0 then _s_38868
    else
      _looper_38866 (_x_38867 - 1)
        (_s_38868
        + _maxl_38785 0
            (let rec _explore_38915 (_x_38845, _k_38917) (_x_3 : int) =
               match _x_38845 with
               | Empty -> _k_38917 _x_3 _x_3
               | Node (_left_38893, _x_38892, _right_38891) ->
                   (let _l_39047 (_y_39054 : bool) =
                      if _y_39054 then
                        _explore_38915
                          ( _left_38893,
                            fun (_b_39056 : int) ->
                              _k_38917 (_op_162 _x_38892 _b_39056) )
                      else
                        _explore_38915
                          ( _right_38891,
                            fun (_b_39059 : int) ->
                              _k_38917 (_op_162 _x_38892 _b_39059) )
                    in
                    fun (_s_39048 : int) ->
                      _op_173
                        (* @ *) (_l_39047 true _s_39048)
                        (_l_39047 false _s_39048))
                     (_x_38892 * _x_38892)
             in
             _explore_38915
               ( ____t_38793,
                 fun (_x_38819 : int) (_ : int) -> Cons (_x_38819, Nil) )
               ~-1))
  in
  _looper_38866 100 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_38783
