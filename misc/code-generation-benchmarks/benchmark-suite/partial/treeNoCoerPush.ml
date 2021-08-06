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

let _max_75 (_a_76 : int) (_b_77 : int) = if _a_76 > _b_77 then _a_76 else _b_77

let max = _max_75

let _effect_max_80 (_m_81 : int) =
  let rec _find_max_127 (_x_102, _k_129) =
    match _x_102 with
    | Empty -> _k_129 0
    | Node (Empty, _x_109, Empty) -> _k_129 _x_109
    | Node (_left_112, _x_111, _right_110) ->
        let _l_103 (_y_116 : bool) =
          if _y_116 then
            _find_max_127
              (_left_112, fun (_next_151 : int) -> _k_129 (_x_111 + _next_151))
          else
            _find_max_127
              (_right_110, fun (_next_154 : int) -> _k_129 (_x_111 + _next_154))
        in
        _max_75 (_l_103 true) (_l_103 false)
  in
  _find_max_127 (_tester_42 _m_81, fun (_x_97 : int) -> _x_97)

let effect_max = _effect_max_80

let _test_max_157 (_m_158 : int) = _effect_max_80 _m_158

let test_max = _test_max_157

let _op_159 (_x_160 : int) (_y_161 : int) = _x_160 - (3 * _y_161)

let op = _op_159

let _max_165 (_a_166 : int) (_b_167 : int) =
  if _a_166 > _b_167 then _a_166 else _b_167

let max = _max_165

type intlist = Nil | Cons of (int * intlist)

let rec _op_170 (* @ *) _x_177 (_ys_179 : intlist) =
  match _x_177 with
  | Nil -> _ys_179
  | Cons (_x_181, _xs_180) -> Cons (_x_181, _op_170 (* @ *) _xs_180 _ys_179)

let _op_170 (* @ *) = _op_170 (* @ *)

let _test_general_184 (_m_185 : int) =
  let rec _maxl_186 _x_216 (_x_288 : intlist) =
    match _x_288 with
    | Nil -> _x_216
    | Cons (_x_290, _xs_289) -> _maxl_186 (_max_165 _x_290 _x_216) _xs_289
  in
  _maxl_186 0
    (let rec _explore_248 (_x_219, _k_250) =
       match _x_219 with
       | Empty -> _k_250 0
       | Node (_left_230, _x_229, _right_228) ->
           let _l_220 (_y_237 : bool) =
             if _y_237 then
               _explore_248
                 ( _left_230,
                   fun (_b_282 : int) -> _k_250 (_op_159 _x_229 _b_282) )
             else
               _explore_248
                 ( _right_228,
                   fun (_b_285 : int) -> _k_250 (_op_159 _x_229 _b_285) )
           in
           _op_170 (* @ *) (_l_220 true) (_l_220 false)
     in
     _explore_248 (_tester_42 _m_185, fun (_x_211 : int) -> Cons (_x_211, Nil)))

let test_general = _test_general_184

let _test_general_loop_294 (_m_295 : int) =
  let rec _maxl_296 _x_338 (_x_435 : intlist) =
    match _x_435 with
    | Nil -> _x_338
    | Cons (_x_437, _xs_436) -> _maxl_296 (_max_165 _x_437 _x_338) _xs_436
  in
  let ____t_304 = _tester_42 _m_295 in
  let rec _looper_358 _x_359 (_s_360 : int) =
    if _x_359 = 0 then _s_360
    else
      _looper_358 (_x_359 - 1)
        (_s_360
        + _maxl_296 0
            (let rec _explore_395 (_x_341, _k_397) =
               match _x_341 with
               | Empty -> _k_397 0
               | Node (_left_377, _x_376, _right_375) ->
                   let _l_342 (_y_384 : bool) =
                     if _y_384 then
                       _explore_395
                         ( _left_377,
                           fun (_b_429 : int) -> _k_397 (_op_159 _x_376 _b_429)
                         )
                     else
                       _explore_395
                         ( _right_375,
                           fun (_b_432 : int) -> _k_397 (_op_159 _x_376 _b_432)
                         )
                   in
                   _op_170 (* @ *) (_l_342 true) (_l_342 false)
             in
             _explore_395 (____t_304, fun (_x_321 : int) -> Cons (_x_321, Nil)))
        )
  in
  _looper_358 100 0

let test_general_loop = _test_general_loop_294

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_441 (_void_442 : float) = match _void_442 with _ -> assert false

let absurd = _absurd_441

let _test_leaf_state_443 (_m_444 : int) =
  let rec _maxl_445 _x_496 (_x_1570 : intlist) =
    match _x_1570 with
    | Nil -> _x_496
    | Cons (_x_1572, _xs_1571) -> _maxl_445 (_max_165 _x_1572 _x_496) _xs_1571
  in
  let rec _populate_leafs_453 _x_497 (_n_671 : int) =
    if _x_497 = _n_671 then Nil
    else Cons (_x_497 * 3, _populate_leafs_453 (_x_497 + 1) _n_671)
  in
  _maxl_445 0
    (let rec _explore_544 (_x_502, _k_546) =
       match _x_502 with
       | Empty -> Call (Get, (), fun (_y_526 : int) -> _k_546 _y_526)
       | Node (_left_529, _x_528, _right_527) ->
           let _l_503 (_y_534 : bool) =
             if _y_534 then
               _explore_544
                 ( _left_529,
                   fun (_b_609 : int) -> _k_546 (_op_159 _x_528 _b_609) )
             else
               _explore_544
                 ( _right_527,
                   fun (_b_612 : int) -> _k_546 (_op_159 _x_528 _b_612) )
           in
           (_l_503 true >>= fun _b_479 -> Value (_op_170 (* @ *) _b_479))
           >>= fun _b_478 ->
           _l_503 false >>= fun _b_480 -> Value (_b_478 _b_480)
     in
     let rec _explore_614 (_x_502, _k_546) =
       match _x_502 with
       | Empty -> (
           fun (_s_616 : intlist) ->
             match _s_616 with
             | Cons (_x_618, _rest_617) ->
                 force_unsafe
                   ((handler
                       {
                         value_clause =
                           (fun (_x_621 : intlist) ->
                             Value (fun (_ : intlist) -> _x_621));
                         effect_clauses =
                           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                (a -> (b -> _) -> _) ->
                             match eff with
                             | Get ->
                                 fun () _l_622 ->
                                   Value
                                     (fun (_s_623 : intlist) ->
                                       match _s_623 with
                                       | Cons (_x_625, _rest_624) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_622 _x_625 _rest_624
                                       | Nil -> Nil)
                             | eff' -> fun arg k -> Call (eff', arg, k));
                       })
                      (_k_546 _x_618))
                   _rest_617
             | Nil -> Nil)
       | Node (_left_529, _x_528, _right_527) ->
           let _l_503 (_y_534 : bool) =
             if _y_534 then
               _explore_544
                 ( _left_529,
                   fun (_b_609 : int) -> _k_546 (_op_159 _x_528 _b_609) )
             else
               _explore_544
                 ( _right_527,
                   fun (_b_612 : int) -> _k_546 (_op_159 _x_528 _b_612) )
           in
           force_unsafe
             ((handler
                 {
                   value_clause =
                     (fun (_b_479 : intlist) ->
                       Value
                         (force_unsafe
                            ((handler
                                {
                                  value_clause =
                                    (fun (_b_631 : intlist) ->
                                      Value
                                        (fun (_ : intlist) ->
                                          _op_170 (* @ *) _b_479 _b_631));
                                  effect_clauses =
                                    (fun (type a b)
                                         (eff : (a, b) eff_internal_effect) :
                                         (a -> (b -> _) -> _) ->
                                      match eff with
                                      | Get ->
                                          fun () _l_633 ->
                                            Value
                                              (fun (_s_634 : intlist) ->
                                                match _s_634 with
                                                | Cons (_x_636, _rest_635) ->
                                                    coer_arrow coer_refl_ty
                                                      force_unsafe _l_633 _x_636
                                                      _rest_635
                                                | Nil -> Nil)
                                      | eff' -> fun arg k -> Call (eff', arg, k));
                                })
                               (_l_503 false))));
                   effect_clauses =
                     (fun (type a b) (eff : (a, b) eff_internal_effect) :
                          (a -> (b -> _) -> _) ->
                       match eff with
                       | Get ->
                           fun () _l_516 ->
                             Value
                               (fun (_s_517 : intlist) ->
                                 match _s_517 with
                                 | Cons (_x_519, _rest_518) ->
                                     coer_arrow coer_refl_ty force_unsafe _l_516
                                       _x_519 _rest_518
                                 | Nil -> Nil)
                       | eff' -> fun arg k -> Call (eff', arg, k));
                 })
                (_l_503 true))
     in
     _explore_614
       (_tester_42 _m_444, fun (_x_481 : int) -> Value (Cons (_x_481, Nil)))
       (_populate_leafs_453 0 154))

let test_leaf_state = _test_leaf_state_443

let _test_leaf_state_loop_2668 (_m_2669 : int) =
  let rec _maxl_2670 _x_2733 (_x_3845 : intlist) =
    match _x_3845 with
    | Nil -> _x_2733
    | Cons (_x_3847, _xs_3846) -> _maxl_2670 (_max_165 _x_3847 _x_2733) _xs_3846
  in
  let rec _populate_leafs_2678 _x_2734 (_n_2946 : int) =
    if _x_2734 = _n_2946 then Nil
    else Cons (_x_2734 * 3, _populate_leafs_2678 (_x_2734 + 1) _n_2946)
  in
  let ____leafs_2689 = _populate_leafs_2678 0 154 in
  let ____t_2691 = _tester_42 _m_2669 in
  let rec _looper_2775 _x_2776 (_s_2777 : int) =
    if _x_2776 = 0 then _s_2777
    else
      _looper_2775 (_x_2776 - 1)
        (_s_2777
        + _maxl_2670 0
            (let rec _explore_2819 (_x_2739, _k_2821) =
               match _x_2739 with
               | Empty -> Call (Get, (), fun (_y_2801 : int) -> _k_2821 _y_2801)
               | Node (_left_2804, _x_2803, _right_2802) ->
                   let _l_2740 (_y_2809 : bool) =
                     if _y_2809 then
                       _explore_2819
                         ( _left_2804,
                           fun (_b_2884 : int) ->
                             _k_2821 (_op_159 _x_2803 _b_2884) )
                     else
                       _explore_2819
                         ( _right_2802,
                           fun (_b_2887 : int) ->
                             _k_2821 (_op_159 _x_2803 _b_2887) )
                   in
                   ( _l_2740 true >>= fun _b_2704 ->
                     Value (_op_170 (* @ *) _b_2704) )
                   >>= fun _b_2703 ->
                   _l_2740 false >>= fun _b_2705 -> Value (_b_2703 _b_2705)
             in
             let rec _explore_2889 (_x_2739, _k_2821) =
               match _x_2739 with
               | Empty -> (
                   fun (_s_2891 : intlist) ->
                     match _s_2891 with
                     | Cons (_x_2893, _rest_2892) ->
                         force_unsafe
                           ((handler
                               {
                                 value_clause =
                                   (fun (_x_2896 : intlist) ->
                                     Value (fun (_ : intlist) -> _x_2896));
                                 effect_clauses =
                                   (fun (type a b)
                                        (eff : (a, b) eff_internal_effect) :
                                        (a -> (b -> _) -> _) ->
                                     match eff with
                                     | Get ->
                                         fun () _l_2897 ->
                                           Value
                                             (fun (_s_2898 : intlist) ->
                                               match _s_2898 with
                                               | Cons (_x_2900, _rest_2899) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l_2897
                                                     _x_2900 _rest_2899
                                               | Nil -> Nil)
                                     | eff' -> fun arg k -> Call (eff', arg, k));
                               })
                              (_k_2821 _x_2893))
                           _rest_2892
                     | Nil -> Nil)
               | Node (_left_2804, _x_2803, _right_2802) ->
                   let _l_2740 (_y_2809 : bool) =
                     if _y_2809 then
                       _explore_2819
                         ( _left_2804,
                           fun (_b_2884 : int) ->
                             _k_2821 (_op_159 _x_2803 _b_2884) )
                     else
                       _explore_2819
                         ( _right_2802,
                           fun (_b_2887 : int) ->
                             _k_2821 (_op_159 _x_2803 _b_2887) )
                   in
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_b_2704 : intlist) ->
                               Value
                                 (force_unsafe
                                    ((handler
                                        {
                                          value_clause =
                                            (fun (_b_2906 : intlist) ->
                                              Value
                                                (fun (_ : intlist) ->
                                                  _op_170 (* @ *) _b_2704
                                                    _b_2906));
                                          effect_clauses =
                                            (fun (type a b)
                                                 (eff :
                                                   (a, b) eff_internal_effect) :
                                                 (a -> (b -> _) -> _) ->
                                              match eff with
                                              | Get ->
                                                  fun () _l_2908 ->
                                                    Value
                                                      (fun (_s_2909 : intlist) ->
                                                        match _s_2909 with
                                                        | Cons
                                                            (_x_2911, _rest_2910)
                                                          ->
                                                            coer_arrow
                                                              coer_refl_ty
                                                              force_unsafe
                                                              _l_2908 _x_2911
                                                              _rest_2910
                                                        | Nil -> Nil)
                                              | eff' ->
                                                  fun arg k ->
                                                    Call (eff', arg, k));
                                        })
                                       (_l_2740 false))));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect)
                                  : (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l_2787 ->
                                     Value
                                       (fun (_s_2788 : intlist) ->
                                         match _s_2788 with
                                         | Cons (_x_2790, _rest_2789) ->
                                             coer_arrow coer_refl_ty
                                               force_unsafe _l_2787 _x_2790
                                               _rest_2789
                                         | Nil -> Nil)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_l_2740 true))
             in
             _explore_2889
               (____t_2691, fun (_x_2706 : int) -> Value (Cons (_x_2706, Nil)))
               ____leafs_2689))
  in
  _looper_2775 100 0

let test_leaf_state_loop = _test_leaf_state_loop_2668

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_4943 (_m_4944 : int) =
  let rec _maxl_4945 _x_4987 (_x_5634 : intlist) =
    match _x_5634 with
    | Nil -> _x_4987
    | Cons (_x_5636, _xs_5635) -> _maxl_4945 (_max_165 _x_5636 _x_4987) _xs_5635
  in
  _maxl_4945 0
    (let rec _explore_5045 (_x_4994, _k_5047) =
       match _x_4994 with
       | Empty -> Call (Get, (), fun (_y_5024 : int) -> _k_5047 _y_5024)
       | Node (_left_5027, _x_5026, _right_5025) ->
           Call
             ( Set,
               _x_5026 * _x_5026,
               fun (_y_5132 : unit) ->
                 let _l_5133 (_y_5137 : bool) =
                   if _y_5137 then
                     _explore_5045
                       ( _left_5027,
                         fun (_b_5139 : int) ->
                           _k_5047 (_op_159 _x_5026 _b_5139) )
                   else
                     _explore_5045
                       ( _right_5025,
                         fun (_b_5142 : int) ->
                           _k_5047 (_op_159 _x_5026 _b_5142) )
                 in
                 ( _l_5133 true >>= fun _b_5136 ->
                   Value (_op_170 (* @ *) _b_5136) )
                 >>= fun _b_5134 ->
                 _l_5133 false >>= fun _b_5135 -> Value (_b_5134 _b_5135) )
     in
     let rec _explore_5144 (_x_4994, _k_5047) (_x_0 : int) =
       match _x_4994 with
       | Empty ->
           force_unsafe
             ((handler
                 {
                   value_clause =
                     (fun (_x_5149 : intlist) ->
                       Value (fun (_ : int) -> _x_5149));
                   effect_clauses =
                     (fun (type a b) (eff : (a, b) eff_internal_effect) :
                          (a -> (b -> _) -> _) ->
                       match eff with
                       | Get ->
                           fun () _l_5150 ->
                             Value
                               (fun (_s_5151 : int) ->
                                 coer_arrow coer_refl_ty force_unsafe _l_5150
                                   _s_5151 _s_5151)
                       | Set ->
                           fun _s_5153 _l_5154 ->
                             Value
                               (fun (_ : int) ->
                                 coer_arrow coer_refl_ty force_unsafe _l_5154 ()
                                   _s_5153)
                       | eff' -> fun arg k -> Call (eff', arg, k));
                 })
                (_k_5047 _x_0))
             _x_0
       | Node (_left_5027, _x_5026, _right_5025) ->
           (let _l_5482 (_y_5499 : bool) =
              if _y_5499 then
                _explore_5045
                  ( _left_5027,
                    fun (_b_5501 : int) -> _k_5047 (_op_159 _x_5026 _b_5501) )
              else
                _explore_5045
                  ( _right_5025,
                    fun (_b_5504 : int) -> _k_5047 (_op_159 _x_5026 _b_5504) )
            in
            force_unsafe
              ((handler
                  {
                    value_clause =
                      (fun (_b_5483 : intlist) ->
                        Value
                          (force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_b_5485 : intlist) ->
                                       Value
                                         (fun (_ : int) ->
                                           _op_170 (* @ *) _b_5483 _b_5485));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l_5487 ->
                                             Value
                                               (fun (_s_5488 : int) ->
                                                 coer_arrow coer_refl_ty
                                                   force_unsafe _l_5487 _s_5488
                                                   _s_5488)
                                       | Set ->
                                           fun _s_5490 _l_5491 ->
                                             Value
                                               (fun (_ : int) ->
                                                 coer_arrow coer_refl_ty
                                                   force_unsafe _l_5491 ()
                                                   _s_5490)
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_l_5482 false))));
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | Get ->
                            fun () _l_5493 ->
                              Value
                                (fun (_s_5494 : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _l_5493
                                    _s_5494 _s_5494)
                        | Set ->
                            fun _s_5496 _l_5497 ->
                              Value
                                (fun (_ : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _l_5497
                                    () _s_5496)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  })
                 (_l_5482 true)))
             (_x_5026 * _x_5026)
     in
     _explore_5144
       (_tester_42 _m_4944, fun (_x_4970 : int) -> Value (Cons (_x_4970, Nil)))
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_4943

let _test_leaf_state_update_loop_21728 (_m_21729 : int) =
  let rec _maxl_21730 _x_21784 (_x_22470 : intlist) =
    match _x_22470 with
    | Nil -> _x_21784
    | Cons (_x_22472, _xs_22471) ->
        _maxl_21730 (_max_165 _x_22472 _x_21784) _xs_22471
  in
  let ____t_21738 = _tester_42 _m_21729 in
  let rec _looper_21830 _x_21831 (_s_21832 : int) =
    if _x_21831 = 0 then _s_21832
    else
      _looper_21830 (_x_21831 - 1)
        (_s_21832
        + _maxl_21730 0
            (let rec _explore_21881 (_x_21791, _k_21883) =
               match _x_21791 with
               | Empty ->
                   Call (Get, (), fun (_y_21860 : int) -> _k_21883 _y_21860)
               | Node (_left_21863, _x_21862, _right_21861) ->
                   Call
                     ( Set,
                       _x_21862 * _x_21862,
                       fun (_y_21968 : unit) ->
                         let _l_21969 (_y_21973 : bool) =
                           if _y_21973 then
                             _explore_21881
                               ( _left_21863,
                                 fun (_b_21975 : int) ->
                                   _k_21883 (_op_159 _x_21862 _b_21975) )
                           else
                             _explore_21881
                               ( _right_21861,
                                 fun (_b_21978 : int) ->
                                   _k_21883 (_op_159 _x_21862 _b_21978) )
                         in
                         ( _l_21969 true >>= fun _b_21972 ->
                           Value (_op_170 (* @ *) _b_21972) )
                         >>= fun _b_21970 ->
                         _l_21969 false >>= fun _b_21971 ->
                         Value (_b_21970 _b_21971) )
             in
             let rec _explore_21980 (_x_21791, _k_21883) (_x_1 : int) =
               match _x_21791 with
               | Empty ->
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_x_21985 : intlist) ->
                               Value (fun (_ : int) -> _x_21985));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect)
                                  : (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l_21986 ->
                                     Value
                                       (fun (_s_21987 : int) ->
                                         coer_arrow coer_refl_ty force_unsafe
                                           _l_21986 _s_21987 _s_21987)
                               | Set ->
                                   fun _s_21989 _l_21990 ->
                                     Value
                                       (fun (_ : int) ->
                                         coer_arrow coer_refl_ty force_unsafe
                                           _l_21990 () _s_21989)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_k_21883 _x_1))
                     _x_1
               | Node (_left_21863, _x_21862, _right_21861) ->
                   (let _l_22318 (_y_22335 : bool) =
                      if _y_22335 then
                        _explore_21881
                          ( _left_21863,
                            fun (_b_22337 : int) ->
                              _k_21883 (_op_159 _x_21862 _b_22337) )
                      else
                        _explore_21881
                          ( _right_21861,
                            fun (_b_22340 : int) ->
                              _k_21883 (_op_159 _x_21862 _b_22340) )
                    in
                    force_unsafe
                      ((handler
                          {
                            value_clause =
                              (fun (_b_22319 : intlist) ->
                                Value
                                  (force_unsafe
                                     ((handler
                                         {
                                           value_clause =
                                             (fun (_b_22321 : intlist) ->
                                               Value
                                                 (fun (_ : int) ->
                                                   _op_170 (* @ *) _b_22319
                                                     _b_22321));
                                           effect_clauses =
                                             (fun (type a b)
                                                  (eff :
                                                    (a, b) eff_internal_effect)
                                                  : (a -> (b -> _) -> _) ->
                                               match eff with
                                               | Get ->
                                                   fun () _l_22323 ->
                                                     Value
                                                       (fun (_s_22324 : int) ->
                                                         coer_arrow coer_refl_ty
                                                           force_unsafe _l_22323
                                                           _s_22324 _s_22324)
                                               | Set ->
                                                   fun _s_22326 _l_22327 ->
                                                     Value
                                                       (fun (_ : int) ->
                                                         coer_arrow coer_refl_ty
                                                           force_unsafe _l_22327
                                                           () _s_22326)
                                               | eff' ->
                                                   fun arg k ->
                                                     Call (eff', arg, k));
                                         })
                                        (_l_22318 false))));
                            effect_clauses =
                              (fun (type a b) (eff : (a, b) eff_internal_effect)
                                   : (a -> (b -> _) -> _) ->
                                match eff with
                                | Get ->
                                    fun () _l_22329 ->
                                      Value
                                        (fun (_s_22330 : int) ->
                                          coer_arrow coer_refl_ty force_unsafe
                                            _l_22329 _s_22330 _s_22330)
                                | Set ->
                                    fun _s_22332 _l_22333 ->
                                      Value
                                        (fun (_ : int) ->
                                          coer_arrow coer_refl_ty force_unsafe
                                            _l_22333 () _s_22332)
                                | eff' -> fun arg k -> Call (eff', arg, k));
                          })
                         (_l_22318 true)))
                     (_x_21862 * _x_21862)
             in
             _explore_21980
               ( ____t_21738,
                 fun (_x_21755 : int) -> Value (Cons (_x_21755, Nil)) )
               ~-1))
  in
  _looper_21830 100 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_21728

let _test_leaf_state_update_merged_handler_38564 (_m_38565 : int) =
  let rec _maxl_38566 _x_38607 (_x_38784 : intlist) =
    match _x_38784 with
    | Nil -> _x_38607
    | Cons (_x_38786, _xs_38785) ->
        _maxl_38566 (_max_165 _x_38786 _x_38607) _xs_38785
  in
  _maxl_38566 0
    (let rec _explore_38656 (_x_38614, _k_38658) (_x_2 : int) =
       match _x_38614 with
       | Empty -> _k_38658 _x_2 _x_2
       | Node (_left_38634, _x_38633, _right_38632) ->
           (let _l_38769 (_y_38776 : bool) =
              if _y_38776 then
                _explore_38656
                  ( _left_38634,
                    fun (_b_38778 : int) -> _k_38658 (_op_159 _x_38633 _b_38778)
                  )
              else
                _explore_38656
                  ( _right_38632,
                    fun (_b_38781 : int) -> _k_38658 (_op_159 _x_38633 _b_38781)
                  )
            in
            fun (_s_38770 : int) ->
              _op_170 (* @ *) (_l_38769 true _s_38770) (_l_38769 false _s_38770))
             (_x_38633 * _x_38633)
     in
     _explore_38656
       ( _tester_42 _m_38565,
         fun (_x_38600 : int) (_ : int) -> Cons (_x_38600, Nil) )
       ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_38564

let _test_leaf_state_update_merged_handler_loop_38790 (_m_38791 : int) =
  let rec _maxl_38792 _x_38845 (_x_39049 : intlist) =
    match _x_39049 with
    | Nil -> _x_38845
    | Cons (_x_39051, _xs_39050) ->
        _maxl_38792 (_max_165 _x_39051 _x_38845) _xs_39050
  in
  let ____t_38800 = _tester_42 _m_38791 in
  let rec _looper_38873 _x_38874 (_s_38875 : int) =
    if _x_38874 = 0 then _s_38875
    else
      _looper_38873 (_x_38874 - 1)
        (_s_38875
        + _maxl_38792 0
            (let rec _explore_38921 (_x_38852, _k_38923) (_x_3 : int) =
               match _x_38852 with
               | Empty -> _k_38923 _x_3 _x_3
               | Node (_left_38899, _x_38898, _right_38897) ->
                   (let _l_39034 (_y_39041 : bool) =
                      if _y_39041 then
                        _explore_38921
                          ( _left_38899,
                            fun (_b_39043 : int) ->
                              _k_38923 (_op_159 _x_38898 _b_39043) )
                      else
                        _explore_38921
                          ( _right_38897,
                            fun (_b_39046 : int) ->
                              _k_38923 (_op_159 _x_38898 _b_39046) )
                    in
                    fun (_s_39035 : int) ->
                      _op_170
                        (* @ *) (_l_39034 true _s_39035)
                        (_l_39034 false _s_39035))
                     (_x_38898 * _x_38898)
             in
             _explore_38921
               ( ____t_38800,
                 fun (_x_38826 : int) (_ : int) -> Cons (_x_38826, Nil) )
               ~-1))
  in
  _looper_38873 100 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_38790
