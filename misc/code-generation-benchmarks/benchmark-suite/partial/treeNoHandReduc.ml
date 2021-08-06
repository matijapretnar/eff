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
  let rec _find_max_95 _x_115 =
    match _x_115 with
    | Empty -> Value 0
    | Node (Empty, _x_123, Empty) -> Value _x_123
    | Node (_left_126, _x_125, _right_124) ->
        Call
          ( Choose,
            (),
            fun (_y_127 : bool) ->
              (if _y_127 then _find_max_95 _left_126
              else _find_max_95 _right_124)
              >>= fun _next_128 -> Value (_x_125 + _next_128) )
  in
  let rec _find_max_130 _x_115 =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x_110 : int) -> Value _x_110);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Choose ->
                    fun () _l_116 ->
                      Value
                        (_max_88
                           (coer_arrow coer_refl_ty force_unsafe _l_116 true)
                           (coer_arrow coer_refl_ty force_unsafe _l_116 false))
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (match _x_115 with
         | Empty -> Value 0
         | Node (Empty, _x_123, Empty) -> Value _x_123
         | Node (_left_126, _x_125, _right_124) ->
             Call
               ( Choose,
                 (),
                 fun (_y_127 : bool) ->
                   (if _y_127 then _find_max_95 _left_126
                   else _find_max_95 _right_124)
                   >>= fun _next_128 -> Value (_x_125 + _next_128) )))
  in
  _find_max_130 (_tester_42 _m_94)

let effect_max = _effect_max_93

let _test_max_131 (_m_132 : int) = _effect_max_93 _m_132

let test_max = _test_max_131

let _op_133 (_x_134 : int) (_y_135 : int) = _x_134 - (3 * _y_135)

let op = _op_133

let _max_139 (_a_140 : int) (_b_141 : int) =
  if _a_140 > _b_141 then _a_140 else _b_141

let max = _max_139

type intlist = Nil | Cons of (int * intlist)

let rec _op_144 (* @ *) _x_151 (_ys_153 : intlist) =
  match _x_151 with
  | Nil -> _ys_153
  | Cons (_x_155, _xs_154) -> Cons (_x_155, _op_144 (* @ *) _xs_154 _ys_153)

let _op_144 (* @ *) = _op_144 (* @ *)

let _test_general_158 (_m_159 : int) =
  let rec _maxl_160 _x_190 (_x_218 : intlist) =
    match _x_218 with
    | Nil -> _x_190
    | Cons (_x_220, _xs_219) -> _maxl_160 (_max_139 _x_220 _x_190) _xs_219
  in
  let rec _explore_169 _x_193 =
    match _x_193 with
    | Empty -> Value 0
    | Node (_left_209, _x_208, _right_207) ->
        Call
          ( Choose,
            (),
            fun (_y_210 : bool) ->
              (if _y_210 then
               _explore_169 _left_209 >>= fun _b_213 ->
               Value (_op_133 _x_208 _b_213)
              else
                _explore_169 _right_207 >>= fun _b_215 ->
                Value (_op_133 _x_208 _b_215))
              >>= fun _next_211 -> Value _next_211 )
  in
  _maxl_160 0
    (let rec _explore_216 _x_193 =
       force_unsafe
         ((handler
             {
               value_clause = (fun (_x_185 : int) -> Value (Cons (_x_185, Nil)));
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | Choose ->
                       fun () _l_194 ->
                         Value
                           (_op_144 (* @ *)
                              (coer_arrow coer_refl_ty force_unsafe _l_194 true)
                              (coer_arrow coer_refl_ty force_unsafe _l_194 false))
                   | eff' -> fun arg k -> Call (eff', arg, k));
             })
            (match _x_193 with
            | Empty -> Value 0
            | Node (_left_209, _x_208, _right_207) ->
                Call
                  ( Choose,
                    (),
                    fun (_y_210 : bool) ->
                      (if _y_210 then
                       _explore_169 _left_209 >>= fun _b_213 ->
                       Value (_op_133 _x_208 _b_213)
                      else
                        _explore_169 _right_207 >>= fun _b_215 ->
                        Value (_op_133 _x_208 _b_215))
                      >>= fun _next_211 -> Value _next_211 )))
     in
     _explore_216 (_tester_42 _m_159))

let test_general = _test_general_158

let _test_general_loop_225 (_m_226 : int) =
  let rec _maxl_227 _x_269 (_x_322 : intlist) =
    match _x_322 with
    | Nil -> _x_269
    | Cons (_x_324, _xs_323) -> _maxl_227 (_max_139 _x_324 _x_269) _xs_323
  in
  let ____t_235 = _tester_42 _m_226 in
  let rec _explore_236 _x_272 =
    match _x_272 with
    | Empty -> Value 0
    | Node (_left_313, _x_312, _right_311) ->
        Call
          ( Choose,
            (),
            fun (_y_314 : bool) ->
              (if _y_314 then
               _explore_236 _left_313 >>= fun _b_317 ->
               Value (_op_133 _x_312 _b_317)
              else
                _explore_236 _right_311 >>= fun _b_319 ->
                Value (_op_133 _x_312 _b_319))
              >>= fun _next_315 -> Value _next_315 )
  in
  let rec _looper_289 _x_290 (_s_291 : int) =
    if _x_290 = 0 then _s_291
    else
      _looper_289 (_x_290 - 1)
        (_s_291
        + _maxl_227 0
            (let rec _explore_320 _x_272 =
               force_unsafe
                 ((handler
                     {
                       value_clause =
                         (fun (_x_252 : int) -> Value (Cons (_x_252, Nil)));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Choose ->
                               fun () _l_273 ->
                                 Value
                                   (_op_144 (* @ *)
                                      (coer_arrow coer_refl_ty force_unsafe
                                         _l_273 true)
                                      (coer_arrow coer_refl_ty force_unsafe
                                         _l_273 false))
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     })
                    (match _x_272 with
                    | Empty -> Value 0
                    | Node (_left_313, _x_312, _right_311) ->
                        Call
                          ( Choose,
                            (),
                            fun (_y_314 : bool) ->
                              (if _y_314 then
                               _explore_236 _left_313 >>= fun _b_317 ->
                               Value (_op_133 _x_312 _b_317)
                              else
                                _explore_236 _right_311 >>= fun _b_319 ->
                                Value (_op_133 _x_312 _b_319))
                              >>= fun _next_315 -> Value _next_315 )))
             in
             _explore_320 ____t_235))
  in
  _looper_289 100 0

let test_general_loop = _test_general_loop_225

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_329 (_void_330 : float) = match _void_330 with _ -> assert false

let absurd = _absurd_329

let _test_leaf_state_331 (_m_332 : int) =
  let rec _maxl_333 _x_384 (_x_436 : intlist) =
    match _x_436 with
    | Nil -> _x_384
    | Cons (_x_438, _xs_437) -> _maxl_333 (_max_139 _x_438 _x_384) _xs_437
  in
  let rec _populate_leafs_341 _x_385 (_n_425 : int) =
    if _x_385 = _n_425 then Nil
    else Cons (_x_385 * 3, _populate_leafs_341 (_x_385 + 1) _n_425)
  in
  let rec _explore_355 _x_390 =
    match _x_390 with
    | Empty -> Call (Get, (), fun (_y_415 : int) -> Value _y_415)
    | Node (_left_418, _x_417, _right_416) ->
        Call
          ( Choose,
            (),
            fun (_y_419 : bool) ->
              _explore_355 (if _y_419 then _left_418 else _right_416)
              >>= fun _b_422 -> Value (_op_133 _x_417 _b_422) )
  in
  _maxl_333 0
    (force_unsafe
       ((handler
           {
             value_clause =
               (fun (_x_403 : intlist) -> Value (fun (_ : intlist) -> _x_403));
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Get ->
                     fun () _l_404 ->
                       Value
                         (fun (_s_405 : intlist) ->
                           match _s_405 with
                           | Cons (_x_407, _rest_406) ->
                               coer_arrow coer_refl_ty force_unsafe _l_404
                                 _x_407 _rest_406
                           | Nil -> Nil)
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (let rec _explore_423 _x_390 =
             (handler
                {
                  value_clause =
                    (fun (_x_369 : int) -> Value (Cons (_x_369, Nil)));
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | Choose ->
                          fun () _l_391 ->
                            _l_391 true >>= fun _b_367 ->
                            _l_391 false >>= fun _b_368 ->
                            Value (_op_144 (* @ *) _b_367 _b_368)
                      | eff' -> fun arg k -> Call (eff', arg, k));
                })
               (match _x_390 with
               | Empty -> Call (Get, (), fun (_y_415 : int) -> Value _y_415)
               | Node (_left_418, _x_417, _right_416) ->
                   Call
                     ( Choose,
                       (),
                       fun (_y_419 : bool) ->
                         _explore_355 (if _y_419 then _left_418 else _right_416)
                         >>= fun _b_422 -> Value (_op_133 _x_417 _b_422) ))
           in
           _explore_423 (_tester_42 _m_332)))
       (_populate_leafs_341 0 154))

let test_leaf_state = _test_leaf_state_331

let _test_leaf_state_loop_444 (_m_445 : int) =
  let rec _maxl_446 _x_509 (_x_599 : intlist) =
    match _x_599 with
    | Nil -> _x_509
    | Cons (_x_601, _xs_600) -> _maxl_446 (_max_139 _x_601 _x_509) _xs_600
  in
  let rec _populate_leafs_454 _x_510 (_n_588 : int) =
    if _x_510 = _n_588 then Nil
    else Cons (_x_510 * 3, _populate_leafs_454 (_x_510 + 1) _n_588)
  in
  let ____leafs_465 = _populate_leafs_454 0 154 in
  let ____t_467 = _tester_42 _m_445 in
  let rec _explore_468 _x_515 =
    match _x_515 with
    | Empty -> Call (Get, (), fun (_y_578 : int) -> Value _y_578)
    | Node (_left_581, _x_580, _right_579) ->
        Call
          ( Choose,
            (),
            fun (_y_582 : bool) ->
              _explore_468 (if _y_582 then _left_581 else _right_579)
              >>= fun _b_585 -> Value (_op_133 _x_580 _b_585) )
  in
  let rec _looper_551 _x_552 (_s_553 : int) =
    if _x_552 = 0 then _s_553
    else
      _looper_551 (_x_552 - 1)
        (_s_553
        + _maxl_446 0
            (force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_565 : intlist) ->
                         Value (fun (_ : intlist) -> _x_565));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_566 ->
                               Value
                                 (fun (_s_567 : intlist) ->
                                   match _s_567 with
                                   | Cons (_x_569, _rest_568) ->
                                       coer_arrow coer_refl_ty force_unsafe
                                         _l_566 _x_569 _rest_568
                                   | Nil -> Nil)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (let rec _explore_586 _x_515 =
                     (handler
                        {
                          value_clause =
                            (fun (_x_482 : int) -> Value (Cons (_x_482, Nil)));
                          effect_clauses =
                            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                 (a -> (b -> _) -> _) ->
                              match eff with
                              | Choose ->
                                  fun () _l_516 ->
                                    _l_516 true >>= fun _b_480 ->
                                    _l_516 false >>= fun _b_481 ->
                                    Value (_op_144 (* @ *) _b_480 _b_481)
                              | eff' -> fun arg k -> Call (eff', arg, k));
                        })
                       (match _x_515 with
                       | Empty ->
                           Call (Get, (), fun (_y_578 : int) -> Value _y_578)
                       | Node (_left_581, _x_580, _right_579) ->
                           Call
                             ( Choose,
                               (),
                               fun (_y_582 : bool) ->
                                 _explore_468
                                   (if _y_582 then _left_581 else _right_579)
                                 >>= fun _b_585 -> Value (_op_133 _x_580 _b_585)
                             ))
                   in
                   _explore_586 ____t_467))
               ____leafs_465))
  in
  _looper_551 100 0

let test_leaf_state_loop = _test_leaf_state_loop_444

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_607 (_m_608 : int) =
  let rec _maxl_609 _x_651 (_x_702 : intlist) =
    match _x_702 with
    | Nil -> _x_651
    | Cons (_x_704, _xs_703) -> _maxl_609 (_max_139 _x_704 _x_651) _xs_703
  in
  let rec _explore_618 _x_658 =
    match _x_658 with
    | Empty -> Call (Get, (), fun (_y_689 : int) -> Value _y_689)
    | Node (_left_692, _x_691, _right_690) ->
        Call
          ( Set,
            _x_691 * _x_691,
            fun (_y_695 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_696 : bool) ->
                    _explore_618 (if _y_696 then _left_692 else _right_690)
                    >>= fun _b_699 -> Value (_op_133 _x_691 _b_699) ) )
  in
  _maxl_609 0
    (force_unsafe
       ((handler
           {
             value_clause =
               (fun (_x_674 : intlist) -> Value (fun (_ : int) -> _x_674));
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Get ->
                     fun () _l_675 ->
                       Value
                         (fun (_s_676 : int) ->
                           coer_arrow coer_refl_ty force_unsafe _l_675 _s_676
                             _s_676)
                 | Set ->
                     fun _s_678 _l_679 ->
                       Value
                         (fun (_ : int) ->
                           coer_arrow coer_refl_ty force_unsafe _l_679 () _s_678)
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (let rec _explore_700 _x_658 =
             (handler
                {
                  value_clause =
                    (fun (_x_634 : int) -> Value (Cons (_x_634, Nil)));
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | Choose ->
                          fun () _l_659 ->
                            _l_659 true >>= fun _b_632 ->
                            _l_659 false >>= fun _b_633 ->
                            Value (_op_144 (* @ *) _b_632 _b_633)
                      | eff' -> fun arg k -> Call (eff', arg, k));
                })
               (match _x_658 with
               | Empty -> Call (Get, (), fun (_y_689 : int) -> Value _y_689)
               | Node (_left_692, _x_691, _right_690) ->
                   Call
                     ( Set,
                       _x_691 * _x_691,
                       fun (_y_695 : unit) ->
                         Call
                           ( Choose,
                             (),
                             fun (_y_696 : bool) ->
                               _explore_618
                                 (if _y_696 then _left_692 else _right_690)
                               >>= fun _b_699 -> Value (_op_133 _x_691 _b_699)
                           ) ))
           in
           _explore_700 (_tester_42 _m_608)))
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_607

let _test_leaf_state_update_loop_709 (_m_710 : int) =
  let rec _maxl_711 _x_765 (_x_855 : intlist) =
    match _x_855 with
    | Nil -> _x_765
    | Cons (_x_857, _xs_856) -> _maxl_711 (_max_139 _x_857 _x_765) _xs_856
  in
  let ____t_719 = _tester_42 _m_710 in
  let rec _explore_720 _x_772 =
    match _x_772 with
    | Empty -> Call (Get, (), fun (_y_842 : int) -> Value _y_842)
    | Node (_left_845, _x_844, _right_843) ->
        Call
          ( Set,
            _x_844 * _x_844,
            fun (_y_848 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_849 : bool) ->
                    _explore_720 (if _y_849 then _left_845 else _right_843)
                    >>= fun _b_852 -> Value (_op_133 _x_844 _b_852) ) )
  in
  let rec _looper_811 _x_812 (_s_813 : int) =
    if _x_812 = 0 then _s_813
    else
      _looper_811 (_x_812 - 1)
        (_s_813
        + _maxl_711 0
            (force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_826 : intlist) ->
                         Value (fun (_ : int) -> _x_826));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_827 ->
                               Value
                                 (fun (_s_828 : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_827
                                     _s_828 _s_828)
                         | Set ->
                             fun _s_830 _l_831 ->
                               Value
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_831
                                     () _s_830)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (let rec _explore_853 _x_772 =
                     (handler
                        {
                          value_clause =
                            (fun (_x_736 : int) -> Value (Cons (_x_736, Nil)));
                          effect_clauses =
                            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                 (a -> (b -> _) -> _) ->
                              match eff with
                              | Choose ->
                                  fun () _l_773 ->
                                    _l_773 true >>= fun _b_734 ->
                                    _l_773 false >>= fun _b_735 ->
                                    Value (_op_144 (* @ *) _b_734 _b_735)
                              | eff' -> fun arg k -> Call (eff', arg, k));
                        })
                       (match _x_772 with
                       | Empty ->
                           Call (Get, (), fun (_y_842 : int) -> Value _y_842)
                       | Node (_left_845, _x_844, _right_843) ->
                           Call
                             ( Set,
                               _x_844 * _x_844,
                               fun (_y_848 : unit) ->
                                 Call
                                   ( Choose,
                                     (),
                                     fun (_y_849 : bool) ->
                                       _explore_720
                                         (if _y_849 then _left_845
                                         else _right_843)
                                       >>= fun _b_852 ->
                                       Value (_op_133 _x_844 _b_852) ) ))
                   in
                   _explore_853 ____t_719))
               ~-1))
  in
  _looper_811 100 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_709

let _test_leaf_state_update_merged_handler_862 (_m_863 : int) =
  let rec _maxl_864 _x_905 (_x_943 : intlist) =
    match _x_943 with
    | Nil -> _x_905
    | Cons (_x_945, _xs_944) -> _maxl_864 (_max_139 _x_945 _x_905) _xs_944
  in
  let rec _explore_873 _x_912 =
    match _x_912 with
    | Empty -> Call (Get, (), fun (_y_930 : int) -> Value _y_930)
    | Node (_left_933, _x_932, _right_931) ->
        Call
          ( Set,
            _x_932 * _x_932,
            fun (_y_936 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_937 : bool) ->
                    _explore_873 (if _y_937 then _left_933 else _right_931)
                    >>= fun _b_940 -> Value (_op_133 _x_932 _b_940) ) )
  in
  _maxl_864 0
    (let rec _explore_941 _x_912 =
       force_unsafe
         ((handler
             {
               value_clause =
                 (fun (_x_898 : int) ->
                   Value (fun (_ : int) -> Cons (_x_898, Nil)));
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | Get ->
                       fun () _l_913 ->
                         Value
                           (fun (_s_886 : int) ->
                             coer_arrow coer_refl_ty force_unsafe _l_913 _s_886
                               _s_886)
                   | Set ->
                       fun _s_888 _l_914 ->
                         Value
                           (fun (_ : int) ->
                             coer_arrow coer_refl_ty force_unsafe _l_914 ()
                               _s_888)
                   | Choose ->
                       fun () _l_915 ->
                         Value
                           (fun (_s_892 : int) ->
                             _op_144 (* @ *)
                               (coer_arrow coer_refl_ty force_unsafe _l_915 true
                                  _s_892)
                               (coer_arrow coer_refl_ty force_unsafe _l_915
                                  false _s_892))
                   | eff' -> fun arg k -> Call (eff', arg, k));
             })
            (match _x_912 with
            | Empty -> Call (Get, (), fun (_y_930 : int) -> Value _y_930)
            | Node (_left_933, _x_932, _right_931) ->
                Call
                  ( Set,
                    _x_932 * _x_932,
                    fun (_y_936 : unit) ->
                      Call
                        ( Choose,
                          (),
                          fun (_y_937 : bool) ->
                            _explore_873
                              (if _y_937 then _left_933 else _right_931)
                            >>= fun _b_940 -> Value (_op_133 _x_932 _b_940) ) )))
     in
     _explore_941 (_tester_42 _m_863) ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_862

let _test_leaf_state_update_merged_handler_loop_950 (_m_951 : int) =
  let rec _maxl_952 _x_1005 (_x_1070 : intlist) =
    match _x_1070 with
    | Nil -> _x_1005
    | Cons (_x_1072, _xs_1071) -> _maxl_952 (_max_139 _x_1072 _x_1005) _xs_1071
  in
  let ____t_960 = _tester_42 _m_951 in
  let rec _explore_961 _x_1012 =
    match _x_1012 with
    | Empty -> Call (Get, (), fun (_y_1057 : int) -> Value _y_1057)
    | Node (_left_1060, _x_1059, _right_1058) ->
        Call
          ( Set,
            _x_1059 * _x_1059,
            fun (_y_1063 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_1064 : bool) ->
                    _explore_961 (if _y_1064 then _left_1060 else _right_1058)
                    >>= fun _b_1067 -> Value (_op_133 _x_1059 _b_1067) ) )
  in
  let rec _looper_1033 _x_1034 (_s_1035 : int) =
    if _x_1034 = 0 then _s_1035
    else
      _looper_1033 (_x_1034 - 1)
        (_s_1035
        + _maxl_952 0
            (let rec _explore_1068 _x_1012 =
               force_unsafe
                 ((handler
                     {
                       value_clause =
                         (fun (_x_986 : int) ->
                           Value (fun (_ : int) -> Cons (_x_986, Nil)));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Get ->
                               fun () _l_1013 ->
                                 Value
                                   (fun (_s_974 : int) ->
                                     coer_arrow coer_refl_ty force_unsafe
                                       _l_1013 _s_974 _s_974)
                           | Set ->
                               fun _s_976 _l_1014 ->
                                 Value
                                   (fun (_ : int) ->
                                     coer_arrow coer_refl_ty force_unsafe
                                       _l_1014 () _s_976)
                           | Choose ->
                               fun () _l_1015 ->
                                 Value
                                   (fun (_s_980 : int) ->
                                     _op_144 (* @ *)
                                       (coer_arrow coer_refl_ty force_unsafe
                                          _l_1015 true _s_980)
                                       (coer_arrow coer_refl_ty force_unsafe
                                          _l_1015 false _s_980))
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     })
                    (match _x_1012 with
                    | Empty ->
                        Call (Get, (), fun (_y_1057 : int) -> Value _y_1057)
                    | Node (_left_1060, _x_1059, _right_1058) ->
                        Call
                          ( Set,
                            _x_1059 * _x_1059,
                            fun (_y_1063 : unit) ->
                              Call
                                ( Choose,
                                  (),
                                  fun (_y_1064 : bool) ->
                                    _explore_961
                                      (if _y_1064 then _left_1060
                                      else _right_1058)
                                    >>= fun _b_1067 ->
                                    Value (_op_133 _x_1059 _b_1067) ) )))
             in
             _explore_1068 ____t_960 ~-1))
  in
  _looper_1033 100 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_950
