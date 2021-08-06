open OcamlHeader

type tree = Empty | Node of (tree * int * tree)

type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect

let _tester_42 (_k_43 : int) =
  let _leaf_44 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_a_45 : int) ->
        Node
          (coer_tuple_3
             (coer_refl_ty, coer_refl_ty, coer_refl_ty)
             ( Empty,
               coer_arrow coer_refl_ty coer_refl_ty (( * ) _a_45) _k_43,
               Empty )))
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
  coer_arrow coer_refl_ty coer_refl_ty
    (_bot_48
       (Node
          (coer_tuple_3
             (coer_refl_ty, coer_refl_ty, coer_refl_ty)
             ( coer_arrow coer_refl_ty coer_refl_ty
                 (_bot_48 (_leaf_44 3))
                 (_leaf_44 4),
               10,
               coer_arrow coer_refl_ty coer_refl_ty
                 (_bot_48 (_leaf_44 1))
                 (_leaf_44 3) ))))
    (coer_arrow coer_refl_ty coer_refl_ty
       (_bot_48
          (Node
             (coer_tuple_3
                (coer_refl_ty, coer_refl_ty, coer_refl_ty)
                ( coer_arrow coer_refl_ty coer_refl_ty
                    (_bot_48 (_leaf_44 3))
                    (_leaf_44 4),
                  10,
                  coer_arrow coer_refl_ty coer_refl_ty
                    (_bot_48 (_leaf_44 1))
                    (_leaf_44 3) ))))
       (_leaf_44 10))

let tester = _tester_42

let _max_88 (_a_89 : int) (_b_90 : int) =
  if coer_arrow coer_refl_ty coer_refl_ty (( > ) _a_89) _b_90 then _a_89
  else _b_90

let max = _max_88

let _effect_max_93 (_m_94 : int) =
  let rec _find_max_167 (_x_115, _k_169) =
    match _x_115 with
    | Empty -> _k_169 0
    | Node (Empty, _x_128, Empty) -> _k_169 _x_128
    | Node (_left_131, _x_130, _right_129) ->
        let _l_116 (_y_132 : bool) =
          if _y_132 then
            _find_max_167
              ( _left_131,
                fun (_x_195 : int) ->
                  _k_169
                    (coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_130) _x_195)
              )
          else
            _find_max_167
              ( _right_129,
                fun (_x_197 : int) ->
                  _k_169
                    (coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_130) _x_197)
              )
        in
        coer_arrow coer_refl_ty coer_refl_ty
          (_max_88 (_l_116 true))
          (_l_116 false)
  in
  _find_max_167 (_tester_42 _m_94, fun (_x_123 : int) -> _x_123)

let effect_max = _effect_max_93

let _test_max_254 (_m_255 : int) = _effect_max_93 _m_255

let test_max = _test_max_254

let _op_256 (_x_257 : int) (_y_258 : int) =
  coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_257)
    (coer_arrow coer_refl_ty coer_refl_ty (( * ) 3) _y_258)

let op = _op_256

let _max_262 (_a_263 : int) (_b_264 : int) =
  if coer_arrow coer_refl_ty coer_refl_ty (( > ) _a_263) _b_264 then _a_263
  else _b_264

let max = _max_262

type intlist = Nil | Cons of (int * intlist)

let rec _op_267 (* @ *) _x_274 =
  coer_arrow coer_refl_ty coer_refl_ty (fun (_ys_276 : intlist) ->
      match _x_274 with
      | Nil -> _ys_276
      | Cons (_x_278, _xs_277) ->
          Cons
            (coer_tuple_2
               (coer_refl_ty, coer_refl_ty)
               ( _x_278,
                 coer_arrow coer_refl_ty coer_refl_ty
                   (_op_267 (* @ *) _xs_277)
                   _ys_276 )))

let _op_267 (* @ *) = _op_267 (* @ *)

let _test_general_281 (_m_282 : int) =
  let rec _maxl_283 _x_313 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_285 : intlist) ->
        match _x_285 with
        | Nil -> _x_313
        | Cons (_x_286, _xs_287) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_283
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_286) _x_313))
              _xs_287)
  in
  coer_arrow coer_refl_ty coer_refl_ty (_maxl_283 0)
    (let rec _explore_377 (_x_316, _k_379) =
       match _x_316 with
       | Empty -> _k_379 0
       | Node (_left_337, _x_336, _right_335) ->
           let _l_317 (_y_338 : bool) =
             if _y_338 then
               _explore_377
                 ( _left_337,
                   fun (_x_443 : int) ->
                     _k_379
                       (coer_arrow coer_refl_ty coer_refl_ty (_op_256 _x_336)
                          _x_443) )
             else
               _explore_377
                 ( _right_335,
                   fun (_x_467 : int) ->
                     _k_379
                       (coer_arrow coer_refl_ty coer_refl_ty (_op_256 _x_336)
                          _x_467) )
           in
           coer_arrow coer_refl_ty coer_refl_ty
             (_op_267 (* @ *) (_l_317 true))
             (_l_317 false)
     in
     _explore_377
       ( _tester_42 _m_282,
         fun (_x_326 : int) ->
           Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_326, Nil)) ))

let test_general = _test_general_281

let _test_general_loop_469 (_m_470 : int) =
  let rec _maxl_471 _x_513 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_473 : intlist) ->
        match _x_473 with
        | Nil -> _x_513
        | Cons (_x_474, _xs_475) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_471
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_474) _x_513))
              _xs_475)
  in
  let ____t_479 = _tester_42 _m_470 in
  let rec _looper_521 _x_522 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_s_524 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_522) 0 then _s_524
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_looper_521
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_522) 1))
            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_524)
               (coer_arrow coer_refl_ty coer_refl_ty (_maxl_471 0)
                  (let rec _explore_591 (_x_516, _k_593) =
                     match _x_516 with
                     | Empty -> _k_593 0
                     | Node (_left_551, _x_550, _right_549) ->
                         let _l_517 (_y_552 : bool) =
                           if _y_552 then
                             _explore_591
                               ( _left_551,
                                 fun (_x_657 : int) ->
                                   _k_593
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (_op_256 _x_550) _x_657) )
                           else
                             _explore_591
                               ( _right_549,
                                 fun (_x_681 : int) ->
                                   _k_593
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (_op_256 _x_550) _x_681) )
                         in
                         coer_arrow coer_refl_ty coer_refl_ty
                           (_op_267 (* @ *) (_l_517 true))
                           (_l_517 false)
                   in
                   _explore_591
                     ( ____t_479,
                       fun (_x_540 : int) ->
                         Cons
                           (coer_tuple_2
                              (coer_refl_ty, coer_refl_ty)
                              (_x_540, Nil)) )))))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_looper_521 100) 0

let test_general_loop = _test_general_loop_469

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_683 (_void_684 : float) = match _void_684 with _ -> assert false

let absurd = _absurd_683

let _test_leaf_state_685 (_m_686 : int) =
  let rec _maxl_687 _x_738 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_689 : intlist) ->
        match _x_689 with
        | Nil -> _x_738
        | Cons (_x_690, _xs_691) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_687
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_690) _x_738))
              _xs_691)
  in
  let rec _populate_leafs_695 _x_739 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_n_697 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_739) _n_697 then Nil
        else
          Cons
            (coer_tuple_2
               (coer_refl_ty, coer_refl_ty)
               ( coer_arrow coer_refl_ty coer_refl_ty (( * ) _x_739) 3,
                 coer_arrow coer_refl_ty coer_refl_ty
                   (_populate_leafs_695
                      (coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_739) 1))
                   _n_697 )))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_maxl_687 0)
    (coer_arrow coer_refl_ty coer_refl_ty
       (coer_arrow coer_refl_ty coer_refl_ty
          (let rec _explore_828 (_x_744, _k_830) =
             match _x_744 with
             | Empty -> Call (Get, (), fun (_y_791 : int) -> _k_830 _y_791)
             | Node (_left_794, _x_793, _right_792) ->
                 let _l_745 (_y_795 : bool) =
                   if _y_795 then
                     coer_return coer_refl_ty (_op_256 _x_793) >>= fun _x_926 ->
                     _explore_828
                       ( _left_794,
                         fun (_x_927 : int) ->
                           coer_return coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty _x_926 _x_927)
                           >>= fun _x_928 -> _k_830 _x_928 )
                   else
                     coer_return coer_refl_ty (_op_256 _x_793) >>= fun _x_994 ->
                     _explore_828
                       ( _right_792,
                         fun (_x_995 : int) ->
                           coer_return coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty _x_994 _x_995)
                           >>= fun _x_996 -> _k_830 _x_996 )
                 in
                 coer_computation coer_refl_ty
                   (coer_computation coer_refl_ty
                      (coer_computation coer_refl_ty
                         (coer_computation coer_refl_ty
                            (coer_computation coer_refl_ty (_l_745 true)))))
                 >>= fun _b_721 ->
                 coer_computation coer_refl_ty
                   (coer_computation coer_refl_ty
                      (coer_return coer_refl_ty
                         (coer_arrow coer_refl_ty coer_refl_ty
                            (_op_267 (* @ *) _b_721))))
                 >>= fun _b_720 ->
                 coer_computation coer_refl_ty
                   (coer_computation coer_refl_ty
                      (coer_computation coer_refl_ty
                         (coer_computation coer_refl_ty
                            (coer_computation coer_refl_ty (_l_745 false)))))
                 >>= fun _b_722 ->
                 coer_computation coer_refl_ty
                   (coer_computation coer_refl_ty
                      (coer_return coer_refl_ty (_b_720 _b_722)))
           in
           let rec _explore_999 (_x_744, _k_830) =
             match _x_744 with
             | Empty ->
                 coer_arrow coer_refl_ty coer_refl_ty
                   (fun (_s_1001 : intlist) ->
                     match _s_1001 with
                     | Cons (_x_1003, _rest_1002) ->
                         coer_arrow coer_refl_ty coer_refl_ty
                           (coer_arrow coer_refl_ty coer_refl_ty
                              (force_unsafe
                                 ((handler
                                     {
                                       value_clause =
                                         (fun (_x_1006 : intlist) ->
                                           Value
                                             (coer_arrow coer_refl_ty
                                                coer_refl_ty
                                                (fun (_ : intlist) -> _x_1006)));
                                       effect_clauses =
                                         (fun (type a b)
                                              (eff : (a, b) eff_internal_effect)
                                              : (a -> (b -> _) -> _) ->
                                           match eff with
                                           | Get ->
                                               fun () _l_1007 ->
                                                 Value
                                                   (coer_arrow coer_refl_ty
                                                      coer_refl_ty
                                                      (fun (_s_1008 : intlist)
                                                      ->
                                                        match _s_1008 with
                                                        | Cons
                                                            (_x_1010, _rest_1009)
                                                          ->
                                                            coer_arrow
                                                              coer_refl_ty
                                                              coer_refl_ty
                                                              (coer_arrow
                                                                 coer_refl_ty
                                                                 coer_refl_ty
                                                                 (coer_arrow
                                                                    coer_refl_ty
                                                                    force_unsafe
                                                                    _l_1007
                                                                    _x_1010))
                                                              _rest_1009
                                                        | Nil -> Nil))
                                           | eff' ->
                                               fun arg k -> Call (eff', arg, k));
                                     })
                                    (_k_830 _x_1003))))
                           _rest_1002
                     | Nil -> Nil)
             | Node (_left_794, _x_793, _right_792) ->
                 let _l_745 (_y_795 : bool) =
                   if _y_795 then
                     coer_return coer_refl_ty (_op_256 _x_793) >>= fun _x_926 ->
                     _explore_828
                       ( _left_794,
                         fun (_x_927 : int) ->
                           coer_return coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty _x_926 _x_927)
                           >>= fun _x_928 -> _k_830 _x_928 )
                   else
                     coer_return coer_refl_ty (_op_256 _x_793) >>= fun _x_994 ->
                     _explore_828
                       ( _right_792,
                         fun (_x_995 : int) ->
                           coer_return coer_refl_ty
                             (coer_arrow coer_refl_ty coer_refl_ty _x_994 _x_995)
                           >>= fun _x_996 -> _k_830 _x_996 )
                 in
                 force_unsafe
                   ((handler
                       {
                         value_clause =
                           (fun (_x_1029 : intlist) ->
                             Value
                               (force_unsafe
                                  ((handler
                                      {
                                        value_clause =
                                          (fun (_x_1114 : intlist) ->
                                            Value
                                              (coer_arrow coer_refl_ty
                                                 coer_refl_ty
                                                 (fun (_ : intlist) ->
                                                   coer_arrow coer_refl_ty
                                                     coer_refl_ty
                                                     (_op_267 (* @ *) _x_1029)
                                                     _x_1114)));
                                        effect_clauses =
                                          (fun (type a b)
                                               (eff :
                                                 (a, b) eff_internal_effect) :
                                               (a -> (b -> _) -> _) ->
                                            match eff with
                                            | Get ->
                                                fun () _l_1116 ->
                                                  Value
                                                    (coer_arrow coer_refl_ty
                                                       coer_refl_ty
                                                       (fun (_s_1117 : intlist)
                                                       ->
                                                         match _s_1117 with
                                                         | Cons
                                                             ( _x_1119,
                                                               _rest_1118 ) ->
                                                             coer_arrow
                                                               coer_refl_ty
                                                               coer_refl_ty
                                                               (coer_arrow
                                                                  coer_refl_ty
                                                                  coer_refl_ty
                                                                  (coer_arrow
                                                                     coer_refl_ty
                                                                     force_unsafe
                                                                     _l_1116
                                                                     _x_1119))
                                                               _rest_1118
                                                         | Nil -> Nil))
                                            | eff' ->
                                                fun arg k -> Call (eff', arg, k));
                                      })
                                     (_l_745 false))));
                         effect_clauses =
                           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                (a -> (b -> _) -> _) ->
                             match eff with
                             | Get ->
                                 fun () _l_768 ->
                                   Value
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (fun (_s_769 : intlist) ->
                                          match _s_769 with
                                          | Cons (_x_771, _rest_770) ->
                                              coer_arrow coer_refl_ty
                                                coer_refl_ty
                                                (coer_arrow coer_refl_ty
                                                   coer_refl_ty
                                                   (coer_arrow coer_refl_ty
                                                      force_unsafe _l_768 _x_771))
                                                _rest_770
                                          | Nil -> Nil))
                             | eff' -> fun arg k -> Call (eff', arg, k));
                       })
                      (_l_745 true))
           in
           _explore_999
             ( _tester_42 _m_686,
               fun (_x_777 : int) ->
                 coer_return coer_refl_ty
                   (Cons
                      (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_777, Nil)))
             )))
       (coer_arrow coer_refl_ty coer_refl_ty (_populate_leafs_695 0) 154))

let test_leaf_state = _test_leaf_state_685

let _test_leaf_state_loop_11780 (_m_11781 : int) =
  let rec _maxl_11782 _x_11845 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_11784 : intlist) ->
        match _x_11784 with
        | Nil -> _x_11845
        | Cons (_x_11785, _xs_11786) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_11782
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_11785)
                    _x_11845))
              _xs_11786)
  in
  let rec _populate_leafs_11790 _x_11846 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_n_11792 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_11846) _n_11792 then
          Nil
        else
          Cons
            (coer_tuple_2
               (coer_refl_ty, coer_refl_ty)
               ( coer_arrow coer_refl_ty coer_refl_ty (( * ) _x_11846) 3,
                 coer_arrow coer_refl_ty coer_refl_ty
                   (_populate_leafs_11790
                      (coer_arrow coer_refl_ty coer_refl_ty (( + ) _x_11846) 1))
                   _n_11792 )))
  in
  let ____leafs_11801 =
    coer_arrow coer_refl_ty coer_refl_ty (_populate_leafs_11790 0) 154
  in
  let ____t_11803 = _tester_42 _m_11781 in
  let rec _looper_11880 _x_11881 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_s_11883 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_11881) 0 then _s_11883
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_looper_11880
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_11881) 1))
            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_11883)
               (coer_arrow coer_refl_ty coer_refl_ty (_maxl_11782 0)
                  (coer_arrow coer_refl_ty coer_refl_ty
                     (coer_arrow coer_refl_ty coer_refl_ty
                        (let rec _explore_11962 (_x_11851, _k_11964) =
                           match _x_11851 with
                           | Empty ->
                               Call
                                 ( Get,
                                   (),
                                   fun (_y_11925 : int) -> _k_11964 _y_11925 )
                           | Node (_left_11928, _x_11927, _right_11926) ->
                               let _l_11852 (_y_11929 : bool) =
                                 if _y_11929 then
                                   coer_return coer_refl_ty (_op_256 _x_11927)
                                   >>= fun _x_12060 ->
                                   _explore_11962
                                     ( _left_11928,
                                       fun (_x_12061 : int) ->
                                         coer_return coer_refl_ty
                                           (coer_arrow coer_refl_ty coer_refl_ty
                                              _x_12060 _x_12061)
                                         >>= fun _x_12062 -> _k_11964 _x_12062
                                     )
                                 else
                                   coer_return coer_refl_ty (_op_256 _x_11927)
                                   >>= fun _x_12128 ->
                                   _explore_11962
                                     ( _right_11926,
                                       fun (_x_12129 : int) ->
                                         coer_return coer_refl_ty
                                           (coer_arrow coer_refl_ty coer_refl_ty
                                              _x_12128 _x_12129)
                                         >>= fun _x_12130 -> _k_11964 _x_12130
                                     )
                               in
                               coer_computation coer_refl_ty
                                 (coer_computation coer_refl_ty
                                    (coer_computation coer_refl_ty
                                       (coer_computation coer_refl_ty
                                          (coer_computation coer_refl_ty
                                             (_l_11852 true)))))
                               >>= fun _b_11816 ->
                               coer_computation coer_refl_ty
                                 (coer_computation coer_refl_ty
                                    (coer_return coer_refl_ty
                                       (coer_arrow coer_refl_ty coer_refl_ty
                                          (_op_267 (* @ *) _b_11816))))
                               >>= fun _b_11815 ->
                               coer_computation coer_refl_ty
                                 (coer_computation coer_refl_ty
                                    (coer_computation coer_refl_ty
                                       (coer_computation coer_refl_ty
                                          (coer_computation coer_refl_ty
                                             (_l_11852 false)))))
                               >>= fun _b_11817 ->
                               coer_computation coer_refl_ty
                                 (coer_computation coer_refl_ty
                                    (coer_return coer_refl_ty
                                       (_b_11815 _b_11817)))
                         in
                         let rec _explore_12133 (_x_11851, _k_11964) =
                           match _x_11851 with
                           | Empty ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (fun (_s_12135 : intlist) ->
                                   match _s_12135 with
                                   | Cons (_x_12137, _rest_12136) ->
                                       coer_arrow coer_refl_ty coer_refl_ty
                                         (coer_arrow coer_refl_ty coer_refl_ty
                                            (force_unsafe
                                               ((handler
                                                   {
                                                     value_clause =
                                                       (fun (_x_12140 : intlist) ->
                                                         Value
                                                           (coer_arrow
                                                              coer_refl_ty
                                                              coer_refl_ty
                                                              (fun (_ : intlist)
                                                              -> _x_12140)));
                                                     effect_clauses =
                                                       (fun (type a b)
                                                            (eff :
                                                              ( a,
                                                                b )
                                                              eff_internal_effect)
                                                            :
                                                            (a -> (b -> _) -> _) ->
                                                         match eff with
                                                         | Get ->
                                                             fun () _l_12141 ->
                                                               Value
                                                                 (coer_arrow
                                                                    coer_refl_ty
                                                                    coer_refl_ty
                                                                    (fun
                                                                      (_s_12142 :
                                                                        intlist)
                                                                    ->
                                                                      match
                                                                        _s_12142
                                                                      with
                                                                      | Cons
                                                                          ( _x_12144,
                                                                            _rest_12143
                                                                          ) ->
                                                                          coer_arrow
                                                                            coer_refl_ty
                                                                            coer_refl_ty
                                                                            (coer_arrow
                                                                               coer_refl_ty
                                                                               coer_refl_ty
                                                                               (coer_arrow
                                                                                coer_refl_ty
                                                                                force_unsafe
                                                                                _l_12141
                                                                                _x_12144))
                                                                            _rest_12143
                                                                      | Nil ->
                                                                          Nil))
                                                         | eff' ->
                                                             fun arg k ->
                                                               Call
                                                                 (eff', arg, k));
                                                   })
                                                  (_k_11964 _x_12137))))
                                         _rest_12136
                                   | Nil -> Nil)
                           | Node (_left_11928, _x_11927, _right_11926) ->
                               let _l_11852 (_y_11929 : bool) =
                                 if _y_11929 then
                                   coer_return coer_refl_ty (_op_256 _x_11927)
                                   >>= fun _x_12060 ->
                                   _explore_11962
                                     ( _left_11928,
                                       fun (_x_12061 : int) ->
                                         coer_return coer_refl_ty
                                           (coer_arrow coer_refl_ty coer_refl_ty
                                              _x_12060 _x_12061)
                                         >>= fun _x_12062 -> _k_11964 _x_12062
                                     )
                                 else
                                   coer_return coer_refl_ty (_op_256 _x_11927)
                                   >>= fun _x_12128 ->
                                   _explore_11962
                                     ( _right_11926,
                                       fun (_x_12129 : int) ->
                                         coer_return coer_refl_ty
                                           (coer_arrow coer_refl_ty coer_refl_ty
                                              _x_12128 _x_12129)
                                         >>= fun _x_12130 -> _k_11964 _x_12130
                                     )
                               in
                               force_unsafe
                                 ((handler
                                     {
                                       value_clause =
                                         (fun (_x_12163 : intlist) ->
                                           Value
                                             (force_unsafe
                                                ((handler
                                                    {
                                                      value_clause =
                                                        (fun (_x_12248 :
                                                               intlist) ->
                                                          Value
                                                            (coer_arrow
                                                               coer_refl_ty
                                                               coer_refl_ty
                                                               (fun
                                                                 (_ : intlist)
                                                               ->
                                                                 coer_arrow
                                                                   coer_refl_ty
                                                                   coer_refl_ty
                                                                   (_op_267
                                                                      (* @ *)
                                                                      _x_12163)
                                                                   _x_12248)));
                                                      effect_clauses =
                                                        (fun (type a b)
                                                             (eff :
                                                               ( a,
                                                                 b )
                                                               eff_internal_effect)
                                                             :
                                                             (a ->
                                                             (b -> _) ->
                                                             _) ->
                                                          match eff with
                                                          | Get ->
                                                              fun () _l_12250 ->
                                                                Value
                                                                  (coer_arrow
                                                                     coer_refl_ty
                                                                     coer_refl_ty
                                                                     (fun
                                                                       (_s_12251 :
                                                                         intlist)
                                                                     ->
                                                                       match
                                                                         _s_12251
                                                                       with
                                                                       | Cons
                                                                           ( _x_12253,
                                                                             _rest_12252
                                                                           ) ->
                                                                           coer_arrow
                                                                             coer_refl_ty
                                                                             coer_refl_ty
                                                                             (coer_arrow
                                                                                coer_refl_ty
                                                                                coer_refl_ty
                                                                                (
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                force_unsafe
                                                                                _l_12250
                                                                                _x_12253))
                                                                             _rest_12252
                                                                       | Nil ->
                                                                           Nil))
                                                          | eff' ->
                                                              fun arg k ->
                                                                Call
                                                                  (eff', arg, k));
                                                    })
                                                   (_l_11852 false))));
                                       effect_clauses =
                                         (fun (type a b)
                                              (eff : (a, b) eff_internal_effect)
                                              : (a -> (b -> _) -> _) ->
                                           match eff with
                                           | Get ->
                                               fun () _l_11901 ->
                                                 Value
                                                   (coer_arrow coer_refl_ty
                                                      coer_refl_ty
                                                      (fun (_s_11902 : intlist)
                                                      ->
                                                        match _s_11902 with
                                                        | Cons
                                                            ( _x_11904,
                                                              _rest_11903 ) ->
                                                            coer_arrow
                                                              coer_refl_ty
                                                              coer_refl_ty
                                                              (coer_arrow
                                                                 coer_refl_ty
                                                                 coer_refl_ty
                                                                 (coer_arrow
                                                                    coer_refl_ty
                                                                    force_unsafe
                                                                    _l_11901
                                                                    _x_11904))
                                                              _rest_11903
                                                        | Nil -> Nil))
                                           | eff' ->
                                               fun arg k -> Call (eff', arg, k));
                                     })
                                    (_l_11852 true))
                         in
                         _explore_12133
                           ( ____t_11803,
                             fun (_x_11911 : int) ->
                               coer_return coer_refl_ty
                                 (Cons
                                    (coer_tuple_2
                                       (coer_refl_ty, coer_refl_ty)
                                       (_x_11911, Nil))) )))
                     ____leafs_11801))))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_looper_11880 100) 0

let test_leaf_state_loop = _test_leaf_state_loop_11780

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_22914 (_m_22915 : int) =
  let rec _maxl_22916 _x_22958 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_22918 : intlist) ->
        match _x_22918 with
        | Nil -> _x_22958
        | Cons (_x_22919, _xs_22920) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_22916
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_22919)
                    _x_22958))
              _xs_22920)
  in
  coer_arrow coer_refl_ty coer_refl_ty (_maxl_22916 0)
    (coer_arrow coer_refl_ty coer_refl_ty
       (coer_arrow coer_refl_ty coer_refl_ty
          (let rec _explore_23060 (_x_22965, _k_23062) =
             match _x_22965 with
             | Empty -> Call (Get, (), fun (_y_23018 : int) -> _k_23062 _y_23018)
             | Node (_left_23021, _x_23020, _right_23019) ->
                 coer_return coer_refl_ty (( * ) _x_23020) >>= fun _x_23270 ->
                 coer_return coer_refl_ty
                   (coer_arrow coer_refl_ty coer_refl_ty _x_23270 _x_23020)
                 >>= fun _x_23393 ->
                 Call
                   ( Set,
                     _x_23393,
                     fun (_y_23394 : unit) ->
                       let _l_23395 (_y_23399 : bool) =
                         if _y_23399 then
                           coer_return coer_refl_ty (_op_256 _x_23020)
                           >>= fun _x_23400 ->
                           _explore_23060
                             ( _left_23021,
                               fun (_x_23401 : int) ->
                                 coer_return coer_refl_ty
                                   (coer_arrow coer_refl_ty coer_refl_ty
                                      _x_23400 _x_23401)
                                 >>= fun _x_23402 -> _k_23062 _x_23402 )
                         else
                           coer_return coer_refl_ty (_op_256 _x_23020)
                           >>= fun _x_23403 ->
                           _explore_23060
                             ( _right_23019,
                               fun (_x_23404 : int) ->
                                 coer_return coer_refl_ty
                                   (coer_arrow coer_refl_ty coer_refl_ty
                                      _x_23403 _x_23404)
                                 >>= fun _x_23405 -> _k_23062 _x_23405 )
                       in
                       coer_computation coer_refl_ty
                         (coer_computation coer_refl_ty
                            (coer_computation coer_refl_ty
                               (coer_computation coer_refl_ty
                                  (coer_computation coer_refl_ty (_l_23395 true)))))
                       >>= fun _b_23396 ->
                       coer_computation coer_refl_ty
                         (coer_computation coer_refl_ty
                            (coer_return coer_refl_ty
                               (coer_arrow coer_refl_ty coer_refl_ty
                                  (_op_267 (* @ *) _b_23396))))
                       >>= fun _b_23397 ->
                       coer_computation coer_refl_ty
                         (coer_computation coer_refl_ty
                            (coer_computation coer_refl_ty
                               (coer_computation coer_refl_ty
                                  (coer_computation coer_refl_ty
                                     (_l_23395 false)))))
                       >>= fun _b_23398 ->
                       coer_computation coer_refl_ty
                         (coer_computation coer_refl_ty
                            (coer_return coer_refl_ty (_b_23397 _b_23398))) )
           in
           let rec _explore_23408 (_x_22965, _k_23062) =
             match _x_22965 with
             | Empty ->
                 coer_arrow coer_refl_ty coer_refl_ty (fun (_s_23410 : int) ->
                     coer_arrow coer_refl_ty coer_refl_ty
                       (coer_arrow coer_refl_ty coer_refl_ty
                          (force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_x_23413 : intlist) ->
                                       Value
                                         (coer_arrow coer_refl_ty coer_refl_ty
                                            (fun (_ : int) -> _x_23413)));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l_23414 ->
                                             Value
                                               (coer_arrow coer_refl_ty
                                                  coer_refl_ty
                                                  (fun (_s_23415 : int) ->
                                                    coer_arrow coer_refl_ty
                                                      coer_refl_ty
                                                      (coer_arrow coer_refl_ty
                                                         coer_refl_ty
                                                         (coer_arrow
                                                            coer_refl_ty
                                                            force_unsafe
                                                            _l_23414 _s_23415))
                                                      _s_23415))
                                       | Set ->
                                           fun _s_23417 _l_23418 ->
                                             Value
                                               (coer_arrow coer_refl_ty
                                                  coer_refl_ty (fun (_ : int) ->
                                                    coer_arrow coer_refl_ty
                                                      coer_refl_ty
                                                      (coer_arrow coer_refl_ty
                                                         coer_refl_ty
                                                         (coer_arrow
                                                            coer_refl_ty
                                                            force_unsafe
                                                            _l_23418 ()))
                                                      _s_23417))
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_k_23062 _s_23410))))
                       _s_23410)
             | Node (_left_23021, _x_23020, _right_23019) ->
                 coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) ->
                     coer_arrow coer_refl_ty coer_refl_ty
                       (coer_arrow coer_refl_ty coer_refl_ty
                          (let _l_24044 (_y_24061 : bool) =
                             if _y_24061 then
                               coer_return coer_refl_ty (_op_256 _x_23020)
                               >>= fun _x_24062 ->
                               _explore_23060
                                 ( _left_23021,
                                   fun (_x_24063 : int) ->
                                     coer_return coer_refl_ty
                                       (coer_arrow coer_refl_ty coer_refl_ty
                                          _x_24062 _x_24063)
                                     >>= fun _x_24064 -> _k_23062 _x_24064 )
                             else
                               coer_return coer_refl_ty (_op_256 _x_23020)
                               >>= fun _x_24065 ->
                               _explore_23060
                                 ( _right_23019,
                                   fun (_x_24066 : int) ->
                                     coer_return coer_refl_ty
                                       (coer_arrow coer_refl_ty coer_refl_ty
                                          _x_24065 _x_24066)
                                     >>= fun _x_24067 -> _k_23062 _x_24067 )
                           in
                           force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_x_24045 : intlist) ->
                                       Value
                                         (force_unsafe
                                            ((handler
                                                {
                                                  value_clause =
                                                    (fun (_x_24047 : intlist) ->
                                                      Value
                                                        (coer_arrow coer_refl_ty
                                                           coer_refl_ty
                                                           (fun (_ : int) ->
                                                             coer_arrow
                                                               coer_refl_ty
                                                               coer_refl_ty
                                                               (_op_267 (* @ *)
                                                                  _x_24045)
                                                               _x_24047)));
                                                  effect_clauses =
                                                    (fun (type a b)
                                                         (eff :
                                                           ( a,
                                                             b )
                                                           eff_internal_effect)
                                                         : (a -> (b -> _) -> _) ->
                                                      match eff with
                                                      | Get ->
                                                          fun () _l_24049 ->
                                                            Value
                                                              (coer_arrow
                                                                 coer_refl_ty
                                                                 coer_refl_ty
                                                                 (fun
                                                                   (_s_24050 :
                                                                     int)
                                                                 ->
                                                                   coer_arrow
                                                                     coer_refl_ty
                                                                     coer_refl_ty
                                                                     (coer_arrow
                                                                        coer_refl_ty
                                                                        coer_refl_ty
                                                                        (coer_arrow
                                                                           coer_refl_ty
                                                                           force_unsafe
                                                                           _l_24049
                                                                           _s_24050))
                                                                     _s_24050))
                                                      | Set ->
                                                          fun _s_24052 _l_24053 ->
                                                            Value
                                                              (coer_arrow
                                                                 coer_refl_ty
                                                                 coer_refl_ty
                                                                 (fun (_ : int)
                                                                 ->
                                                                   coer_arrow
                                                                     coer_refl_ty
                                                                     coer_refl_ty
                                                                     (coer_arrow
                                                                        coer_refl_ty
                                                                        coer_refl_ty
                                                                        (coer_arrow
                                                                           coer_refl_ty
                                                                           force_unsafe
                                                                           _l_24053
                                                                           ()))
                                                                     _s_24052))
                                                      | eff' ->
                                                          fun arg k ->
                                                            Call (eff', arg, k));
                                                })
                                               (_l_24044 false))));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l_24055 ->
                                             Value
                                               (coer_arrow coer_refl_ty
                                                  coer_refl_ty
                                                  (fun (_s_24056 : int) ->
                                                    coer_arrow coer_refl_ty
                                                      coer_refl_ty
                                                      (coer_arrow coer_refl_ty
                                                         coer_refl_ty
                                                         (coer_arrow
                                                            coer_refl_ty
                                                            force_unsafe
                                                            _l_24055 _s_24056))
                                                      _s_24056))
                                       | Set ->
                                           fun _s_24058 _l_24059 ->
                                             Value
                                               (coer_arrow coer_refl_ty
                                                  coer_refl_ty (fun (_ : int) ->
                                                    coer_arrow coer_refl_ty
                                                      coer_refl_ty
                                                      (coer_arrow coer_refl_ty
                                                         coer_refl_ty
                                                         (coer_arrow
                                                            coer_refl_ty
                                                            force_unsafe
                                                            _l_24059 ()))
                                                      _s_24058))
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_l_24044 true))))
                       (coer_arrow coer_refl_ty coer_refl_ty (( * ) _x_23020)
                          _x_23020))
           in
           _explore_23408
             ( _tester_42 _m_22915,
               fun (_x_23002 : int) ->
                 coer_return coer_refl_ty
                   (Cons
                      (coer_tuple_2
                         (coer_refl_ty, coer_refl_ty)
                         (_x_23002, Nil))) )))
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_22914

let _test_leaf_state_update_loop_57319 (_m_57320 : int) =
  let rec _maxl_57321 _x_57375 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_57323 : intlist) ->
        match _x_57323 with
        | Nil -> _x_57375
        | Cons (_x_57324, _xs_57325) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_57321
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_57324)
                    _x_57375))
              _xs_57325)
  in
  let ____t_57329 = _tester_42 _m_57320 in
  let rec _looper_57413 _x_57414 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_s_57416 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_57414) 0 then _s_57416
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_looper_57413
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_57414) 1))
            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_57416)
               (coer_arrow coer_refl_ty coer_refl_ty (_maxl_57321 0)
                  (coer_arrow coer_refl_ty coer_refl_ty
                     (coer_arrow coer_refl_ty coer_refl_ty
                        (let rec _explore_57504 (_x_57382, _k_57506) =
                           match _x_57382 with
                           | Empty ->
                               Call
                                 ( Get,
                                   (),
                                   fun (_y_57462 : int) -> _k_57506 _y_57462 )
                           | Node (_left_57465, _x_57464, _right_57463) ->
                               coer_return coer_refl_ty (( * ) _x_57464)
                               >>= fun _x_57714 ->
                               coer_return coer_refl_ty
                                 (coer_arrow coer_refl_ty coer_refl_ty _x_57714
                                    _x_57464)
                               >>= fun _x_57837 ->
                               Call
                                 ( Set,
                                   _x_57837,
                                   fun (_y_57838 : unit) ->
                                     let _l_57839 (_y_57843 : bool) =
                                       if _y_57843 then
                                         coer_return coer_refl_ty
                                           (_op_256 _x_57464)
                                         >>= fun _x_57844 ->
                                         _explore_57504
                                           ( _left_57465,
                                             fun (_x_57845 : int) ->
                                               coer_return coer_refl_ty
                                                 (coer_arrow coer_refl_ty
                                                    coer_refl_ty _x_57844
                                                    _x_57845)
                                               >>= fun _x_57846 ->
                                               _k_57506 _x_57846 )
                                       else
                                         coer_return coer_refl_ty
                                           (_op_256 _x_57464)
                                         >>= fun _x_57847 ->
                                         _explore_57504
                                           ( _right_57463,
                                             fun (_x_57848 : int) ->
                                               coer_return coer_refl_ty
                                                 (coer_arrow coer_refl_ty
                                                    coer_refl_ty _x_57847
                                                    _x_57848)
                                               >>= fun _x_57849 ->
                                               _k_57506 _x_57849 )
                                     in
                                     coer_computation coer_refl_ty
                                       (coer_computation coer_refl_ty
                                          (coer_computation coer_refl_ty
                                             (coer_computation coer_refl_ty
                                                (coer_computation coer_refl_ty
                                                   (_l_57839 true)))))
                                     >>= fun _b_57840 ->
                                     coer_computation coer_refl_ty
                                       (coer_computation coer_refl_ty
                                          (coer_return coer_refl_ty
                                             (coer_arrow coer_refl_ty
                                                coer_refl_ty
                                                (_op_267 (* @ *) _b_57840))))
                                     >>= fun _b_57841 ->
                                     coer_computation coer_refl_ty
                                       (coer_computation coer_refl_ty
                                          (coer_computation coer_refl_ty
                                             (coer_computation coer_refl_ty
                                                (coer_computation coer_refl_ty
                                                   (_l_57839 false)))))
                                     >>= fun _b_57842 ->
                                     coer_computation coer_refl_ty
                                       (coer_computation coer_refl_ty
                                          (coer_return coer_refl_ty
                                             (_b_57841 _b_57842))) )
                         in
                         let rec _explore_57852 (_x_57382, _k_57506) =
                           match _x_57382 with
                           | Empty ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (fun (_s_57854 : int) ->
                                   coer_arrow coer_refl_ty coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (force_unsafe
                                           ((handler
                                               {
                                                 value_clause =
                                                   (fun (_x_57857 : intlist) ->
                                                     Value
                                                       (coer_arrow coer_refl_ty
                                                          coer_refl_ty
                                                          (fun (_ : int) ->
                                                            _x_57857)));
                                                 effect_clauses =
                                                   (fun (type a b)
                                                        (eff :
                                                          ( a,
                                                            b )
                                                          eff_internal_effect) :
                                                        (a -> (b -> _) -> _) ->
                                                     match eff with
                                                     | Get ->
                                                         fun () _l_57858 ->
                                                           Value
                                                             (coer_arrow
                                                                coer_refl_ty
                                                                coer_refl_ty
                                                                (fun
                                                                  (_s_57859 :
                                                                    int)
                                                                ->
                                                                  coer_arrow
                                                                    coer_refl_ty
                                                                    coer_refl_ty
                                                                    (coer_arrow
                                                                       coer_refl_ty
                                                                       coer_refl_ty
                                                                       (coer_arrow
                                                                          coer_refl_ty
                                                                          force_unsafe
                                                                          _l_57858
                                                                          _s_57859))
                                                                    _s_57859))
                                                     | Set ->
                                                         fun _s_57861 _l_57862 ->
                                                           Value
                                                             (coer_arrow
                                                                coer_refl_ty
                                                                coer_refl_ty
                                                                (fun (_ : int)
                                                                ->
                                                                  coer_arrow
                                                                    coer_refl_ty
                                                                    coer_refl_ty
                                                                    (coer_arrow
                                                                       coer_refl_ty
                                                                       coer_refl_ty
                                                                       (coer_arrow
                                                                          coer_refl_ty
                                                                          force_unsafe
                                                                          _l_57862
                                                                          ()))
                                                                    _s_57861))
                                                     | eff' ->
                                                         fun arg k ->
                                                           Call (eff', arg, k));
                                               })
                                              (_k_57506 _s_57854))))
                                     _s_57854)
                           | Node (_left_57465, _x_57464, _right_57463) ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (let _l_58488 (_y_58505 : bool) =
                                           if _y_58505 then
                                             coer_return coer_refl_ty
                                               (_op_256 _x_57464)
                                             >>= fun _x_58506 ->
                                             _explore_57504
                                               ( _left_57465,
                                                 fun (_x_58507 : int) ->
                                                   coer_return coer_refl_ty
                                                     (coer_arrow coer_refl_ty
                                                        coer_refl_ty _x_58506
                                                        _x_58507)
                                                   >>= fun _x_58508 ->
                                                   _k_57506 _x_58508 )
                                           else
                                             coer_return coer_refl_ty
                                               (_op_256 _x_57464)
                                             >>= fun _x_58509 ->
                                             _explore_57504
                                               ( _right_57463,
                                                 fun (_x_58510 : int) ->
                                                   coer_return coer_refl_ty
                                                     (coer_arrow coer_refl_ty
                                                        coer_refl_ty _x_58509
                                                        _x_58510)
                                                   >>= fun _x_58511 ->
                                                   _k_57506 _x_58511 )
                                         in
                                         force_unsafe
                                           ((handler
                                               {
                                                 value_clause =
                                                   (fun (_x_58489 : intlist) ->
                                                     Value
                                                       (force_unsafe
                                                          ((handler
                                                              {
                                                                value_clause =
                                                                  (fun (_x_58491 :
                                                                         intlist)
                                                                       ->
                                                                    Value
                                                                      (coer_arrow
                                                                         coer_refl_ty
                                                                         coer_refl_ty
                                                                         (fun
                                                                           (_ :
                                                                             int)
                                                                         ->
                                                                           coer_arrow
                                                                             coer_refl_ty
                                                                             coer_refl_ty
                                                                             (_op_267
                                                                                (* @ *)
                                                                                _x_58489)
                                                                             _x_58491)));
                                                                effect_clauses =
                                                                  (fun (type a
                                                                       b)
                                                                       (eff :
                                                                         ( a,
                                                                           b )
                                                                         eff_internal_effect)
                                                                       :
                                                                       (a ->
                                                                       (b -> _) ->
                                                                       _) ->
                                                                    match
                                                                      eff
                                                                    with
                                                                    | Get ->
                                                                        fun ()
                                                                            _l_58493
                                                                            ->
                                                                          Value
                                                                            (coer_arrow
                                                                               coer_refl_ty
                                                                               coer_refl_ty
                                                                               (fun
                                                                                (_s_58494 :
                                                                                int)
                                                                               ->
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                coer_refl_ty
                                                                                (
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                coer_refl_ty
                                                                                (
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                force_unsafe
                                                                                _l_58493
                                                                                _s_58494))
                                                                                _s_58494))
                                                                    | Set ->
                                                                        fun _s_58496
                                                                            _l_58497
                                                                            ->
                                                                          Value
                                                                            (coer_arrow
                                                                               coer_refl_ty
                                                                               coer_refl_ty
                                                                               (fun
                                                                                (_ :
                                                                                int)
                                                                               ->
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                coer_refl_ty
                                                                                (
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                coer_refl_ty
                                                                                (
                                                                                coer_arrow
                                                                                coer_refl_ty
                                                                                force_unsafe
                                                                                _l_58497
                                                                                ()))
                                                                                _s_58496))
                                                                    | eff' ->
                                                                        fun arg
                                                                            k ->
                                                                          Call
                                                                            ( eff',
                                                                              arg,
                                                                              k
                                                                            ));
                                                              })
                                                             (_l_58488 false))));
                                                 effect_clauses =
                                                   (fun (type a b)
                                                        (eff :
                                                          ( a,
                                                            b )
                                                          eff_internal_effect) :
                                                        (a -> (b -> _) -> _) ->
                                                     match eff with
                                                     | Get ->
                                                         fun () _l_58499 ->
                                                           Value
                                                             (coer_arrow
                                                                coer_refl_ty
                                                                coer_refl_ty
                                                                (fun
                                                                  (_s_58500 :
                                                                    int)
                                                                ->
                                                                  coer_arrow
                                                                    coer_refl_ty
                                                                    coer_refl_ty
                                                                    (coer_arrow
                                                                       coer_refl_ty
                                                                       coer_refl_ty
                                                                       (coer_arrow
                                                                          coer_refl_ty
                                                                          force_unsafe
                                                                          _l_58499
                                                                          _s_58500))
                                                                    _s_58500))
                                                     | Set ->
                                                         fun _s_58502 _l_58503 ->
                                                           Value
                                                             (coer_arrow
                                                                coer_refl_ty
                                                                coer_refl_ty
                                                                (fun (_ : int)
                                                                ->
                                                                  coer_arrow
                                                                    coer_refl_ty
                                                                    coer_refl_ty
                                                                    (coer_arrow
                                                                       coer_refl_ty
                                                                       coer_refl_ty
                                                                       (coer_arrow
                                                                          coer_refl_ty
                                                                          force_unsafe
                                                                          _l_58503
                                                                          ()))
                                                                    _s_58502))
                                                     | eff' ->
                                                         fun arg k ->
                                                           Call (eff', arg, k));
                                               })
                                              (_l_58488 true))))
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (( * ) _x_57464) _x_57464))
                         in
                         _explore_57852
                           ( ____t_57329,
                             fun (_x_57446 : int) ->
                               coer_return coer_refl_ty
                                 (Cons
                                    (coer_tuple_2
                                       (coer_refl_ty, coer_refl_ty)
                                       (_x_57446, Nil))) )))
                     ~-1))))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_looper_57413 100) 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_57319

let _test_leaf_state_update_merged_handler_91763 (_m_91764 : int) =
  let rec _maxl_91765 _x_91806 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_91767 : intlist) ->
        match _x_91767 with
        | Nil -> _x_91806
        | Cons (_x_91768, _xs_91769) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_91765
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_91768)
                    _x_91806))
              _xs_91769)
  in
  coer_arrow coer_refl_ty coer_refl_ty (_maxl_91765 0)
    (coer_arrow coer_refl_ty coer_refl_ty
       (coer_arrow coer_refl_ty coer_refl_ty
          (let rec _explore_91883 (_x_91813, _k_91885) =
             match _x_91813 with
             | Empty ->
                 coer_arrow coer_refl_ty coer_refl_ty (fun (_s_91900 : int) ->
                     coer_arrow coer_refl_ty coer_refl_ty
                       (coer_arrow coer_refl_ty coer_refl_ty (_k_91885 _s_91900))
                       _s_91900)
             | Node (_left_91839, _x_91838, _right_91837) ->
                 coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) ->
                     coer_arrow coer_refl_ty coer_refl_ty
                       (coer_arrow coer_refl_ty coer_refl_ty
                          (let _l_92267 (_y_92274 : bool) =
                             if _y_92274 then
                               _explore_91883
                                 ( _left_91839,
                                   fun (_x_92276 : int) ->
                                     _k_91885
                                       (coer_arrow coer_refl_ty coer_refl_ty
                                          (_op_256 _x_91838) _x_92276) )
                             else
                               _explore_91883
                                 ( _right_91837,
                                   fun (_x_92279 : int) ->
                                     _k_91885
                                       (coer_arrow coer_refl_ty coer_refl_ty
                                          (_op_256 _x_91838) _x_92279) )
                           in
                           coer_arrow coer_refl_ty coer_refl_ty
                             (fun (_s_92268 : int) ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (_op_267 (* @ *)
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (coer_arrow coer_refl_ty coer_refl_ty
                                          (_l_92267 true))
                                       _s_92268))
                                 (coer_arrow coer_refl_ty coer_refl_ty
                                    (coer_arrow coer_refl_ty coer_refl_ty
                                       (_l_92267 false))
                                    _s_92268))))
                       (coer_arrow coer_refl_ty coer_refl_ty (( * ) _x_91838)
                          _x_91838))
           in
           _explore_91883
             ( _tester_42 _m_91764,
               fun (_x_91827 : int) ->
                 coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) ->
                     Cons
                       (coer_tuple_2
                          (coer_refl_ty, coer_refl_ty)
                          (_x_91827, Nil))) )))
       ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_91763

let _test_leaf_state_update_merged_handler_loop_92281 (_m_92282 : int) =
  let rec _maxl_92283 _x_92336 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_x_92285 : intlist) ->
        match _x_92285 with
        | Nil -> _x_92336
        | Cons (_x_92286, _xs_92287) ->
            coer_arrow coer_refl_ty coer_refl_ty
              (_maxl_92283
                 (coer_arrow coer_refl_ty coer_refl_ty (_max_262 _x_92286)
                    _x_92336))
              _xs_92287)
  in
  let ____t_92291 = _tester_42 _m_92282 in
  let rec _looper_92350 _x_92351 =
    coer_arrow coer_refl_ty coer_refl_ty (fun (_s_92353 : int) ->
        if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_92351) 0 then _s_92353
        else
          coer_arrow coer_refl_ty coer_refl_ty
            (_looper_92350
               (coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_92351) 1))
            (coer_arrow coer_refl_ty coer_refl_ty (( + ) _s_92353)
               (coer_arrow coer_refl_ty coer_refl_ty (_maxl_92283 0)
                  (coer_arrow coer_refl_ty coer_refl_ty
                     (coer_arrow coer_refl_ty coer_refl_ty
                        (let rec _explore_92427 (_x_92343, _k_92429) =
                           match _x_92343 with
                           | Empty ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (fun (_s_92444 : int) ->
                                   coer_arrow coer_refl_ty coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (_k_92429 _s_92444))
                                     _s_92444)
                           | Node (_left_92383, _x_92382, _right_92381) ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty coer_refl_ty
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (let _l_92811 (_y_92818 : bool) =
                                           if _y_92818 then
                                             _explore_92427
                                               ( _left_92383,
                                                 fun (_x_92820 : int) ->
                                                   _k_92429
                                                     (coer_arrow coer_refl_ty
                                                        coer_refl_ty
                                                        (_op_256 _x_92382)
                                                        _x_92820) )
                                           else
                                             _explore_92427
                                               ( _right_92381,
                                                 fun (_x_92823 : int) ->
                                                   _k_92429
                                                     (coer_arrow coer_refl_ty
                                                        coer_refl_ty
                                                        (_op_256 _x_92382)
                                                        _x_92823) )
                                         in
                                         coer_arrow coer_refl_ty coer_refl_ty
                                           (fun (_s_92812 : int) ->
                                             coer_arrow coer_refl_ty
                                               coer_refl_ty
                                               (_op_267 (* @ *)
                                                  (coer_arrow coer_refl_ty
                                                     coer_refl_ty
                                                     (coer_arrow coer_refl_ty
                                                        coer_refl_ty
                                                        (_l_92811 true))
                                                     _s_92812))
                                               (coer_arrow coer_refl_ty
                                                  coer_refl_ty
                                                  (coer_arrow coer_refl_ty
                                                     coer_refl_ty
                                                     (_l_92811 false))
                                                  _s_92812))))
                                     (coer_arrow coer_refl_ty coer_refl_ty
                                        (( * ) _x_92382) _x_92382))
                         in
                         _explore_92427
                           ( ____t_92291,
                             fun (_x_92371 : int) ->
                               coer_arrow coer_refl_ty coer_refl_ty
                                 (fun (_ : int) ->
                                   Cons
                                     (coer_tuple_2
                                        (coer_refl_ty, coer_refl_ty)
                                        (_x_92371, Nil))) )))
                     ~-1))))
  in
  coer_arrow coer_refl_ty coer_refl_ty (_looper_92350 100) 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_92281
