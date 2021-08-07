open OcamlHeader

(* Manual value extractions *)
type tree = Empty | Node of (tree * int * tree)

type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect

let _tester_42 (_k_43 : int) =
  let _leaf_44 (_a_45 : int) =
    Value (( * ) _a_45) >>= fun _b_47 ->
    Value (_b_47 _k_43) >>= fun _b_46 -> Value (Node (Empty, _b_46, Empty))
  in
  let _bot_48 (_t_49 : tree) (_t2_50 : tree) =
    Value (_leaf_44 13) >>= fun _b_51 ->
    Value (_leaf_44 9) >>= fun _b_52 ->
    Value (_leaf_44 3) >>= fun _b_53 ->
    Value
      (Node
         ( Node (Node (_t_49, 0, _t2_50), 2, force_unsafe _b_51),
           5,
           Node
             ( force_unsafe _b_52,
               7,
               Node (_t2_50, 3, Node (force_unsafe _b_53, 5, _t2_50)) ) ))
  in
  Value (_leaf_44 3) >>= fun _b_57 ->
  Value (_bot_48 (force_unsafe _b_57)) >>= fun _b_56 ->
  Value (_leaf_44 4) >>= fun _b_58 ->
  Value (_b_56 (force_unsafe _b_58)) >>= fun _b_55 ->
  Value (_leaf_44 1) >>= fun _b_61 ->
  Value (_bot_48 (force_unsafe _b_61)) >>= fun _b_60 ->
  Value (_leaf_44 3) >>= fun _b_62 ->
  Value (_b_60 (force_unsafe _b_62)) >>= fun _b_59 ->
  Value (_leaf_44 3) >>= fun _b_76 ->
  Value (_bot_48 (force_unsafe _b_76)) >>= fun _b_77 ->
  Value (_leaf_44 4) >>= fun _b_78 ->
  Value (_b_77 (force_unsafe _b_78)) >>= fun _b_79 ->
  Value (_leaf_44 1) >>= fun _b_80 ->
  Value (_bot_48 (force_unsafe _b_80)) >>= fun _b_81 ->
  Value (_leaf_44 3) >>= fun _b_82 ->
  Value (_b_81 (force_unsafe _b_82)) >>= fun _b_83 ->
  Value (_bot_48 (Node (force_unsafe _b_79, 10, force_unsafe _b_83)))
  >>= fun _b_84 ->
  Value (_leaf_44 10) >>= fun _b_85 ->
  Value (_b_84 (force_unsafe _b_85)) >>= fun _n2_86 ->
  Value (_bot_48 (Node (force_unsafe _b_55, 10, force_unsafe _b_59)))
  >>= fun _b_87 -> _b_87 (force_unsafe _n2_86)

let tester = _tester_42

let _max_88 (_a_89 : int) (_b_90 : int) =
  Value (( > ) _a_89) >>= fun _b_92 ->
  Value (_b_92 _b_90) >>= fun _b_91 ->
  if _b_91 then Value _a_89 else Value _b_90

let max = _max_88

let _effect_max_93 (_m_94 : int) =
  Value (_tester_42 _m_94) >>= fun _t_104 ->
  let rec _find_max_141 (_x_115, _k_143) =
    match _x_115 with
    | Empty -> _k_143 0
    | Node (Empty, _x_123, Empty) -> _k_143 _x_123
    | Node (_left_126, _x_125, _right_124) ->
        let _l_116 (_y_127 : bool) =
          if _y_127 then
            _find_max_141
              ( _left_126,
                fun (_next_128 : int) ->
                  Value (( + ) _x_125) >>= fun _x_153 ->
                  Value (_x_153 _next_128) >>= fun _x_156 -> _k_143 _x_156 )
          else
            _find_max_141
              ( _right_124,
                fun (_next_128 : int) ->
                  Value (( + ) _x_125) >>= fun _x_153 ->
                  Value (_x_153 _next_128) >>= fun _x_159 -> _k_143 _x_159 )
        in
        Value (_l_116 true) >>= fun _b_108 ->
        Value (_max_88 (force_unsafe _b_108)) >>= fun _b_107 ->
        Value (_l_116 false) >>= fun _b_109 -> _b_107 (force_unsafe _b_109)
  in
  _find_max_141 (force_unsafe _t_104, fun (_x_110 : int) -> Value _x_110)

let effect_max = _effect_max_93

let _test_max_160 (_m_161 : int) = _effect_max_93 _m_161

let test_max = _test_max_160

let _op_162 (_x_163 : int) (_y_164 : int) =
  Value (( - ) _x_163) >>= fun _b_165 ->
  Value (( * ) 3) >>= fun _b_167 ->
  Value (_b_167 _y_164) >>= fun _b_166 -> Value (_b_165 _b_166)

let op = _op_162

let _max_168 (_a_169 : int) (_b_170 : int) =
  Value (( > ) _a_169) >>= fun _b_172 ->
  Value (_b_172 _b_170) >>= fun _b_171 ->
  if _b_171 then Value _a_169 else Value _b_170

let max = _max_168

type intlist = Nil | Cons of (int * intlist)

let rec _op_173 (* @ *) _x_180 (_ys_182 : intlist) : intlist computation =
  match _x_180 with
  | Nil -> Value _ys_182
  | Cons (_x_184, _xs_183) ->
      Value (_op_173 (* @ *) _xs_183) >>= fun _b_185 ->
      Value (_b_185 _ys_182) >>= fun _b_186 ->
      Value (Cons (_x_184, force_unsafe _b_186))

let _op_173 (* @ *) = _op_173 (* @ *)

let _test_general_187 (_m_188 : int) =
  let rec _maxl_189 _x_219 (_x_279 : intlist) : int computation =
    match _x_279 with
    | Nil -> Value _x_219
    | Cons (_x_281, _xs_280) ->
        Value (_max_168 _x_281) >>= fun _b_282 ->
        Value (_b_282 _x_219) >>= fun _b_283 ->
        Value (_maxl_189 (force_unsafe _b_283)) >>= fun _b_284 -> _b_284 _xs_280
  in
  Value (_tester_42 _m_188) >>= fun _t_197 ->
  Value (_maxl_189 0) >>= fun _b_226 ->
  Value
    (let rec _explore_255 (_x_222, _k_257) =
       match _x_222 with
       | Empty -> _k_257 0
       | Node (_left_238, _x_237, _right_236) ->
           let _l_223 (_y_239 : bool) =
             if _y_239 then
               Value (_op_162 _x_237) >>= fun _x_267 ->
               _explore_255
                 ( _left_238,
                   fun (_b_272 : int) ->
                     Value (_x_267 _b_272) >>= fun _x_273 ->
                     _k_257 (force_unsafe _x_273) )
             else
               Value (_op_162 _x_237) >>= fun _x_269 ->
               _explore_255
                 ( _right_236,
                   fun (_b_276 : int) ->
                     Value (_x_269 _b_276) >>= fun _x_277 ->
                     _k_257 (force_unsafe _x_277) )
           in
           Value (_l_223 true) >>= fun _b_212 ->
           Value (_op_173 (* @ *) (force_unsafe _b_212)) >>= fun _b_211 ->
           Value (_l_223 false) >>= fun _b_213 -> _b_211 (force_unsafe _b_213)
     in
     _explore_255
       (force_unsafe _t_197, fun (_x_214 : int) -> Value (Cons (_x_214, Nil))))
  >>= fun _b_227 -> _b_226 (force_unsafe _b_227)

let test_general x = force_unsafe (_test_general_187 x)

let _test_general_loop_285 (_m_286 : int) =
  let rec _maxl_287 _x_329 (_x_414 : intlist) : int computation =
    match _x_414 with
    | Nil -> Value _x_329
    | Cons (_x_416, _xs_415) ->
        Value (_max_168 _x_416) >>= fun _b_417 ->
        Value (_b_417 _x_329) >>= fun _b_418 ->
        Value (_maxl_287 (force_unsafe _b_418)) >>= fun _b_419 -> _b_419 _xs_415
  in
  Value (_tester_42 _m_286) >>= fun ____t_295 ->
  let rec _looper_349 _x_350 (_s_351 : int) =
    Value (( = ) _x_350) >>= fun _b_352 ->
    Value (_b_352 0) >>= fun _b_353 ->
    if _b_353 then Value _s_351
    else
      Value (( - ) _x_350) >>= fun _b_354 ->
      Value (_b_354 1) >>= fun _b_355 ->
      Value (_looper_349 _b_355) >>= fun _b_356 ->
      Value (( + ) _s_351) >>= fun _b_357 ->
      Value (_maxl_287 0) >>= fun _b_358 ->
      Value
        (let rec _explore_390 (_x_332, _k_392) =
           match _x_332 with
           | Empty -> _k_392 0
           | Node (_left_373, _x_372, _right_371) ->
               let _l_333 (_y_374 : bool) =
                 if _y_374 then
                   Value (_op_162 _x_372) >>= fun _x_402 ->
                   _explore_390
                     ( _left_373,
                       fun (_b_407 : int) ->
                         Value (_x_402 _b_407) >>= fun _x_408 ->
                         _k_392 (force_unsafe _x_408) )
                 else
                   Value (_op_162 _x_372) >>= fun _x_404 ->
                   _explore_390
                     ( _right_371,
                       fun (_b_411 : int) ->
                         Value (_x_404 _b_411) >>= fun _x_412 ->
                         _k_392 (force_unsafe _x_412) )
               in
               Value (_l_333 true) >>= fun _b_310 ->
               Value (_op_173 (* @ *) (force_unsafe _b_310)) >>= fun _b_309 ->
               Value (_l_333 false) >>= fun _b_311 ->
               _b_309 (force_unsafe _b_311)
         in
         _explore_390
           ( force_unsafe ____t_295,
             fun (_x_312 : int) -> Value (Cons (_x_312, Nil)) ))
      >>= fun _b_359 ->
      Value (_b_358 (force_unsafe _b_359)) >>= fun _b_360 ->
      Value (_b_357 (force_unsafe _b_360)) >>= fun _b_361 -> _b_356 _b_361
  in
  Value (_looper_349 100) >>= fun _b_362 -> _b_362 0

let test_general_loop x = force_unsafe( _test_general_loop_285 x)

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_420 (_void_421 : float) = match _void_421 with _ -> assert false

let absurd = _absurd_420

let _test_leaf_state_422 (_m_423 : int) : int = 1

(* let rec _maxl_424 _x_475 (_x_1533 : intlist) : int computation =
     match _x_1533 with
     | Nil -> Value _x_475
     | Cons (_x_1535, _xs_1534) ->
         Value (_max_168 _x_1535) >>= fun _b_1536 ->
         Value (_b_1536 _x_475) >>= fun _b_1537 ->
         Value (_maxl_424 (force_unsafe _b_1537)) >>= fun _b_1538 ->
         _b_1538 _xs_1534
   in
   let rec _populate_leafs_432 _x_476 (_n_634 : int) =
     Value (( = ) _x_476) >>= fun _b_635 ->
     Value (_b_635 _n_634) >>= fun _b_636 ->
     if _b_636 then Value Nil
     else
       Value (( * ) _x_476) >>= fun _b_637 ->
       Value (_b_637 3) >>= fun _b_638 ->
       Value (( + ) _x_476) >>= fun _b_639 ->
       Value (_b_639 1) >>= fun _b_640 ->
       Value (_populate_leafs_432 _b_640) >>= fun _b_641 ->
       Value (_b_641 _n_634) >>= fun _b_642 ->
       Value (Cons (_b_638, force_unsafe _b_642))
   in
   Value (_populate_leafs_432 0) >>= fun _b_444 ->
   Value (_b_444 154) >>= fun _leafs_443 ->
   Value (_tester_42 _m_423) >>= fun _t_445 ->
   Value (_maxl_424 0) >>= fun _b_491 ->
   Value
     (let rec _explore_523 (_x_481, _k_525) =
        match _x_481 with
        | Empty -> Call (Get, (), fun (_y_506 : int) -> _k_525 _y_506)
        | Node (_left_509, _x_508, _right_507) ->
            let _l_482 (_y_510 : bool) =
              if _y_510 then
                Value (_op_162 _x_508) >>= fun _x_554 ->
                _explore_523
                  ( _left_509,
                    fun (_b_555 : int) ->
                      Value (_x_554 _b_555) >>= fun _x_556 ->
                      _k_525 (force_unsafe _x_556) )
              else
                Value (_op_162 _x_508) >>= fun _x_574 ->
                _explore_523
                  ( _right_507,
                    fun (_b_575 : int) ->
                      Value (_x_574 _b_575) >>= fun _x_576 ->
                      _k_525 (force_unsafe _x_576) )
            in
            _l_482 true >>= fun _b_458 ->
            Value (_op_173 (* @ *) _b_458) >>= fun _b_457 ->
            _l_482 false >>= fun _b_459 -> _b_457 _b_459
      in
      let rec _explore_577 (_x_481, _k_525) =
        match _x_481 with
        | Empty -> (
            fun (_s_579 : intlist) ->
              match _s_579 with
              | Cons (_x_581, _rest_580) ->
                  Value
                    (force_unsafe
                       ((handler
                           {
                             value_clause =
                               (fun (_x_584 : intlist) ->
                                 Value (fun (_ : intlist) -> _x_584));
                             effect_clauses =
                               (fun (type a b) (eff : (a, b) eff_internal_effect)
                                    : (a -> (b -> _) -> _) ->
                                 match eff with
                                 | Get ->
                                     fun (() : unit) _l_585 ->
                                       Value
                                         (fun (_s_586 : intlist) ->
                                           match _s_586 with
                                           | Cons (_x_588, _rest_587) ->
                                               Value
                                                 (coer_arrow coer_refl_ty
                                                    force_unsafe _l_585 _x_588)
                                               >>= fun _b_589 -> _b_589 _rest_587
                                           | Nil -> Nil)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (_k_525 _x_581)))
                  >>= fun _b_582 -> Value (_b_582 _rest_580)
              | Nil -> Value Nil)
        | Node (_left_509, _x_508, _right_507) ->
            let _l_482 (_y_510 : bool) =
              if _y_510 then
                Value (_op_162 _x_508) >>= fun _x_554 ->
                _explore_523
                  ( _left_509,
                    fun (_b_555 : int) ->
                      Value (_x_554 _b_555) >>= fun _x_556 ->
                      _k_525 (force_unsafe _x_556) )
              else
                Value (_op_162 _x_508) >>= fun _x_574 ->
                _explore_523
                  ( _right_507,
                    fun (_b_575 : int) ->
                      Value (_x_574 _b_575) >>= fun _x_576 ->
                      _k_525 (force_unsafe _x_576) )
            in
            force_unsafe
              ((handler
                  {
                    value_clause =
                      (fun (_b_458 : intlist) ->
                        Value
                          ( Value (_op_173 (* @ *) _b_458) >>= fun _x_591 ->
                            force_unsafe
                              ((handler
                                  {
                                    value_clause =
                                      (fun (_b_594 : intlist) ->
                                        Value
                                          ( Value (_x_591 _b_594)
                                          >>= fun _x_595 (_ : intlist) -> _x_595
                                          ));
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
                                                      Value
                                                        (coer_arrow coer_refl_ty
                                                           force_unsafe _l_596
                                                           _x_599)
                                                      >>= fun _b_600 ->
                                                      _b_600 _rest_598
                                                  | Nil -> Nil)
                                        | eff' -> fun arg k -> Call (eff', arg, k));
                                  })
                                 (_l_482 false)) ));
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
                                      Value
                                        (coer_arrow coer_refl_ty force_unsafe
                                           _l_495 _x_498)
                                      >>= fun _b_499 -> _b_499 _rest_497
                                  | Nil -> Nil)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  })
                 (_l_482 true))
      in
      _explore_577
        (force_unsafe _t_445, fun (_x_460 : int) -> Value (Cons (_x_460, Nil))))
   >>= fun _b_492 ->
   Value (_b_492 (force_unsafe _leafs_443)) >>= fun _b_493 ->
   _b_491 (force_unsafe _b_493) *)

let test_leaf_state = _test_leaf_state_422

let _test_leaf_state_loop_2631 (_m_2632 : int) = 1

(* let rec _maxl_2633 _x_2696 (_x_3792 : intlist) : int computation =
     match _x_3792 with
     | Nil -> Value _x_2696
     | Cons (_x_3794, _xs_3793) ->
         Value (_max_168 _x_3794) >>= fun _b_3795 ->
         Value (_b_3795 _x_2696) >>= fun _b_3796 ->
         Value (_maxl_2633 (force_unsafe _b_3796)) >>= fun _b_3797 ->
         _b_3797 _xs_3793
   in
   let rec _populate_leafs_2641 _x_2697 (_n_2893 : int) =
     Value (( = ) _x_2697) >>= fun _b_2894 ->
     Value (_b_2894 _n_2893) >>= fun _b_2895 ->
     if _b_2895 then Value Nil
     else
       Value (( * ) _x_2697) >>= fun _b_2896 ->
       Value (_b_2896 3) >>= fun _b_2897 ->
       Value (( + ) _x_2697) >>= fun _b_2898 ->
       Value (_b_2898 1) >>= fun _b_2899 ->
       Value (_populate_leafs_2641 _b_2899) >>= fun _b_2900 ->
       Value (_b_2900 _n_2893) >>= fun _b_2901 ->
       Value (Cons (_b_2897, force_unsafe _b_2901))
   in
   Value (_populate_leafs_2641 0) >>= fun _b_2653 ->
   Value (_b_2653 154) >>= fun ____leafs_2652 ->
   Value (_tester_42 _m_2632) >>= fun ____t_2654 ->
   let rec _looper_2738 _x_2739 (_s_2740 : int) =
     Value (( = ) _x_2739) >>= fun _b_2741 ->
     Value (_b_2741 0) >>= fun _b_2742 ->
     if _b_2742 then Value _s_2740
     else
       Value (( - ) _x_2739) >>= fun _b_2743 ->
       Value (_b_2743 1) >>= fun _b_2744 ->
       Value (_looper_2738 _b_2744) >>= fun _b_2745 ->
       Value (( + ) _s_2740) >>= fun _b_2746 ->
       Value (_maxl_2633 0) >>= fun _b_2747 ->
       Value
         (let rec _explore_2782 (_x_2702, _k_2784) =
            match _x_2702 with
            | Empty -> Call (Get, (), fun (_y_2765 : int) -> _k_2784 _y_2765)
            | Node (_left_2768, _x_2767, _right_2766) ->
                let _l_2703 (_y_2769 : bool) =
                  if _y_2769 then
                    Value (_op_162 _x_2767) >>= fun _x_2813 ->
                    _explore_2782
                      ( _left_2768,
                        fun (_b_2814 : int) ->
                          Value (_x_2813 _b_2814) >>= fun _x_2815 ->
                          _k_2784 (force_unsafe _x_2815) )
                  else
                    Value (_op_162 _x_2767) >>= fun _x_2833 ->
                    _explore_2782
                      ( _right_2766,
                        fun (_b_2834 : int) ->
                          Value (_x_2833 _b_2834) >>= fun _x_2835 ->
                          _k_2784 (force_unsafe _x_2835) )
                in
                _l_2703 true >>= fun _b_2667 ->
                Value (_op_173 (* @ *) _b_2667) >>= fun _b_2666 ->
                _l_2703 false >>= fun _b_2668 -> _b_2666 _b_2668
          in
          let rec _explore_2836 (_x_2702, _k_2784) =
            match _x_2702 with
            | Empty -> (
                fun (_s_2838 : intlist) ->
                  match _s_2838 with
                  | Cons (_x_2840, _rest_2839) ->
                      Value
                        (force_unsafe
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
                                                   Value
                                                     (coer_arrow coer_refl_ty
                                                        force_unsafe _l_2844
                                                        _x_2847)
                                                   >>= fun _b_2848 ->
                                                   _b_2848 _rest_2846
                                               | Nil -> Nil)
                                     | eff' -> fun arg k -> Call (eff', arg, k));
                               })
                              (_k_2784 _x_2840)))
                      >>= fun _b_2841 -> Value (_b_2841 _rest_2839)
                  | Nil -> Value Nil)
            | Node (_left_2768, _x_2767, _right_2766) ->
                let _l_2703 (_y_2769 : bool) =
                  if _y_2769 then
                    Value (_op_162 _x_2767) >>= fun _x_2813 ->
                    _explore_2782
                      ( _left_2768,
                        fun (_b_2814 : int) ->
                          Value (_x_2813 _b_2814) >>= fun _x_2815 ->
                          _k_2784 (force_unsafe _x_2815) )
                  else
                    Value (_op_162 _x_2767) >>= fun _x_2833 ->
                    _explore_2782
                      ( _right_2766,
                        fun (_b_2834 : int) ->
                          Value (_x_2833 _b_2834) >>= fun _x_2835 ->
                          _k_2784 (force_unsafe _x_2835) )
                in
                force_unsafe
                  ((handler
                      {
                        value_clause =
                          (fun (_b_2667 : intlist) ->
                            Value
                              ( Value (_op_173 (* @ *) _b_2667) >>= fun _x_2850 ->
                                force_unsafe
                                  ((handler
                                      {
                                        value_clause =
                                          (fun (_b_2853 : intlist) ->
                                            Value
                                              ( Value (_x_2850 _b_2853)
                                              >>= fun _x_2854 (_ : intlist) ->
                                                _x_2854 ));
                                        effect_clauses =
                                          (fun (type a b)
                                               (eff : (a, b) eff_internal_effect)
                                               : (a -> (b -> _) -> _) ->
                                            match eff with
                                            | Get ->
                                                fun () _l_2855 ->
                                                  Value
                                                    (fun (_s_2856 : intlist) ->
                                                      match _s_2856 with
                                                      | Cons (_x_2858, _rest_2857)
                                                        ->
                                                          Value
                                                            (coer_arrow
                                                               coer_refl_ty
                                                               force_unsafe
                                                               _l_2855 _x_2858)
                                                          >>= fun _b_2859 ->
                                                          _b_2859 _rest_2857
                                                      | Nil -> Nil)
                                            | eff' ->
                                                fun arg k -> Call (eff', arg, k));
                                      })
                                     (_l_2703 false)) ));
                        effect_clauses =
                          (fun (type a b) (eff : (a, b) eff_internal_effect) :
                               (a -> (b -> _) -> _) ->
                            match eff with
                            | Get ->
                                fun () _l_2753 ->
                                  Value
                                    (fun (_s_2754 : intlist) ->
                                      match _s_2754 with
                                      | Cons (_x_2756, _rest_2755) ->
                                          Value
                                            (coer_arrow coer_refl_ty force_unsafe
                                               _l_2753 _x_2756)
                                          >>= fun _b_2757 -> _b_2757 _rest_2755
                                      | Nil -> Nil)
                            | eff' -> fun arg k -> Call (eff', arg, k));
                      })
                     (_l_2703 true))
          in
          _explore_2836
            ( force_unsafe ____t_2654,
              fun (_x_2669 : int) -> Value (Cons (_x_2669, Nil)) ))
       >>= fun _b_2748 ->
       Value (_b_2748 (force_unsafe ____leafs_2652)) >>= fun _b_2749 ->
       Value (_b_2747 (force_unsafe _b_2749)) >>= fun _b_2750 ->
       Value (_b_2746 (force_unsafe _b_2750)) >>= fun _b_2751 -> _b_2745 _b_2751
   in
   Value (_looper_2738 100) >>= fun _b_2758 -> _b_2758 0 *)

let test_leaf_state_loop = _test_leaf_state_loop_2631

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_4890 (_m_4891 : int) = 1

(* let rec _maxl_4892 (_x_4934 : int) (_x_5594 : intlist) : int computation =
     match _x_5594 with
     | Nil -> Value _x_4934
     | Cons (_x_5596, _xs_5595) ->
         Value (_max_168 _x_5596) >>= fun _b_5597 ->
         Value (_b_5597 _x_4934) >>= fun _b_5598 ->
         Value (_maxl_4892 (force_unsafe _b_5598)) >>= fun _b_5599 ->
         _b_5599 _xs_5595
   in
   Value (_tester_42 _m_4891) >>= fun _t_4900 ->
   Value (_maxl_4892 0) >>= fun _b_4953 ->
   Value
     (let rec _explore_4992 (_x_4941, _k_4994) =
        match _x_4941 with
        | Empty -> Call (Get, (), fun (_y_4972 : int) -> _k_4994 _y_4972)
        | Node (_left_4975, _x_4974, _right_4973) ->
            Value (( * ) _x_4974) >>= fun _x_5049 ->
            Value (_x_5049 _x_4974) >>= fun _x_5091 ->
            Call
              ( Set,
                _x_5091,
                fun (_y_5092 : unit) ->
                  let _l_5093 (_y_5097 : bool) =
                    if _y_5097 then
                      Value (_op_162 _x_4974) >>= fun _x_5098 ->
                      _explore_4992
                        ( _left_4975,
                          fun (_b_5099 : int) ->
                            Value (_x_5098 _b_5099) >>= fun _x_5100 ->
                            _k_4994 _x_5100 )
                    else
                      Value (_op_162 _x_4974) >>= fun _x_5101 ->
                      _explore_4992
                        ( _right_4973,
                          fun (_b_5102 : int) ->
                            Value (_x_5101 _b_5102) >>= fun _x_5103 ->
                            _k_4994 _x_5103 )
                  in
                  _l_5093 true >>= fun _b_5094 ->
                  Value (_op_173 (* @ *) _b_5094) >>= fun _b_5095 ->
                  _l_5093 false >>= fun _b_5096 -> Value (_b_5095 _b_5096) )
      in
      let rec _explore_5104 (_x_4941, _k_4994) =
        match _x_4941 with
        | Empty ->
            fun (_s_5106 : int) ->
              Value
                (force_unsafe
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
                                       Value
                                         (coer_arrow coer_refl_ty force_unsafe
                                            _l_5110 _s_5111)
                                       >>= fun _b_5112 -> _b_5112 _s_5111)
                             | Set ->
                                 fun _s_5113 _l_5114 ->
                                   Value
                                     (fun (_ : int) ->
                                       Value
                                         (coer_arrow coer_refl_ty force_unsafe
                                            _l_5114 ())
                                       >>= fun _b_5115 -> _b_5115 _s_5113)
                             | eff' -> fun arg k -> Call (eff', arg, k));
                       })
                      (_k_4994 _s_5106)))
              >>= fun _b_5107 -> Value (_b_5107 _s_5106)
        | Node (_left_4975, _x_4974, _right_4973) ->
            Value (( * ) _x_4974) >>= fun _x_5285 ->
            Value (_x_5285 _x_4974) >>= fun _x_5440 (_ : int) ->
            Value
              (let _l_5442 (_y_5459 : bool) =
                 if _y_5459 then
                   Value (_op_162 _x_4974) >>= fun _x_5460 ->
                   _explore_4992
                     ( _left_4975,
                       fun (_b_5461 : int) ->
                         Value (_x_5460 _b_5461) >>= fun _x_5462 ->
                         _k_4994 _x_5462 )
                 else
                   Value (_op_162 _x_4974) >>= fun _x_5463 ->
                   _explore_4992
                     ( _right_4973,
                       fun (_b_5464 : int) ->
                         Value (_x_5463 _b_5464) >>= fun _x_5465 ->
                         _k_4994 _x_5465 )
               in
               force_unsafe
                 ((handler
                     {
                       value_clause =
                         (fun (_b_5443 : intlist) ->
                           Value
                             ( Value (_op_173 (* @ *) _b_5443) >>= fun _x_5444 ->
                               force_unsafe
                                 ((handler
                                     {
                                       value_clause =
                                         (fun (_b_5445 : intlist) ->
                                           Value
                                             ( Value (_x_5444 _b_5445)
                                             >>= fun _x_5446 (_ : int) -> _x_5446
                                             ));
                                       effect_clauses =
                                         (fun (type a b)
                                              (eff : (a, b) eff_internal_effect)
                                              : (a -> (b -> _) -> _) ->
                                           match eff with
                                           | Get ->
                                               fun () _l_5447 ->
                                                 Value
                                                   (fun (_s_5448 : int) ->
                                                     Value
                                                       (coer_arrow coer_refl_ty
                                                          force_unsafe _l_5447
                                                          _s_5448)
                                                     >>= fun _b_5449 ->
                                                     _b_5449 _s_5448)
                                           | Set ->
                                               fun _s_5450 _l_5451 ->
                                                 Value
                                                   (fun (_ : int) ->
                                                     Value
                                                       (coer_arrow coer_refl_ty
                                                          force_unsafe _l_5451 ())
                                                     >>= fun _b_5452 ->
                                                     _b_5452 _s_5450)
                                           | eff' ->
                                               fun arg k -> Call (eff', arg, k));
                                     })
                                    (_l_5442 false)) ));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Get ->
                               fun () _l_5453 ->
                                 Value
                                   (fun (_s_5454 : int) ->
                                     Value
                                       (coer_arrow coer_refl_ty force_unsafe
                                          _l_5453 _s_5454)
                                     >>= fun _b_5455 -> _b_5455 _s_5454)
                           | Set ->
                               fun _s_5456 _l_5457 ->
                                 Value
                                   (fun (_ : int) ->
                                     Value
                                       (coer_arrow coer_refl_ty force_unsafe
                                          _l_5457 ())
                                     >>= fun _b_5458 -> _b_5458 _s_5456)
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     })
                    (_l_5442 true)))
            >>= fun _b_5441 -> _b_5441 _x_5440
      in
      _explore_5104
        (force_unsafe _t_4900, fun (_x_4917 : int) -> Value (Cons (_x_4917, Nil))))
   >>= fun _b_4954 ->
   Value ~-1 >>= fun _b_4955 ->
   Value (_b_4954 _b_4955) >>= fun _b_4956 ->
   Value (_b_4953 (force_unsafe _b_4956)) *)

let test_leaf_state_update = _test_leaf_state_update_4890

let _test_leaf_state_update_loop_21688 (_m_21689 : int) = 1

(* let rec _maxl_21690 _x_21744 (_x_22443 : intlist) : int computation =
     match _x_22443 with
     | Nil -> Value _x_21744
     | Cons (_x_22445, _xs_22444) ->
         Value (_max_168 _x_22445) >>= fun _b_22446 ->
         Value (_b_22446 _x_21744) >>= fun _b_22447 ->
         Value (_maxl_21690 (force_unsafe _b_22447)) >>= fun _b_22448 ->
         _b_22448 _xs_22444
   in
   Value (_tester_42 _m_21689) >>= fun ____t_21698 ->
   let rec _looper_21790 _x_21791 (_s_21792 : int) =
     Value (( = ) _x_21791) >>= fun _b_21793 ->
     Value (_b_21793 0) >>= fun _b_21794 ->
     if _b_21794 then Value _s_21792
     else
       Value (( - ) _x_21791) >>= fun _b_21795 ->
       Value (_b_21795 1) >>= fun _b_21796 ->
       Value (_looper_21790 _b_21796) >>= fun _b_21797 ->
       Value (( + ) _s_21792) >>= fun _b_21798 ->
       Value (_maxl_21690 0) >>= fun _b_21799 ->
       Value
         (let rec _explore_21841 (_x_21751, _k_21843) =
            match _x_21751 with
            | Empty -> Call (Get, (), fun (_y_21821 : int) -> _k_21843 _y_21821)
            | Node (_left_21824, _x_21823, _right_21822) ->
                Value (( * ) _x_21823) >>= fun _x_21898 ->
                Value (_x_21898 _x_21823) >>= fun _x_21940 ->
                Call
                  ( Set,
                    _x_21940,
                    fun (_y_21941 : unit) ->
                      let _l_21942 (_y_21946 : bool) =
                        if _y_21946 then
                          Value (_op_162 _x_21823) >>= fun _x_21947 ->
                          _explore_21841
                            ( _left_21824,
                              fun (_b_21948 : int) ->
                                Value (_x_21947 _b_21948) >>= fun _x_21949 ->
                                _k_21843 (force_unsafe _x_21949) )
                        else
                          Value (_op_162 _x_21823) >>= fun _x_21950 ->
                          _explore_21841
                            ( _right_21822,
                              fun (_b_21951 : int) ->
                                Value (_x_21950 _b_21951) >>= fun _x_21952 ->
                                _k_21843 (force_unsafe _x_21952) )
                      in
                      _l_21942 true >>= fun _b_21943 ->
                      Value (_op_173 (* @ *) _b_21943) >>= fun _b_21944 ->
                      _l_21942 false >>= fun _b_21945 ->
                      Value (_b_21944 _b_21945) )
          in
          let rec _explore_21953 (_x_21751, _k_21843) =
            match _x_21751 with
            | Empty ->
                fun (_s_21955 : int) ->
                  Value
                    (force_unsafe
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
                                           Value
                                             (coer_arrow coer_refl_ty
                                                force_unsafe _l_21959 _s_21960)
                                           >>= fun _b_21961 -> _b_21961 _s_21960)
                                 | Set ->
                                     fun _s_21962 _l_21963 ->
                                       Value
                                         (fun (_ : int) ->
                                           Value
                                             (coer_arrow coer_refl_ty
                                                force_unsafe _l_21963 ())
                                           >>= fun _b_21964 -> _b_21964 _s_21962)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (_k_21843 _s_21955)))
                  >>= fun _b_21956 -> _b_21956 _s_21955
            | Node (_left_21824, _x_21823, _right_21822) ->
                Value (( * ) _x_21823) >>= fun _x_22134 ->
                Value (_x_22134 _x_21823) >>= fun _x_22289 (_ : int) ->
                Value
                  (let _l_22291 (_y_22308 : bool) =
                     if _y_22308 then
                       Value (_op_162 _x_21823) >>= fun _x_22309 ->
                       _explore_21841
                         ( _left_21824,
                           fun (_b_22310 : int) ->
                             Value (_x_22309 _b_22310) >>= fun _x_22311 ->
                             _k_21843 _x_22311 )
                     else
                       Value (_op_162 _x_21823) >>= fun _x_22312 ->
                       _explore_21841
                         ( _right_21822,
                           fun (_b_22313 : int) ->
                             Value (_x_22312 _b_22313) >>= fun _x_22314 ->
                             _k_21843 _x_22314 )
                   in
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_b_22292 : intlist) ->
                               Value
                                 ( Value (_op_173 (* @ *) _b_22292)
                                 >>= fun _x_22293 ->
                                   force_unsafe
                                     ((handler
                                         {
                                           value_clause =
                                             (fun (_b_22294 : intlist) ->
                                               Value
                                                 ( Value (_x_22293 _b_22294)
                                                 >>= fun _x_22295 (_ : int) ->
                                                   _x_22295 ));
                                           effect_clauses =
                                             (fun (type a b)
                                                  (eff :
                                                    (a, b) eff_internal_effect) :
                                                  (a -> (b -> _) -> _) ->
                                               match eff with
                                               | Get ->
                                                   fun () _l_22296 ->
                                                     Value
                                                       (fun (_s_22297 : int) ->
                                                         Value
                                                           (coer_arrow
                                                              coer_refl_ty
                                                              force_unsafe
                                                              _l_22296 _s_22297)
                                                         >>= fun _b_22298 ->
                                                         _b_22298 _s_22297)
                                               | Set ->
                                                   fun _s_22299 _l_22300 ->
                                                     Value
                                                       (fun (_ : int) ->
                                                         Value
                                                           (coer_arrow
                                                              coer_refl_ty
                                                              force_unsafe
                                                              _l_22300 ())
                                                         >>= fun _b_22301 ->
                                                         _b_22301 _s_22299)
                                               | eff' ->
                                                   fun arg k ->
                                                     Call (eff', arg, k));
                                         })
                                        (_l_22291 false)) ));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                  (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l_22302 ->
                                     Value
                                       (fun (_s_22303 : int) ->
                                         Value
                                           (coer_arrow coer_refl_ty force_unsafe
                                              _l_22302 _s_22303)
                                         >>= fun _b_22304 -> _b_22304 _s_22303)
                               | Set ->
                                   fun _s_22305 _l_22306 ->
                                     Value
                                       (fun (_ : int) ->
                                         Value
                                           (coer_arrow coer_refl_ty force_unsafe
                                              _l_22306 ())
                                         >>= fun _b_22307 -> _b_22307 _s_22305)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_l_22291 true)))
                >>= fun _b_22290 -> _b_22290 _x_22289
          in
          _explore_21953
            ( force_unsafe ____t_21698,
              fun (_x_21715 : int) -> Value (Cons (_x_21715, Nil)) ))
       >>= fun _b_21800 ->
       Value ~-1 >>= fun _b_21801 ->
       Value (_b_21800 _b_21801) >>= fun _b_21802 ->
       Value (_b_21799 (force_unsafe _b_21802)) >>= fun _b_21803 ->
       Value (_b_21798 (force_unsafe _b_21803)) >>= fun _b_21804 ->
       _b_21797 _b_21804
   in
   Value (_looper_21790 100) >>= fun _b_21812 -> _b_21812 0 *)

let test_leaf_state_update_loop = _test_leaf_state_update_loop_21688

let _test_leaf_state_update_merged_handler_38537 (_m_38538 : int) = 1

(* let rec _maxl_38539 _x_38580 (_x_38777 : intlist) =
     match _x_38777 with
     | Nil -> Value _x_38580
     | Cons (_x_38779, _xs_38778) ->
         Value (_max_168 _x_38779) >>= fun _b_38780 ->
         Value (_b_38780 _x_38580) >>= fun _b_38781 ->
         Value (_maxl_38539 (force_unsafe _b_38781)) >>= fun _b_38782 ->
         _b_38782 _xs_38778
   in
   Value (_tester_42 _m_38538) >>= fun _t_38547 ->
   Value (_maxl_38539 0) >>= fun _b_38593 ->
   Value
     (let rec _explore_38630 (_x_38587, _k_38632) =
        match _x_38587 with
        | Empty ->
            fun (_s_38641 : int) ->
              Value (_k_38632 _s_38641) >>= fun _b_38642 -> _b_38642 _s_38641
        | Node (_left_38608, _x_38607, _right_38606) ->
            Value (( * ) _x_38607) >>= fun _x_38709 ->
            Value (_x_38709 _x_38607) >>= fun _x_38760 (_ : int) ->
            Value
              (let _l_38762 (_y_38769 : bool) =
                 if _y_38769 then
                   Value (_op_162 _x_38607) >>= fun _x_38770 ->
                   _explore_38630
                     ( _left_38608,
                       fun (_b_38771 : int) ->
                         Value (_x_38770 _b_38771) >>= fun _x_38772 ->
                         _k_38632 _x_38772 )
                 else
                   Value (_op_162 _x_38607) >>= fun _x_38773 ->
                   _explore_38630
                     ( _right_38606,
                       fun (_b_38774 : int) ->
                         Value (_x_38773 _b_38774) >>= fun _x_38775 ->
                         _k_38632 _x_38775 )
               in
               fun (_s_38763 : int) ->
                 Value (_l_38762 true) >>= fun _b_38764 ->
                 Value (_b_38764 _s_38763) >>= fun _b_38765 ->
                 Value (_op_173 (* @ *) _b_38765) >>= fun _b_38766 ->
                 Value (_l_38762 false) >>= fun _b_38767 ->
                 Value (_b_38767 _s_38763) >>= fun _b_38768 -> _b_38766 _b_38768)
            >>= fun _b_38761 -> _b_38761 _x_38760
      in
      _explore_38630
        ( force_unsafe _t_38547,
          fun (_x_38573 : int) (_ : int) -> Value (Cons (_x_38573, Nil)) ))
   >>= fun _b_38594 ->
   Value ~-1 >>= fun _b_38595 ->
   Value (_b_38594 _b_38595) >>= fun _b_38596 ->
   Value (_b_38593 (force_unsafe _b_38596)) *)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_38537

let _test_leaf_state_update_merged_handler_loop_38783 (_m_38784 : int) = 1

(* let rec _maxl_38785 _x_38838 (_x_39062 : intlist) =
     match _x_39062 with
     | Nil -> Value _x_38838
     | Cons (_x_39064, _xs_39063) ->
         Value (_max_168 _x_39064) >>= fun _b_39065 ->
         Value (_b_39065 _x_38838) >>= fun _b_39066 ->
         Value (_maxl_38785 (force_unsafe _b_39066)) >>= fun _b_39067 ->
         _b_39067 _xs_39063
   in
   Value (_tester_42 _m_38784) >>= fun ____t_38793 ->
   let rec _looper_38866 _x_38867 (_s_38868 : int) =
     Value (( = ) _x_38867) >>= fun _b_38869 ->
     Value (_b_38869 0) >>= fun _b_38870 ->
     if _b_38870 then Value _s_38868
     else
       Value (( - ) _x_38867) >>= fun _b_38871 ->
       Value (_b_38871 1) >>= fun _b_38872 ->
       Value (_looper_38866 _b_38872) >>= fun _b_38873 ->
       Value (( + ) _s_38868) >>= fun _b_38874 ->
       Value (_maxl_38785 0) >>= fun _b_38875 ->
       Value
         (let rec _explore_38915 (_x_38845, _k_38917) =
            match _x_38845 with
            | Empty ->
                fun (_s_38926 : int) ->
                  Value (_k_38917 _s_38926) >>= fun _b_38927 -> _b_38927 _s_38926
            | Node (_left_38893, _x_38892, _right_38891) ->
                Value (( * ) _x_38892) >>= fun _x_38994 ->
                Value (_x_38994 _x_38892) >>= fun _x_39045 (_ : int) ->
                Value
                  (let _l_39047 (_y_39054 : bool) =
                     if _y_39054 then
                       Value (_op_162 _x_38892) >>= fun _x_39055 ->
                       _explore_38915
                         ( _left_38893,
                           fun (_b_39056 : int) ->
                             Value (_x_39055 _b_39056) >>= fun _x_39057 ->
                             _k_38917 _x_39057 )
                     else
                       Value (_op_162 _x_38892) >>= fun _x_39058 ->
                       _explore_38915
                         ( _right_38891,
                           fun (_b_39059 : int) ->
                             Value (_x_39058 _b_39059) >>= fun _x_39060 ->
                             _k_38917 _x_39060 )
                   in
                   fun (_s_39048 : int) ->
                     Value (_l_39047 true) >>= fun _b_39049 ->
                     Value (_b_39049 _s_39048) >>= fun _b_39050 ->
                     Value (_op_173 (* @ *) _b_39050) >>= fun _b_39051 ->
                     Value (_l_39047 false) >>= fun _b_39052 ->
                     Value (_b_39052 _s_39048) >>= fun _b_39053 ->
                     _b_39051 _b_39053)
                >>= fun _b_39046 -> _b_39046 _x_39045
          in
          _explore_38915
            ( force_unsafe ____t_38793,
              fun (_x_38819 : int) (_ : int) -> Value (Cons (_x_38819, Nil)) ))
       >>= fun _b_38876 ->
       Value ~-1 >>= fun _b_38877 ->
       Value (_b_38876 _b_38877) >>= fun _b_38878 ->
       Value (_b_38875 (force_unsafe _b_38878)) >>= fun _b_38879 ->
       Value (_b_38874 (force_unsafe _b_38879)) >>= fun _b_38880 ->
       _b_38873 _b_38880
   in
   Value (_looper_38866 100) >>= fun _b_38881 -> _b_38881 0 *)

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_38783
