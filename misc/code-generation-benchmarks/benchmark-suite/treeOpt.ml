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
  let rec _find_max_133 (_x_115, _k_135) =
    match _x_115 with
    | Empty -> _k_135 0
    | Node (Empty, _x_123, Empty) -> _k_135 _x_123
    | Node (_left_126, _x_125, _right_124) ->
        let _l_116 (_y_127 : bool) =
          if _y_127 then
            _find_max_133
              (_left_126, fun (_next_128 : int) -> _k_135 (_x_125 + _next_128))
          else
            _find_max_133
              (_right_124, fun (_next_128 : int) -> _k_135 (_x_125 + _next_128))
        in
        _max_88 (_l_116 true) (_l_116 false)
  in
  _find_max_133 (_tester_42 _m_94, fun (_x_110 : int) -> _x_110)

let effect_max = _effect_max_93

let _test_max_138 (_m_139 : int) = _effect_max_93 _m_139

let test_max = _test_max_138

let _op_140 (_x_141 : int) (_y_142 : int) = _x_141 - (3 * _y_142)

let op = _op_140

let _max_146 (_a_147 : int) (_b_148 : int) =
  if _a_147 > _b_148 then _a_147 else _b_148

let max = _max_146

type intlist = Nil | Cons of (int * intlist)

let rec _op_151 (* @ *) _x_158 (_ys_160 : intlist) =
  match _x_158 with
  | Nil -> _ys_160
  | Cons (_x_162, _xs_161) -> Cons (_x_162, _op_151 (* @ *) _xs_161 _ys_160)

let _op_151 (* @ *) = _op_151 (* @ *)

let _test_general_165 (_m_166 : int) =
  let rec _maxl_167 _x_197 (_x_232 : intlist) =
    match _x_232 with
    | Nil -> _x_197
    | Cons (_x_234, _xs_233) -> _maxl_167 (_max_146 _x_234 _x_197) _xs_233
  in
  _maxl_167 0
    (let rec _explore_226 (_x_200, _k_228) =
       match _x_200 with
       | Empty -> _k_228 0
       | Node (_left_216, _x_215, _right_214) ->
           let _l_201 (_y_217 : bool) =
             if _y_217 then
               _explore_226
                 ( _left_216,
                   fun (_b_220 : int) -> _k_228 (_op_140 _x_215 _b_220) )
             else
               _explore_226
                 ( _right_214,
                   fun (_b_222 : int) -> _k_228 (_op_140 _x_215 _b_222) )
           in
           _op_151 (* @ *) (_l_201 true) (_l_201 false)
     in
     _explore_226 (_tester_42 _m_166, fun (_x_192 : int) -> Cons (_x_192, Nil)))

let test_general = _test_general_165

let _test_general_loop_238 (_m_239 : int) =
  let rec _maxl_240 _x_282 (_x_342 : intlist) =
    match _x_342 with
    | Nil -> _x_282
    | Cons (_x_344, _xs_343) -> _maxl_240 (_max_146 _x_344 _x_282) _xs_343
  in
  let ____t_248 = _tester_42 _m_239 in
  let rec _looper_302 _x_303 (_s_304 : int) =
    if _x_303 = 0 then _s_304
    else
      _looper_302 (_x_303 - 1)
        (_s_304
        + _maxl_240 0
            (let rec _explore_336 (_x_285, _k_338) =
               match _x_285 with
               | Empty -> _k_338 0
               | Node (_left_326, _x_325, _right_324) ->
                   let _l_286 (_y_327 : bool) =
                     if _y_327 then
                       _explore_336
                         ( _left_326,
                           fun (_b_330 : int) -> _k_338 (_op_140 _x_325 _b_330)
                         )
                     else
                       _explore_336
                         ( _right_324,
                           fun (_b_332 : int) -> _k_338 (_op_140 _x_325 _b_332)
                         )
                   in
                   _op_151 (* @ *) (_l_286 true) (_l_286 false)
             in
             _explore_336 (____t_248, fun (_x_265 : int) -> Cons (_x_265, Nil)))
        )
  in
  _looper_302 100 0

let test_general_loop = _test_general_loop_238

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_348 (_void_349 : float) = match _void_349 with _ -> assert false

let absurd = _absurd_348

let _test_leaf_state_350 (_m_351 : int) =
  let rec _maxl_352 _x_403 (_x_738 : intlist) =
    match _x_738 with
    | Nil -> _x_403
    | Cons (_x_740, _xs_739) -> _maxl_352 (_max_146 _x_740 _x_403) _xs_739
  in
  let rec _populate_leafs_360 _x_404 (_n_474 : int) =
    if _x_404 = _n_474 then Nil
    else Cons (_x_404 * 3, _populate_leafs_360 (_x_404 + 1) _n_474)
  in
  _maxl_352 0
    ((let rec _explore_444 (_x_409, _k_446) =
        match _x_409 with
        | Empty -> Call (Get, (), fun (_y_434 : int) -> _k_446 _y_434)
        | Node (_left_437, _x_436, _right_435) ->
            let _l_410 (_y_438 : bool) =
              _explore_444
                ( (if _y_438 then _left_437 else _right_435),
                  fun (_b_441 : int) -> _k_446 (_op_140 _x_436 _b_441) )
            in
            _l_410 true >> fun _b_386 ->
            _l_410 false >> fun _b_387 -> Value (_op_151 (* @ *) _b_386 _b_387)
      in
      let rec _explore_448 (_x_409, _k_446) =
        match _x_409 with
        | Empty -> (
            fun (_s_450 : intlist) ->
              match _s_450 with
              | Cons (_x_452, _rest_451) ->
                  force_unsafe
                    ((handler
                        {
                          value_clause =
                            (fun (_x_455 : intlist) ->
                              Value (fun (_ : intlist) -> _x_455));
                          effect_clauses =
                            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                 (a -> (b -> _) -> _) ->
                              match eff with
                              | Get ->
                                  fun () _l_456 ->
                                    Value
                                      (fun (_s_457 : intlist) ->
                                        match _s_457 with
                                        | Cons (_x_459, _rest_458) ->
                                            coer_arrow coer_refl_ty force_unsafe
                                              _l_456 _x_459 _rest_458
                                        | Nil -> Nil)
                              | eff' -> fun arg k -> Call (eff', arg, k));
                        })
                       (_k_446 _x_452))
                    _rest_451
              | Nil -> Nil)
        | Node (_left_437, _x_436, _right_435) ->
            let _l_410 (_y_438 : bool) =
              _explore_444
                ( (if _y_438 then _left_437 else _right_435),
                  fun (_b_441 : int) -> _k_446 (_op_140 _x_436 _b_441) )
            in
            force_unsafe
              ((handler
                  {
                    value_clause =
                      (fun (_b_386 : intlist) ->
                        Value
                          (force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_b_387 : intlist) ->
                                       Value
                                         (fun (_ : intlist) ->
                                           _op_151 (* @ *) _b_386 _b_387));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l_423 ->
                                             Value
                                               (fun (_s_424 : intlist) ->
                                                 match _s_424 with
                                                 | Cons (_x_426, _rest_425) ->
                                                     coer_arrow coer_refl_ty
                                                       force_unsafe _l_423
                                                       _x_426 _rest_425
                                                 | Nil -> Nil)
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_l_410 false))));
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | Get ->
                            fun () _l_423 ->
                              Value
                                (fun (_s_424 : intlist) ->
                                  match _s_424 with
                                  | Cons (_x_426, _rest_425) ->
                                      coer_arrow coer_refl_ty force_unsafe
                                        _l_423 _x_426 _rest_425
                                  | Nil -> Nil)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  })
                 (_l_410 true))
      in
      _explore_448
        (_tester_42 _m_351, fun (_x_388 : int) -> Value (Cons (_x_388, Nil))))
       (_populate_leafs_360 0 154))

let test_leaf_state = _test_leaf_state_350

let _test_leaf_state_loop_1088 (_m_1089 : int) =
  let rec _maxl_1090 _x_1153 (_x_1526 : intlist) =
    match _x_1526 with
    | Nil -> _x_1153
    | Cons (_x_1528, _xs_1527) -> _maxl_1090 (_max_146 _x_1528 _x_1153) _xs_1527
  in
  let rec _populate_leafs_1098 _x_1154 (_n_1262 : int) =
    if _x_1154 = _n_1262 then Nil
    else Cons (_x_1154 * 3, _populate_leafs_1098 (_x_1154 + 1) _n_1262)
  in
  let ____leafs_1109 = _populate_leafs_1098 0 154 in
  let ____t_1111 = _tester_42 _m_1089 in
  let rec _looper_1195 _x_1196 (_s_1197 : int) =
    if _x_1196 = 0 then _s_1197
    else
      _looper_1195 (_x_1196 - 1)
        (_s_1197
        + _maxl_1090 0
            ((let rec _explore_1232 (_x_1159, _k_1234) =
                match _x_1159 with
                | Empty -> Call (Get, (), fun (_y_1222 : int) -> _k_1234 _y_1222)
                | Node (_left_1225, _x_1224, _right_1223) ->
                    let _l_1160 (_y_1226 : bool) =
                      _explore_1232
                        ( (if _y_1226 then _left_1225 else _right_1223),
                          fun (_b_1229 : int) ->
                            _k_1234 (_op_140 _x_1224 _b_1229) )
                    in
                    _l_1160 true >> fun _b_1124 ->
                    _l_1160 false >> fun _b_1125 ->
                    Value (_op_151 (* @ *) _b_1124 _b_1125)
              in
              let rec _explore_1236 (_x_1159, _k_1234) =
                match _x_1159 with
                | Empty -> (
                    fun (_s_1238 : intlist) ->
                      match _s_1238 with
                      | Cons (_x_1240, _rest_1239) ->
                          force_unsafe
                            ((handler
                                {
                                  value_clause =
                                    (fun (_x_1243 : intlist) ->
                                      Value (fun (_ : intlist) -> _x_1243));
                                  effect_clauses =
                                    (fun (type a b)
                                         (eff : (a, b) eff_internal_effect) :
                                         (a -> (b -> _) -> _) ->
                                      match eff with
                                      | Get ->
                                          fun () _l_1244 ->
                                            Value
                                              (fun (_s_1245 : intlist) ->
                                                match _s_1245 with
                                                | Cons (_x_1247, _rest_1246) ->
                                                    coer_arrow coer_refl_ty
                                                      force_unsafe _l_1244
                                                      _x_1247 _rest_1246
                                                | Nil -> Nil)
                                      | eff' -> fun arg k -> Call (eff', arg, k));
                                })
                               (_k_1234 _x_1240))
                            _rest_1239
                      | Nil -> Nil)
                | Node (_left_1225, _x_1224, _right_1223) ->
                    let _l_1160 (_y_1226 : bool) =
                      _explore_1232
                        ( (if _y_1226 then _left_1225 else _right_1223),
                          fun (_b_1229 : int) ->
                            _k_1234 (_op_140 _x_1224 _b_1229) )
                    in
                    force_unsafe
                      ((handler
                          {
                            value_clause =
                              (fun (_b_1124 : intlist) ->
                                Value
                                  (force_unsafe
                                     ((handler
                                         {
                                           value_clause =
                                             (fun (_b_1125 : intlist) ->
                                               Value
                                                 (fun (_ : intlist) ->
                                                   _op_151 (* @ *) _b_1124
                                                     _b_1125));
                                           effect_clauses =
                                             (fun (type a b)
                                                  (eff :
                                                    (a, b) eff_internal_effect)
                                                  : (a -> (b -> _) -> _) ->
                                               match eff with
                                               | Get ->
                                                   fun () _l_1210 ->
                                                     Value
                                                       (fun (_s_1211 : intlist) ->
                                                         match _s_1211 with
                                                         | Cons
                                                             ( _x_1213,
                                                               _rest_1212 ) ->
                                                             coer_arrow
                                                               coer_refl_ty
                                                               force_unsafe
                                                               _l_1210 _x_1213
                                                               _rest_1212
                                                         | Nil -> Nil)
                                               | eff' ->
                                                   fun arg k ->
                                                     Call (eff', arg, k));
                                         })
                                        (_l_1160 false))));
                            effect_clauses =
                              (fun (type a b) (eff : (a, b) eff_internal_effect)
                                   : (a -> (b -> _) -> _) ->
                                match eff with
                                | Get ->
                                    fun () _l_1210 ->
                                      Value
                                        (fun (_s_1211 : intlist) ->
                                          match _s_1211 with
                                          | Cons (_x_1213, _rest_1212) ->
                                              coer_arrow coer_refl_ty
                                                force_unsafe _l_1210 _x_1213
                                                _rest_1212
                                          | Nil -> Nil)
                                | eff' -> fun arg k -> Call (eff', arg, k));
                          })
                         (_l_1160 true))
              in
              _explore_1236
                (____t_1111, fun (_x_1126 : int) -> Value (Cons (_x_1126, Nil))))
               ____leafs_1109))
  in
  _looper_1195 100 0

let test_leaf_state_loop = _test_leaf_state_loop_1088

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_1876 (_m_1877 : int) =
  let rec _maxl_1878 _x_1920 (_x_2292 : intlist) =
    match _x_2292 with
    | Nil -> _x_1920
    | Cons (_x_2294, _xs_2293) -> _maxl_1878 (_max_146 _x_2294 _x_1920) _xs_2293
  in
  _maxl_1878 0
    ((let rec _explore_1971 (_x_1927, _k_1973) =
        match _x_1927 with
        | Empty -> Call (Get, (), fun (_y_1958 : int) -> _k_1973 _y_1958)
        | Node (_left_1961, _x_1960, _right_1959) ->
            Call
              ( Set,
                _x_1960 * _x_1960,
                fun (_y_1964 : unit) ->
                  let _l_1928 (_y_1965 : bool) =
                    _explore_1971
                      ( (if _y_1965 then _left_1961 else _right_1959),
                        fun (_b_1968 : int) -> _k_1973 (_op_140 _x_1960 _b_1968)
                      )
                  in
                  _l_1928 true >> fun _b_1901 ->
                  _l_1928 false >> fun _b_1902 ->
                  Value (_op_151 (* @ *) _b_1901 _b_1902) )
      in
      let rec _explore_1975 (_x_1927, _k_1973) (_x_0 : int) =
        match _x_1927 with
        | Empty ->
            force_unsafe
              ((handler
                  {
                    value_clause =
                      (fun (_x_1980 : intlist) ->
                        Value (fun (_ : int) -> _x_1980));
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | Get ->
                            fun () _l_1981 ->
                              Value
                                (fun (_s_1982 : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _l_1981
                                    _s_1982 _s_1982)
                        | Set ->
                            fun _s_1984 _l_1985 ->
                              Value
                                (fun (_ : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _l_1985
                                    () _s_1984)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  })
                 (_k_1973 _x_0))
              _x_0
        | Node (_left_1961, _x_1960, _right_1959) ->
            (let _l_1991 (_y_2008 : bool) =
               _explore_1971
                 ( (if _y_2008 then _left_1961 else _right_1959),
                   fun (_b_2011 : int) -> _k_1973 (_op_140 _x_1960 _b_2011) )
             in
             force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_b_1992 : intlist) ->
                         Value
                           (force_unsafe
                              ((handler
                                  {
                                    value_clause =
                                      (fun (_b_1994 : intlist) ->
                                        Value
                                          (fun (_ : int) ->
                                            _op_151 (* @ *) _b_1992 _b_1994));
                                    effect_clauses =
                                      (fun (type a b)
                                           (eff : (a, b) eff_internal_effect) :
                                           (a -> (b -> _) -> _) ->
                                        match eff with
                                        | Get ->
                                            fun () _l_1996 ->
                                              Value
                                                (fun (_s_1997 : int) ->
                                                  coer_arrow coer_refl_ty
                                                    force_unsafe _l_1996 _s_1997
                                                    _s_1997)
                                        | Set ->
                                            fun _s_1999 _l_2000 ->
                                              Value
                                                (fun (_ : int) ->
                                                  coer_arrow coer_refl_ty
                                                    force_unsafe _l_2000 ()
                                                    _s_1999)
                                        | eff' ->
                                            fun arg k -> Call (eff', arg, k));
                                  })
                                 (_l_1991 false))));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_2002 ->
                               Value
                                 (fun (_s_2003 : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_2002
                                     _s_2003 _s_2003)
                         | Set ->
                             fun _s_2005 _l_2006 ->
                               Value
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_2006
                                     () _s_2005)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (_l_1991 true)))
              (_x_1960 * _x_1960)
      in
      _explore_1975
        (_tester_42 _m_1877, fun (_x_1903 : int) -> Value (Cons (_x_1903, Nil))))
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_1876

let _test_leaf_state_update_loop_10985 (_m_10986 : int) =
  let rec _maxl_10987 _x_11041 (_x_11452 : intlist) =
    match _x_11452 with
    | Nil -> _x_11041
    | Cons (_x_11454, _xs_11453) ->
        _maxl_10987 (_max_146 _x_11454 _x_11041) _xs_11453
  in
  let ____t_10995 = _tester_42 _m_10986 in
  let rec _looper_11087 _x_11088 (_s_11089 : int) =
    if _x_11088 = 0 then _s_11089
    else
      _looper_11087 (_x_11088 - 1)
        (_s_11089
        + _maxl_10987 0
            ((let rec _explore_11131 (_x_11048, _k_11133) =
                match _x_11048 with
                | Empty ->
                    Call (Get, (), fun (_y_11118 : int) -> _k_11133 _y_11118)
                | Node (_left_11121, _x_11120, _right_11119) ->
                    Call
                      ( Set,
                        _x_11120 * _x_11120,
                        fun (_y_11124 : unit) ->
                          let _l_11049 (_y_11125 : bool) =
                            _explore_11131
                              ( (if _y_11125 then _left_11121 else _right_11119),
                                fun (_b_11128 : int) ->
                                  _k_11133 (_op_140 _x_11120 _b_11128) )
                          in
                          _l_11049 true >> fun _b_11010 ->
                          _l_11049 false >> fun _b_11011 ->
                          Value (_op_151 (* @ *) _b_11010 _b_11011) )
              in
              let rec _explore_11135 (_x_11048, _k_11133) (_x_1 : int) =
                match _x_11048 with
                | Empty ->
                    force_unsafe
                      ((handler
                          {
                            value_clause =
                              (fun (_x_11140 : intlist) ->
                                Value (fun (_ : int) -> _x_11140));
                            effect_clauses =
                              (fun (type a b) (eff : (a, b) eff_internal_effect)
                                   : (a -> (b -> _) -> _) ->
                                match eff with
                                | Get ->
                                    fun () _l_11141 ->
                                      Value
                                        (fun (_s_11142 : int) ->
                                          coer_arrow coer_refl_ty force_unsafe
                                            _l_11141 _s_11142 _s_11142)
                                | Set ->
                                    fun _s_11144 _l_11145 ->
                                      Value
                                        (fun (_ : int) ->
                                          coer_arrow coer_refl_ty force_unsafe
                                            _l_11145 () _s_11144)
                                | eff' -> fun arg k -> Call (eff', arg, k));
                          })
                         (_k_11133 _x_1))
                      _x_1
                | Node (_left_11121, _x_11120, _right_11119) ->
                    (let _l_11151 (_y_11168 : bool) =
                       _explore_11131
                         ( (if _y_11168 then _left_11121 else _right_11119),
                           fun (_b_11171 : int) ->
                             _k_11133 (_op_140 _x_11120 _b_11171) )
                     in
                     force_unsafe
                       ((handler
                           {
                             value_clause =
                               (fun (_b_11152 : intlist) ->
                                 Value
                                   (force_unsafe
                                      ((handler
                                          {
                                            value_clause =
                                              (fun (_b_11154 : intlist) ->
                                                Value
                                                  (fun (_ : int) ->
                                                    _op_151 (* @ *) _b_11152
                                                      _b_11154));
                                            effect_clauses =
                                              (fun (type a b)
                                                   (eff :
                                                     (a, b) eff_internal_effect)
                                                   : (a -> (b -> _) -> _) ->
                                                match eff with
                                                | Get ->
                                                    fun () _l_11156 ->
                                                      Value
                                                        (fun (_s_11157 : int) ->
                                                          coer_arrow
                                                            coer_refl_ty
                                                            force_unsafe
                                                            _l_11156 _s_11157
                                                            _s_11157)
                                                | Set ->
                                                    fun _s_11159 _l_11160 ->
                                                      Value
                                                        (fun (_ : int) ->
                                                          coer_arrow
                                                            coer_refl_ty
                                                            force_unsafe
                                                            _l_11160 () _s_11159)
                                                | eff' ->
                                                    fun arg k ->
                                                      Call (eff', arg, k));
                                          })
                                         (_l_11151 false))));
                             effect_clauses =
                               (fun (type a b)
                                    (eff : (a, b) eff_internal_effect) :
                                    (a -> (b -> _) -> _) ->
                                 match eff with
                                 | Get ->
                                     fun () _l_11162 ->
                                       Value
                                         (fun (_s_11163 : int) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_11162 _s_11163 _s_11163)
                                 | Set ->
                                     fun _s_11165 _l_11166 ->
                                       Value
                                         (fun (_ : int) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_11166 () _s_11165)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (_l_11151 true)))
                      (_x_11120 * _x_11120)
              in
              _explore_11135
                ( ____t_10995,
                  fun (_x_11012 : int) -> Value (Cons (_x_11012, Nil)) ))
               ~-1))
  in
  _looper_11087 100 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_10985

let _test_leaf_state_update_merged_handler_20145 (_m_20146 : int) =
  let rec _maxl_20147 _x_20188 (_x_20256 : intlist) =
    match _x_20256 with
    | Nil -> _x_20188
    | Cons (_x_20258, _xs_20257) ->
        _maxl_20147 (_max_146 _x_20258 _x_20188) _xs_20257
  in
  _maxl_20147 0
    ((let rec _explore_20231 (_x_20195, _k_20233) (_x_2 : int) =
        match _x_20195 with
        | Empty -> _k_20233 _x_2 _x_2
        | Node (_left_20216, _x_20215, _right_20214) ->
            (let _l_20243 (_y_20250 : bool) =
               _explore_20231
                 ( (if _y_20250 then _left_20216 else _right_20214),
                   fun (_b_20253 : int) -> _k_20233 (_op_140 _x_20215 _b_20253)
                 )
             in
             fun (_s_20244 : int) ->
               _op_151
                 (* @ *) (_l_20243 true _s_20244)
                 (_l_20243 false _s_20244))
              (_x_20215 * _x_20215)
      in
      _explore_20231
        ( _tester_42 _m_20146,
          fun (_x_20181 : int) (_ : int) -> Cons (_x_20181, Nil) ))
       ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_20145

let _test_leaf_state_update_merged_handler_loop_20262 (_m_20263 : int) =
  let rec _maxl_20264 _x_20317 (_x_20412 : intlist) =
    match _x_20412 with
    | Nil -> _x_20317
    | Cons (_x_20414, _xs_20413) ->
        _maxl_20264 (_max_146 _x_20414 _x_20317) _xs_20413
  in
  let ____t_20272 = _tester_42 _m_20263 in
  let rec _looper_20345 _x_20346 (_s_20347 : int) =
    if _x_20346 = 0 then _s_20347
    else
      _looper_20345 (_x_20346 - 1)
        (_s_20347
        + _maxl_20264 0
            ((let rec _explore_20387 (_x_20324, _k_20389) (_x_3 : int) =
                match _x_20324 with
                | Empty -> _k_20389 _x_3 _x_3
                | Node (_left_20372, _x_20371, _right_20370) ->
                    (let _l_20399 (_y_20406 : bool) =
                       _explore_20387
                         ( (if _y_20406 then _left_20372 else _right_20370),
                           fun (_b_20409 : int) ->
                             _k_20389 (_op_140 _x_20371 _b_20409) )
                     in
                     fun (_s_20400 : int) ->
                       _op_151
                         (* @ *) (_l_20399 true _s_20400)
                         (_l_20399 false _s_20400))
                      (_x_20371 * _x_20371)
              in
              _explore_20387
                ( ____t_20272,
                  fun (_x_20298 : int) (_ : int) -> Cons (_x_20298, Nil) ))
               ~-1))
  in
  _looper_20345 100 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_20262
