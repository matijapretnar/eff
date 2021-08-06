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
       (_find_max_95 (_tester_42 _m_94)))

let effect_max = _effect_max_93

let _test_max_147 (_m_148 : int) = _effect_max_93 _m_148

let test_max = _test_max_147

let _op_149 (_x_150 : int) (_y_151 : int) = _x_150 - (3 * _y_151)

let op = _op_149

let _max_155 (_a_156 : int) (_b_157 : int) =
  if _a_156 > _b_157 then _a_156 else _b_157

let max = _max_155

type intlist = Nil | Cons of (int * intlist)

let rec _op_160 (* @ *) _x_167 (_ys_169 : intlist) =
  match _x_167 with
  | Nil -> _ys_169
  | Cons (_x_171, _xs_170) -> Cons (_x_171, _op_160 (* @ *) _xs_170 _ys_169)

let _op_160 (* @ *) = _op_160 (* @ *)

let _test_general_174 (_m_175 : int) =
  let rec _maxl_176 _x_206 (_x_846 : intlist) =
    match _x_846 with
    | Nil -> _x_206
    | Cons (_x_848, _xs_847) -> _maxl_176 (_max_155 _x_848 _x_206) _xs_847
  in
  let rec _explore_185 _x_209 =
    match _x_209 with
    | Empty -> Value 0
    | Node (_left_225, _x_224, _right_223) ->
        Call
          ( Choose,
            (),
            fun (_y_226 : bool) ->
              (if _y_226 then
               _explore_185 _left_225 >>= fun _b_229 ->
               Value (_op_149 _x_224 _b_229)
              else
                _explore_185 _right_223 >>= fun _b_231 ->
                Value (_op_149 _x_224 _b_231))
              >>= fun _next_227 -> Value _next_227 )
  in
  _maxl_176 0
    (force_unsafe
       ((handler
           {
             value_clause = (fun (_x_201 : int) -> Value (Cons (_x_201, Nil)));
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Choose ->
                     fun () _l_210 ->
                       Value
                         (_op_160 (* @ *)
                            (coer_arrow coer_refl_ty force_unsafe _l_210 true)
                            (coer_arrow coer_refl_ty force_unsafe _l_210 false))
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_explore_185 (_tester_42 _m_175))))

let test_general = _test_general_174

let _test_general_loop_1041 (_m_1042 : int) =
  let rec _maxl_1043 _x_1085 (_x_1750 : intlist) =
    match _x_1750 with
    | Nil -> _x_1085
    | Cons (_x_1752, _xs_1751) -> _maxl_1043 (_max_155 _x_1752 _x_1085) _xs_1751
  in
  let ____t_1051 = _tester_42 _m_1042 in
  let rec _explore_1052 _x_1088 =
    match _x_1088 with
    | Empty -> Value 0
    | Node (_left_1129, _x_1128, _right_1127) ->
        Call
          ( Choose,
            (),
            fun (_y_1130 : bool) ->
              (if _y_1130 then
               _explore_1052 _left_1129 >>= fun _b_1133 ->
               Value (_op_149 _x_1128 _b_1133)
              else
                _explore_1052 _right_1127 >>= fun _b_1135 ->
                Value (_op_149 _x_1128 _b_1135))
              >>= fun _next_1131 -> Value _next_1131 )
  in
  let rec _looper_1105 _x_1106 (_s_1107 : int) =
    if _x_1106 = 0 then _s_1107
    else
      _looper_1105 (_x_1106 - 1)
        (_s_1107
        + _maxl_1043 0
            (force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_1068 : int) -> Value (Cons (_x_1068, Nil)));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Choose ->
                             fun () _l_1089 ->
                               Value
                                 (_op_160 (* @ *)
                                    (coer_arrow coer_refl_ty force_unsafe
                                       _l_1089 true)
                                    (coer_arrow coer_refl_ty force_unsafe
                                       _l_1089 false))
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (_explore_1052 ____t_1051))))
  in
  _looper_1105 100 0

let test_general_loop = _test_general_loop_1041

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_1945 (_void_1946 : float) =
  match _void_1946 with _ -> assert false

let absurd = _absurd_1945

let _test_leaf_state_1947 (_m_1948 : int) =
  let rec _maxl_1949 _x_2000 (_x_21754 : intlist) =
    match _x_21754 with
    | Nil -> _x_2000
    | Cons (_x_21756, _xs_21755) ->
        _maxl_1949 (_max_155 _x_21756 _x_2000) _xs_21755
  in
  let rec _populate_leafs_1957 _x_2001 (_n_19416 : int) =
    if _x_2001 = _n_19416 then Nil
    else Cons (_x_2001 * 3, _populate_leafs_1957 (_x_2001 + 1) _n_19416)
  in
  let rec _explore_1971 _x_2006 =
    match _x_2006 with
    | Empty -> Call (Get, (), fun (_y_2031 : int) -> Value _y_2031)
    | Node (_left_2034, _x_2033, _right_2032) ->
        Call
          ( Choose,
            (),
            fun (_y_2035 : bool) ->
              _explore_1971 (if _y_2035 then _left_2034 else _right_2032)
              >>= fun _b_2038 -> Value (_op_149 _x_2033 _b_2038) )
  in
  _maxl_1949 0
    (force_unsafe
       ((handler
           {
             value_clause =
               (fun (_x_2019 : intlist) -> Value (fun (_ : intlist) -> _x_2019));
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Get ->
                     fun () _l_2020 ->
                       Value
                         (fun (_s_2021 : intlist) ->
                           match _s_2021 with
                           | Cons (_x_2023, _rest_2022) ->
                               coer_arrow coer_refl_ty force_unsafe _l_2020
                                 _x_2023 _rest_2022
                           | Nil -> Nil)
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          ((handler
              {
                value_clause =
                  (fun (_x_1985 : int) -> Value (Cons (_x_1985, Nil)));
                effect_clauses =
                  (fun (type a b) (eff : (a, b) eff_internal_effect) :
                       (a -> (b -> _) -> _) ->
                    match eff with
                    | Choose ->
                        fun () _l_2007 ->
                          _l_2007 true >>= fun _b_1983 ->
                          _l_2007 false >>= fun _b_1984 ->
                          Value (_op_160 (* @ *) _b_1983 _b_1984)
                    | eff' -> fun arg k -> Call (eff', arg, k));
              })
             (_explore_1971 (_tester_42 _m_1948))))
       (_populate_leafs_1957 0 154))

let test_leaf_state = _test_leaf_state_1947

let _test_leaf_state_loop_24394 (_m_24395 : int) =
  let rec _maxl_24396 _x_24459 (_x_44251 : intlist) =
    match _x_44251 with
    | Nil -> _x_24459
    | Cons (_x_44253, _xs_44252) ->
        _maxl_24396 (_max_155 _x_44253 _x_24459) _xs_44252
  in
  let rec _populate_leafs_24404 _x_24460 (_n_41913 : int) =
    if _x_24460 = _n_41913 then Nil
    else Cons (_x_24460 * 3, _populate_leafs_24404 (_x_24460 + 1) _n_41913)
  in
  let ____leafs_24415 = _populate_leafs_24404 0 154 in
  let ____t_24417 = _tester_42 _m_24395 in
  let rec _explore_24418 _x_24465 =
    match _x_24465 with
    | Empty -> Call (Get, (), fun (_y_24528 : int) -> Value _y_24528)
    | Node (_left_24531, _x_24530, _right_24529) ->
        Call
          ( Choose,
            (),
            fun (_y_24532 : bool) ->
              _explore_24418 (if _y_24532 then _left_24531 else _right_24529)
              >>= fun _b_24535 -> Value (_op_149 _x_24530 _b_24535) )
  in
  let rec _looper_24501 _x_24502 (_s_24503 : int) =
    if _x_24502 = 0 then _s_24503
    else
      _looper_24501 (_x_24502 - 1)
        (_s_24503
        + _maxl_24396 0
            (force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_24515 : intlist) ->
                         Value (fun (_ : intlist) -> _x_24515));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_24516 ->
                               Value
                                 (fun (_s_24517 : intlist) ->
                                   match _s_24517 with
                                   | Cons (_x_24519, _rest_24518) ->
                                       coer_arrow coer_refl_ty force_unsafe
                                         _l_24516 _x_24519 _rest_24518
                                   | Nil -> Nil)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  ((handler
                      {
                        value_clause =
                          (fun (_x_24432 : int) -> Value (Cons (_x_24432, Nil)));
                        effect_clauses =
                          (fun (type a b) (eff : (a, b) eff_internal_effect) :
                               (a -> (b -> _) -> _) ->
                            match eff with
                            | Choose ->
                                fun () _l_24466 ->
                                  _l_24466 true >>= fun _b_24430 ->
                                  _l_24466 false >>= fun _b_24431 ->
                                  Value (_op_160 (* @ *) _b_24430 _b_24431)
                            | eff' -> fun arg k -> Call (eff', arg, k));
                      })
                     (_explore_24418 ____t_24417)))
               ____leafs_24415))
  in
  _looper_24501 100 0

let test_leaf_state_loop = _test_leaf_state_loop_24394

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _test_leaf_state_update_46891 (_m_46892 : int) =
  let rec _maxl_46893 _x_46935 (_x_76379 : intlist) =
    match _x_76379 with
    | Nil -> _x_46935
    | Cons (_x_76381, _xs_76380) ->
        _maxl_46893 (_max_155 _x_76381 _x_46935) _xs_76380
  in
  let rec _explore_46902 _x_46942 =
    match _x_46942 with
    | Empty -> Call (Get, (), fun (_y_46973 : int) -> Value _y_46973)
    | Node (_left_46976, _x_46975, _right_46974) ->
        Call
          ( Set,
            _x_46975 * _x_46975,
            fun (_y_46979 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_46980 : bool) ->
                    _explore_46902
                      (if _y_46980 then _left_46976 else _right_46974)
                    >>= fun _b_46983 -> Value (_op_149 _x_46975 _b_46983) ) )
  in
  _maxl_46893 0
    (force_unsafe
       ((handler
           {
             value_clause =
               (fun (_x_46958 : intlist) -> Value (fun (_ : int) -> _x_46958));
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Get ->
                     fun () _l_46959 ->
                       Value
                         (fun (_s_46960 : int) ->
                           coer_arrow coer_refl_ty force_unsafe _l_46959
                             _s_46960 _s_46960)
                 | Set ->
                     fun _s_46962 _l_46963 ->
                       Value
                         (fun (_ : int) ->
                           coer_arrow coer_refl_ty force_unsafe _l_46963 ()
                             _s_46962)
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          ((handler
              {
                value_clause =
                  (fun (_x_46918 : int) -> Value (Cons (_x_46918, Nil)));
                effect_clauses =
                  (fun (type a b) (eff : (a, b) eff_internal_effect) :
                       (a -> (b -> _) -> _) ->
                    match eff with
                    | Choose ->
                        fun () _l_46943 ->
                          _l_46943 true >>= fun _b_46916 ->
                          _l_46943 false >>= fun _b_46917 ->
                          Value (_op_160 (* @ *) _b_46916 _b_46917)
                    | eff' -> fun arg k -> Call (eff', arg, k));
              })
             (_explore_46902 (_tester_42 _m_46892))))
       ~-1)

let test_leaf_state_update = _test_leaf_state_update_46891

let _test_leaf_state_update_loop_79887 (_m_79888 : int) =
  let rec _maxl_79889 _x_79943 (_x_109426 : intlist) =
    match _x_109426 with
    | Nil -> _x_79943
    | Cons (_x_109428, _xs_109427) ->
        _maxl_79889 (_max_155 _x_109428 _x_79943) _xs_109427
  in
  let ____t_79897 = _tester_42 _m_79888 in
  let rec _explore_79898 _x_79950 =
    match _x_79950 with
    | Empty -> Call (Get, (), fun (_y_80020 : int) -> Value _y_80020)
    | Node (_left_80023, _x_80022, _right_80021) ->
        Call
          ( Set,
            _x_80022 * _x_80022,
            fun (_y_80026 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_80027 : bool) ->
                    _explore_79898
                      (if _y_80027 then _left_80023 else _right_80021)
                    >>= fun _b_80030 -> Value (_op_149 _x_80022 _b_80030) ) )
  in
  let rec _looper_79989 _x_79990 (_s_79991 : int) =
    if _x_79990 = 0 then _s_79991
    else
      _looper_79989 (_x_79990 - 1)
        (_s_79991
        + _maxl_79889 0
            (force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_80004 : intlist) ->
                         Value (fun (_ : int) -> _x_80004));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_80005 ->
                               Value
                                 (fun (_s_80006 : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_80005
                                     _s_80006 _s_80006)
                         | Set ->
                             fun _s_80008 _l_80009 ->
                               Value
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l_80009
                                     () _s_80008)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  ((handler
                      {
                        value_clause =
                          (fun (_x_79914 : int) -> Value (Cons (_x_79914, Nil)));
                        effect_clauses =
                          (fun (type a b) (eff : (a, b) eff_internal_effect) :
                               (a -> (b -> _) -> _) ->
                            match eff with
                            | Choose ->
                                fun () _l_79951 ->
                                  _l_79951 true >>= fun _b_79912 ->
                                  _l_79951 false >>= fun _b_79913 ->
                                  Value (_op_160 (* @ *) _b_79912 _b_79913)
                            | eff' -> fun arg k -> Call (eff', arg, k));
                      })
                     (_explore_79898 ____t_79897)))
               ~-1))
  in
  _looper_79989 100 0

let test_leaf_state_update_loop = _test_leaf_state_update_loop_79887

let _test_leaf_state_update_merged_handler_112934 (_m_112935 : int) =
  let rec _maxl_112936 _x_112977 (_x_326925 : intlist) =
    match _x_326925 with
    | Nil -> _x_112977
    | Cons (_x_326927, _xs_326926) ->
        _maxl_112936 (_max_155 _x_326927 _x_112977) _xs_326926
  in
  let rec _explore_112945 _x_112984 =
    match _x_112984 with
    | Empty -> Call (Get, (), fun (_y_113002 : int) -> Value _y_113002)
    | Node (_left_113005, _x_113004, _right_113003) ->
        Call
          ( Set,
            _x_113004 * _x_113004,
            fun (_y_113008 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_113009 : bool) ->
                    _explore_112945
                      (if _y_113009 then _left_113005 else _right_113003)
                    >>= fun _b_113012 -> Value (_op_149 _x_113004 _b_113012) )
          )
  in
  _maxl_112936 0
    (force_unsafe
       ((handler
           {
             value_clause =
               (fun (_x_112970 : int) ->
                 Value (fun (_ : int) -> Cons (_x_112970, Nil)));
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Get ->
                     fun () _l_112985 ->
                       Value
                         (fun (_s_112958 : int) ->
                           coer_arrow coer_refl_ty force_unsafe _l_112985
                             _s_112958 _s_112958)
                 | Set ->
                     fun _s_112960 _l_112986 ->
                       Value
                         (fun (_ : int) ->
                           coer_arrow coer_refl_ty force_unsafe _l_112986 ()
                             _s_112960)
                 | Choose ->
                     fun () _l_112987 ->
                       Value
                         (fun (_s_112964 : int) ->
                           _op_160 (* @ *)
                             (coer_arrow coer_refl_ty force_unsafe _l_112987
                                true _s_112964)
                             (coer_arrow coer_refl_ty force_unsafe _l_112987
                                false _s_112964))
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_explore_112945 (_tester_42 _m_112935)))
       ~-1)

let test_leaf_state_update_merged_handler =
  _test_leaf_state_update_merged_handler_112934

let _test_leaf_state_update_merged_handler_loop_345178 (_m_345179 : int) =
  let rec _maxl_345180 _x_345233 (_x_559208 : intlist) =
    match _x_559208 with
    | Nil -> _x_345233
    | Cons (_x_559210, _xs_559209) ->
        _maxl_345180 (_max_155 _x_559210 _x_345233) _xs_559209
  in
  let ____t_345188 = _tester_42 _m_345179 in
  let rec _explore_345189 _x_345240 =
    match _x_345240 with
    | Empty -> Call (Get, (), fun (_y_345285 : int) -> Value _y_345285)
    | Node (_left_345288, _x_345287, _right_345286) ->
        Call
          ( Set,
            _x_345287 * _x_345287,
            fun (_y_345291 : unit) ->
              Call
                ( Choose,
                  (),
                  fun (_y_345292 : bool) ->
                    _explore_345189
                      (if _y_345292 then _left_345288 else _right_345286)
                    >>= fun _b_345295 -> Value (_op_149 _x_345287 _b_345295) )
          )
  in
  let rec _looper_345261 _x_345262 (_s_345263 : int) =
    if _x_345262 = 0 then _s_345263
    else
      _looper_345261 (_x_345262 - 1)
        (_s_345263
        + _maxl_345180 0
            (force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x_345214 : int) ->
                         Value (fun (_ : int) -> Cons (_x_345214, Nil)));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l_345241 ->
                               Value
                                 (fun (_s_345202 : int) ->
                                   coer_arrow coer_refl_ty force_unsafe
                                     _l_345241 _s_345202 _s_345202)
                         | Set ->
                             fun _s_345204 _l_345242 ->
                               Value
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty force_unsafe
                                     _l_345242 () _s_345204)
                         | Choose ->
                             fun () _l_345243 ->
                               Value
                                 (fun (_s_345208 : int) ->
                                   _op_160 (* @ *)
                                     (coer_arrow coer_refl_ty force_unsafe
                                        _l_345243 true _s_345208)
                                     (coer_arrow coer_refl_ty force_unsafe
                                        _l_345243 false _s_345208))
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (_explore_345189 ____t_345188))
               ~-1))
  in
  _looper_345261 100 0

let test_leaf_state_update_merged_handler_loop =
  _test_leaf_state_update_merged_handler_loop_345178
