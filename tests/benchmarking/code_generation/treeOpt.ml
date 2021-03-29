open OcamlHeader

type tree = Empty | Node of (tree * int * tree)

type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect

let _tester_45 (_k_46 : int) =
  let _leaf_47 (_a_48 : int) = Node (Empty, _a_48 * _k_46, Empty) in
  let _bot_51 (_t_52 : tree) (_t2_53 : tree) =
    Node
      ( Node (Node (_t_52, 0, _t2_53), 2, _leaf_47 13),
        5,
        Node (_leaf_47 9, 7, Node (_t2_53, 3, Node (_leaf_47 3, 5, _t2_53))) )
  in
  _bot_51
    (Node
       (_bot_51 (_leaf_47 3) (_leaf_47 4), 10, _bot_51 (_leaf_47 1) (_leaf_47 3)))
    (_bot_51
       (Node
          ( _bot_51 (_leaf_47 3) (_leaf_47 4),
            10,
            _bot_51 (_leaf_47 1) (_leaf_47 3) ))
       (_leaf_47 10))

let tester = _tester_45

let _max_91 (_a_92 : int) (_b_93 : int) = if _a_92 > _b_93 then _a_92 else _b_93

let max = _max_91

let _effect_max_96 (_m_97 : int) =
  let rec _find_max_98 _x_118 =
    match _x_118 with
    | Empty -> Value 0
    | Node (Empty, _x_126, Empty) -> Value _x_126
    | Node (_left_129, _x_128, _right_127) ->
        Call
          ( Choose,
            (),
            fun (_y_130 : bool) ->
              (if _y_130 then _find_max_98 _left_129
              else _find_max_98 _right_127)
              >> fun _next_131 -> Value (_x_128 + _next_131) )
  in
  let rec _find_max_136 (_x_118, _k_138) =
    match _x_118 with
    | Empty -> _k_138 0
    | Node (Empty, _x_126, Empty) -> _k_138 _x_126
    | Node (_left_129, _x_128, _right_127) ->
        let _l_119 (_y_130 : bool) =
          if _y_130 then
            _find_max_136
              (_left_129, fun (_next_131 : int) -> _k_138 (_x_128 + _next_131))
          else
            _find_max_136
              (_right_127, fun (_next_131 : int) -> _k_138 (_x_128 + _next_131))
        in
        _max_91 (_l_119 true) (_l_119 false)
  in
  _find_max_136 (_tester_45 _m_97, fun (_x_113 : int) -> _x_113)

let effect_max = _effect_max_96

let _test_max_141 (_m_142 : int) = _effect_max_96 _m_142

let test_max = _test_max_141

let _op_143 (_x_144 : int) (_y_145 : int) = _x_144 - (3 * _y_145)

let op = _op_143

let _max_149 (_a_150 : int) (_b_151 : int) =
  if _a_150 > _b_151 then _a_150 else _b_151

let max = _max_149

type intlist = Nil | Cons of (int * intlist)

let rec _op_154 (* @ *) _x_161 (_ys_163 : intlist) =
  match _x_161 with
  | Nil -> _ys_163
  | Cons (_x_165, _xs_164) -> Cons (_x_165, _op_154 (* @ *) _xs_164 _ys_163)

let _op_154 (* @ *) = _op_154 (* @ *)

let _test_general_168 (_m_169 : int) =
  let rec _maxl_170 _x_200 (_x_235 : intlist) =
    match _x_235 with
    | Nil -> _x_200
    | Cons (_x_237, _xs_236) -> _maxl_170 (_max_149 _x_237 _x_200) _xs_236
  in
  let rec _explore_179 _x_203 =
    match _x_203 with
    | Empty -> Value 0
    | Node (_left_219, _x_218, _right_217) ->
        Call
          ( Choose,
            (),
            fun (_y_220 : bool) ->
              (if _y_220 then
               _explore_179 _left_219 >> fun _b_223 ->
               Value (_op_143 _x_218 _b_223)
              else
                _explore_179 _right_217 >> fun _b_225 ->
                Value (_op_143 _x_218 _b_225))
              >> fun _next_221 -> Value _next_221 )
  in
  _maxl_170 0
    (let rec _explore_229 (_x_203, _k_231) =
       match _x_203 with
       | Empty -> _k_231 0
       | Node (_left_219, _x_218, _right_217) ->
           let _l_204 (_y_220 : bool) =
             if _y_220 then
               _explore_229
                 ( _left_219,
                   fun (_b_223 : int) -> _k_231 (_op_143 _x_218 _b_223) )
             else
               _explore_229
                 ( _right_217,
                   fun (_b_225 : int) -> _k_231 (_op_143 _x_218 _b_225) )
           in
           _op_154 (* @ *) (_l_204 true) (_l_204 false)
     in
     _explore_229 (_tester_45 _m_169, fun (_x_195 : int) -> Cons (_x_195, Nil)))

let test_general = _test_general_168

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

let _absurd_241 (_void_242 : float) = match _void_242 with _ -> assert false

let absurd = _absurd_241

let _test_leaf_state_243 (_m_244 : int) =
  let rec _maxl_245 _x_296 (_x_625 : intlist) =
    match _x_625 with
    | Nil -> _x_296
    | Cons (_x_627, _xs_626) -> _maxl_245 (_max_149 _x_627 _x_296) _xs_626
  in
  let rec _populate_leafs_253 _x_297 (_n_361 : int) =
    if _x_297 = _n_361 then Nil
    else Cons (_x_297 * 3, _populate_leafs_253 (_x_297 + 1) _n_361)
  in
  let rec _explore_267 _x_302 =
    match _x_302 with
    | Empty -> Call (Get, (), fun (_y_327 : int) -> Value _y_327)
    | Node (_left_330, _x_329, _right_328) ->
        Call
          ( Choose,
            (),
            fun (_y_331 : bool) ->
              _explore_267 (if _y_331 then _left_330 else _right_328)
              >> fun _b_334 -> Value (_op_143 _x_329 _b_334) )
  in
  _maxl_245 0
    ((let rec _explore_337 (_x_302, _k_339) =
        match _x_302 with
        | Empty -> Call (Get, (), fun (_y_327 : int) -> _k_339 _y_327)
        | Node (_left_330, _x_329, _right_328) ->
            let _l_303 (_y_331 : bool) =
              _explore_337
                ( (if _y_331 then _left_330 else _right_328),
                  fun (_b_334 : int) -> _k_339 (_op_143 _x_329 _b_334) )
            in
            _l_303 true >> fun _b_279 ->
            _l_303 false >> fun _b_280 -> Value (_op_154 (* @ *) _b_279 _b_280)
      in
      let rec _explore_341 (_x_302, _k_339) =
        match _x_302 with
        | Empty -> (
            fun (_s_343 : intlist) ->
              match _s_343 with
              | Cons (_x_345, _rest_344) ->
                  force_unsafe
                    ((handler
                        {
                          value_clause =
                            (fun (_x_348 : intlist) ->
                              Value (fun (_ : intlist) -> _x_348));
                          effect_clauses =
                            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                 (a -> (b -> _) -> _) ->
                              match eff with
                              | Get ->
                                  fun () _l_349 ->
                                    Value
                                      (fun (_s_350 : intlist) ->
                                        match _s_350 with
                                        | Cons (_x_352, _rest_351) ->
                                            coer_arrow coer_refl_ty force_unsafe
                                              _l_349 _x_352 _rest_351
                                        | Nil -> Nil)
                              | eff' -> fun arg k -> Call (eff', arg, k));
                        })
                       (_k_339 _x_345))
                    _rest_344
              | Nil -> Nil)
        | Node (_left_330, _x_329, _right_328) ->
            let _l_303 (_y_331 : bool) =
              _explore_337
                ( (if _y_331 then _left_330 else _right_328),
                  fun (_b_334 : int) -> _k_339 (_op_143 _x_329 _b_334) )
            in
            force_unsafe
              ((handler
                  {
                    value_clause =
                      (fun (_b_279 : intlist) ->
                        Value
                          (force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_b_280 : intlist) ->
                                       Value
                                         (fun (_ : intlist) ->
                                           _op_154 (* @ *) _b_279 _b_280));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l_316 ->
                                             Value
                                               (fun (_s_317 : intlist) ->
                                                 match _s_317 with
                                                 | Cons (_x_319, _rest_318) ->
                                                     coer_arrow coer_refl_ty
                                                       force_unsafe _l_316
                                                       _x_319 _rest_318
                                                 | Nil -> Nil)
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_l_303 false))));
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | Get ->
                            fun () _l_316 ->
                              Value
                                (fun (_s_317 : intlist) ->
                                  match _s_317 with
                                  | Cons (_x_319, _rest_318) ->
                                      coer_arrow coer_refl_ty force_unsafe
                                        _l_316 _x_319 _rest_318
                                  | Nil -> Nil)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  })
                 (_l_303 true))
      in
      _explore_341
        (_tester_45 _m_244, fun (_x_281 : int) -> Value (Cons (_x_281, Nil))))
       (_populate_leafs_253 0 154))

let test_leaf_state = _test_leaf_state_243
