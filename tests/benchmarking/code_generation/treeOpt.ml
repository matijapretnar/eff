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

type intlist = Nil | Cons of (int * intlist)

let rec _op_149 (* @ *) _x_156 (_ys_158 : intlist) =
  match _x_156 with
  | Nil -> _ys_158
  | Cons (_x_160, _xs_159) -> Cons (_x_160, _op_149 (* @ *) _xs_159 _ys_158)

let _op_149 (* @ *) = _op_149 (* @ *)

let _test_general_163 (_m_164 : int) =
  let rec _maxl_165 _x_195 (_x_230 : intlist) =
    match _x_230 with
    | Nil -> _x_195
    | Cons (_x_232, _xs_231) -> _maxl_165 (_max_91 _x_232 _x_195) _xs_231
  in
  let rec _explore_174 _x_198 =
    match _x_198 with
    | Empty -> Value 0
    | Node (_left_214, _x_213, _right_212) ->
        Call
          ( Choose,
            (),
            fun (_y_215 : bool) ->
              (if _y_215 then
               _explore_174 _left_214 >> fun _b_218 ->
               Value (_op_143 _x_213 _b_218)
              else
                _explore_174 _right_212 >> fun _b_220 ->
                Value (_op_143 _x_213 _b_220))
              >> fun _next_216 -> Value _next_216 )
  in
  _maxl_165 0
    (let rec _explore_224 (_x_198, _k_226) =
       match _x_198 with
       | Empty -> _k_226 0
       | Node (_left_214, _x_213, _right_212) ->
           let _l_199 (_y_215 : bool) =
             if _y_215 then
               _explore_224
                 ( _left_214,
                   fun (_b_218 : int) -> _k_226 (_op_143 _x_213 _b_218) )
             else
               _explore_224
                 ( _right_212,
                   fun (_b_220 : int) -> _k_226 (_op_143 _x_213 _b_220) )
           in
           _op_149 (* @ *) (_l_199 true) (_l_199 false)
     in
     _explore_224 (_tester_45 _m_164, fun (_x_190 : int) -> Cons (_x_190, Nil)))

let test_general = _test_general_163
