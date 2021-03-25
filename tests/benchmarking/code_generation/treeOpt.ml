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
