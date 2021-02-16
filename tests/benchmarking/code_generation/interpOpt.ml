open OcamlHeader

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) eff_internal_effect += DivByZero : (unit, int) eff_internal_effect

let _addCase_41 =
  Add
    ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
      Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )

let addCase = _addCase_41

let rec _createZeroCase_42 _x_51 =
  match _x_51 with
  | 0 -> Sub (_addCase_41, _addCase_41)
  | _n_53 -> Sub (_createZeroCase_42 (_n_53 - 1), _createZeroCase_42 (_n_53 - 1))

let createZeroCase = _createZeroCase_42

let rec _createCase_60 _x_66 =
  match _x_66 with
  | 1 -> Div (Num 100, _createZeroCase_42 3)
  | _ -> Add (_addCase_41, _createCase_60 (_x_66 - 1))

let createCase = _createCase_60

let _bigTest_72 (_num_73 : int) =
  let rec _interp_74 _x_104 =
    match _x_104 with
    | Num _b_110 -> Value _b_110
    | Add (_l_112, _r_111) ->
        _interp_74 _l_112 >> fun _x_113 ->
        _interp_74 _r_111 >> fun _y_114 -> Value (_x_113 + _y_114)
    | Mul (_l_117, _r_116) ->
        _interp_74 _l_117 >> fun _x_118 ->
        _interp_74 _r_116 >> fun _y_119 -> Value (_x_118 * _y_119)
    | Sub (_l_122, _r_121) ->
        _interp_74 _l_122 >> fun _x_123 ->
        _interp_74 _r_121 >> fun _y_124 -> Value (_x_123 - _y_124)
    | Div (_l_127, _r_126) -> (
        _interp_74 _r_126 >> fun _y_128 ->
        _interp_74 _l_127 >> fun _x_129 ->
        match _y_128 with
        | 0 -> Call (DivByZero, (), fun (_y_130 : int) -> Value _y_130)
        | _ -> Value (_x_129 / _y_128))
  in
  let rec _interp_132 (_x_104, _k_134) =
    match _x_104 with
    | Num _b_110 -> _k_134 _b_110
    | Add (_l_112, _r_111) ->
        _interp_132
          ( _l_112,
            fun (_x_113 : int) ->
              _interp_132
                (_r_111, fun (_y_114 : int) -> _k_134 (_x_113 + _y_114)) )
    | Mul (_l_117, _r_116) ->
        _interp_132
          ( _l_117,
            fun (_x_118 : int) ->
              _interp_132
                (_r_116, fun (_y_119 : int) -> _k_134 (_x_118 * _y_119)) )
    | Sub (_l_122, _r_121) ->
        _interp_132
          ( _l_122,
            fun (_x_123 : int) ->
              _interp_132
                (_r_121, fun (_y_124 : int) -> _k_134 (_x_123 - _y_124)) )
    | Div (_l_127, _r_126) ->
        _interp_132
          ( _r_126,
            fun (_y_128 : int) ->
              _interp_132
                ( _l_127,
                  fun (_x_129 : int) ->
                    match _y_128 with 0 -> ~-1 | _ -> _k_134 (_x_129 / _y_128)
                ) )
  in
  _interp_132 (_createCase_60 _num_73, fun (_id_100 : int) -> _id_100)

let bigTest = _bigTest_72
