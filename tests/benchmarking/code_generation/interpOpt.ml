open OcamlHeader

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) eff_internal_effect += DivByZero : (unit, int) eff_internal_effect

let _addCase_42 =
  Add
    ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
      Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )

let addCase = _addCase_42

let rec _createZeroCase_43 _x_52 =
  match _x_52 with
  | 0 -> Sub (_addCase_42, _addCase_42)
  | _n_54 -> Sub (_createZeroCase_43 (_n_54 - 1), _createZeroCase_43 (_n_54 - 1))

let createZeroCase = _createZeroCase_43

let rec _createCase_61 _x_67 =
  match _x_67 with
  | 1 -> Div (Num 100, _createZeroCase_43 3)
  | _ -> Add (_addCase_42, _createCase_61 (_x_67 - 1))

let createCase = _createCase_61

let _bigTest_73 (_num_74 : int) =
  let rec _interp_75 _x_105 =
    match _x_105 with
    | Num _b_111 -> Value _b_111
    | Add (_l_113, _r_112) ->
        _interp_75 _l_113 >> fun _x_114 ->
        _interp_75 _r_112 >> fun _y_115 -> Value (_x_114 + _y_115)
    | Mul (_l_118, _r_117) ->
        _interp_75 _l_118 >> fun _x_119 ->
        _interp_75 _r_117 >> fun _y_120 -> Value (_x_119 * _y_120)
    | Sub (_l_123, _r_122) ->
        _interp_75 _l_123 >> fun _x_124 ->
        _interp_75 _r_122 >> fun _y_125 -> Value (_x_124 - _y_125)
    | Div (_l_128, _r_127) -> (
        _interp_75 _r_127 >> fun _y_129 ->
        _interp_75 _l_128 >> fun _x_130 ->
        match _y_129 with
        | 0 -> Call (DivByZero, (), fun (_y_131 : int) -> Value _y_131)
        | _ -> Value (_x_130 / _y_129))
  in
  let rec _interp_135 (_x_105, _k_137) =
    match _x_105 with
    | Num _b_111 -> _k_137 _b_111
    | Add (_l_113, _r_112) ->
        _interp_135
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_135
                (_r_112, fun (_y_115 : int) -> _k_137 (_x_114 + _y_115)) )
    | Mul (_l_118, _r_117) ->
        _interp_135
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_135
                (_r_117, fun (_y_120 : int) -> _k_137 (_x_119 * _y_120)) )
    | Sub (_l_123, _r_122) ->
        _interp_135
          ( _l_123,
            fun (_x_124 : int) ->
              _interp_135
                (_r_122, fun (_y_125 : int) -> _k_137 (_x_124 - _y_125)) )
    | Div (_l_128, _r_127) ->
        _interp_135
          ( _r_127,
            fun (_y_129 : int) ->
              _interp_135
                ( _l_128,
                  fun (_x_130 : int) ->
                    match _y_129 with 0 -> ~-1 | _ -> _k_137 (_x_130 / _y_129)
                ) )
  in
  _interp_135 (_createCase_61 _num_74, fun (_id_101 : int) -> _id_101)

let bigTest = _bigTest_73
