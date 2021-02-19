open OcamlHeader

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) eff_internal_effect += DivByZero : (unit, int) eff_internal_effect

let _addCase_45 =
  Add
    ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
      Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )

let addCase = _addCase_45

let rec _createZeroCase_46 _x_55 =
  match _x_55 with
  | 0 -> Sub (_addCase_45, _addCase_45)
  | _n_57 -> Sub (_createZeroCase_46 (_n_57 - 1), _createZeroCase_46 (_n_57 - 1))

let createZeroCase = _createZeroCase_46

let rec _createCase_64 _x_70 =
  match _x_70 with
  | 1 -> Div (Num 100, _createZeroCase_46 3)
  | _ -> Add (_addCase_45, _createCase_64 (_x_70 - 1))

let createCase = _createCase_64

let _bigTest_76 (_num_77 : int) =
  let rec _interp_78 _x_108 =
    match _x_108 with
    | Num _b_114 -> Value _b_114
    | Add (_l_116, _r_115) ->
        _interp_78 _l_116 >> fun _x_117 ->
        _interp_78 _r_115 >> fun _y_118 -> Value (_x_117 + _y_118)
    | Mul (_l_121, _r_120) ->
        _interp_78 _l_121 >> fun _x_122 ->
        _interp_78 _r_120 >> fun _y_123 -> Value (_x_122 * _y_123)
    | Sub (_l_126, _r_125) ->
        _interp_78 _l_126 >> fun _x_127 ->
        _interp_78 _r_125 >> fun _y_128 -> Value (_x_127 - _y_128)
    | Div (_l_131, _r_130) -> (
        _interp_78 _r_130 >> fun _y_132 ->
        _interp_78 _l_131 >> fun _x_133 ->
        match _y_132 with
        | 0 -> Call (DivByZero, (), fun (_y_134 : int) -> Value _y_134)
        | _ -> Value (_x_133 / _y_132))
  in
  let rec _interp_136 (_x_108, _k_138) =
    match _x_108 with
    | Num _b_114 -> _k_138 _b_114
    | Add (_l_116, _r_115) ->
        _interp_136
          ( _l_116,
            fun (_x_117 : int) ->
              _interp_136
                (_r_115, fun (_y_118 : int) -> _k_138 (_x_117 + _y_118)) )
    | Mul (_l_121, _r_120) ->
        _interp_136
          ( _l_121,
            fun (_x_122 : int) ->
              _interp_136
                (_r_120, fun (_y_123 : int) -> _k_138 (_x_122 * _y_123)) )
    | Sub (_l_126, _r_125) ->
        _interp_136
          ( _l_126,
            fun (_x_127 : int) ->
              _interp_136
                (_r_125, fun (_y_128 : int) -> _k_138 (_x_127 - _y_128)) )
    | Div (_l_131, _r_130) ->
        _interp_136
          ( _r_130,
            fun (_y_132 : int) ->
              _interp_136
                ( _l_131,
                  fun (_x_133 : int) ->
                    match _y_132 with 0 -> ~-1 | _ -> _k_138 (_x_133 / _y_132)
                ) )
  in
  _interp_136 (_createCase_64 _num_77, fun (_id_104 : int) -> _id_104)

let bigTest = _bigTest_76
