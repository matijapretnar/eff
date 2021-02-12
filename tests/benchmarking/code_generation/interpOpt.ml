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
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_100 : int) -> Value _id_100);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | DivByZero -> fun () _l_105 -> Value ~-1
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_interp_74 (_createCase_60 _num_73)))

let bigTest = _bigTest_72
