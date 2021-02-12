open OcamlHeader

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) effect += DivByZero : (unit, int) effect

let _bigTest_41 (() : unit) =
  let rec _interp_42 _x_79 =
    match _x_79 with
    | Num _b_101 -> Value _b_101
    | Add (_l_103, _r_102) ->
        _interp_42 _l_103 >> fun _x_104 ->
        _interp_42 _r_102 >> fun _y_105 -> Value (_x_104 + _y_105)
    | Mul (_l_108, _r_107) ->
        _interp_42 _l_108 >> fun _x_109 ->
        _interp_42 _r_107 >> fun _y_110 -> Value (_x_109 * _y_110)
    | Sub (_l_113, _r_112) ->
        _interp_42 _l_113 >> fun _x_114 ->
        _interp_42 _r_112 >> fun _y_115 -> Value (_x_114 - _y_115)
    | Div (_l_118, _r_117) -> (
        _interp_42 _r_117 >> fun _y_119 ->
        _interp_42 _l_118 >> fun _x_120 ->
        match _y_119 with
        | 0 -> Call (DivByZero, (), fun (_y_121 : int) -> Value _y_121)
        | _ -> Value (_x_120 / _y_119))
  in
  let rec _createCase_89 _x_90 =
    match _x_90 with
    | 1 -> Div (Num 100, Num 0)
    | _ ->
        Add
          ( Add
              ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
                Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) ),
            _createCase_89 (_x_90 - 1) )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_96 : int) -> Value _id_96);
          effect_clauses =
            (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
              match eff with
              | DivByZero -> fun () _l_97 -> Value ~-1
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_interp_42 (_createCase_89 200)))

let bigTest = _bigTest_41
