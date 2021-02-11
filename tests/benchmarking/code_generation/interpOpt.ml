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
    | Num _b_91 -> Value _b_91
    | Add (_l_93, _r_92) ->
        _interp_42 _l_93 >> fun _x_94 ->
        _interp_42 _r_92 >> fun _y_95 -> Value (_x_94 + _y_95)
    | Mul (_l_98, _r_97) ->
        _interp_42 _l_98 >> fun _x_99 ->
        _interp_42 _r_97 >> fun _y_100 -> Value (_x_99 * _y_100)
    | Sub (_l_103, _r_102) ->
        _interp_42 _l_103 >> fun _x_104 ->
        _interp_42 _r_102 >> fun _y_105 -> Value (_x_104 - _y_105)
    | Div (_l_108, _r_107) -> (
        _interp_42 _r_107 >> fun _y_109 ->
        _interp_42 _l_108 >> fun _x_110 ->
        match _y_109 with
        | 0 -> Call (DivByZero, (), fun (_y_111 : int) -> Value _y_111)
        | _ -> Value (_x_110 / _y_109))
  in
  let _addCase_65 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createCase_66 _x_80 =
    match _x_80 with
    | 1 -> Div (Num 100, Num 0)
    | _ -> Add (_addCase_65, _createCase_66 (_x_80 - 1))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_74 : int) -> Value _id_74);
          effect_clauses =
            (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
              match eff with
              | DivByZero -> fun () _l_81 -> Value ~-1
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_interp_42 (_createCase_66 200)))

let bigTest = _bigTest_41
