open OcamlHeader

let _op_0 (* + *) = ( + )

let _op_1 (* * *) = ( * )

let _op_2 (* - *) = ( - )

let _op_3 (* ~- *) = ( ~- )

let _op_4 (* / *) = ( / )

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) effect += DivByZero : (unit, int) effect

let _bigTest_5 (() : unit) =
  let rec _interp_6 _x_43 =
    match _x_43 with
    | Num _b_55 -> Value _b_55
    | Add (_l_57, _r_56) ->
        _interp_6 _l_57 >> fun _x_58 ->
        _interp_6 _r_56 >> fun _y_59 -> Value (_op_0 (* + *) _x_58 _y_59)
    | Mul (_l_62, _r_61) ->
        _interp_6 _l_62 >> fun _x_63 ->
        _interp_6 _r_61 >> fun _y_64 -> Value (_op_1 (* * *) _x_63 _y_64)
    | Sub (_l_67, _r_66) ->
        _interp_6 _l_67 >> fun _x_68 ->
        _interp_6 _r_66 >> fun _y_69 -> Value (_op_2 (* - *) _x_68 _y_69)
    | Div (_l_72, _r_71) -> (
        _interp_6 _r_71 >> fun _y_73 ->
        _interp_6 _l_72 >> fun _x_74 ->
        match _y_73 with
        | 0 -> Call (DivByZero, (), fun (_y_75 : int) -> Value _y_75)
        | _ -> Value (_op_4 (* / *) _x_74 _y_73))
  in
  let _addCase_29 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec _createCase_30 _x_44 =
    match _x_44 with
    | 1 -> Div (Num 100, Num 0)
    | _ -> Add (_addCase_29, _createCase_30 (_op_2 (* - *) _x_44 1))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_38 : int) -> Value _id_38);
          effect_clauses =
            (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
              match eff with
              | DivByZero -> fun () _l_45 -> Value (_op_3 (* ~- *) 1)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_interp_6 (_createCase_30 200)))

let bigTest = _bigTest_5
