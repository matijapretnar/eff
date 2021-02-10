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
    | Num _b_8 -> Value _b_8
    | Add (_l_9, _r_10) ->
        _interp_6 _l_9 >> fun _x_11 ->
        _interp_6 _r_10 >> fun _y_12 -> Value (_op_0 (* + *) _x_11 _y_12)
    | Mul (_l_14, _r_15) ->
        _interp_6 _l_14 >> fun _x_16 ->
        _interp_6 _r_15 >> fun _y_17 -> Value (_op_1 (* * *) _x_16 _y_17)
    | Sub (_l_19, _r_20) ->
        _interp_6 _l_19 >> fun _x_21 ->
        _interp_6 _r_20 >> fun _y_22 -> Value (_op_2 (* - *) _x_21 _y_22)
    | Div (_l_24, _r_25) -> (
        _interp_6 _r_25 >> fun _y_26 ->
        _interp_6 _l_24 >> fun _x_27 ->
        match _y_26 with
        | 0 -> Call (DivByZero, (), fun (_y_42 : int) -> Value _y_42)
        | _ -> Value (_op_4 (* / *) _x_27 _y_26))
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
