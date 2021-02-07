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

let bigTest_5 (() : unit) =
  let rec interp_6 _x_7 =
    match _x_7 with
    | Num b_8 -> Value b_8
    | Add (l_9, r_10) ->
        interp_6 l_9 >> fun x_11 ->
        interp_6 r_10 >> fun y_12 -> Value ((_op_0 (* + *) x_11) y_12)
    | Mul (l_14, r_15) ->
        interp_6 l_14 >> fun x_16 ->
        interp_6 r_15 >> fun y_17 -> Value ((_op_1 (* * *) x_16) y_17)
    | Sub (l_19, r_20) ->
        interp_6 l_19 >> fun x_21 ->
        interp_6 r_20 >> fun y_22 -> Value ((_op_2 (* - *) x_21) y_22)
    | Div (l_24, r_25) -> (
        interp_6 r_25 >> fun y_26 ->
        interp_6 l_24 >> fun x_27 ->
        match y_26 with
        | 0 -> Call (DivByZero, (), fun (y_42 : int) -> Value y_42)
        | _ -> Value ((_op_4 (* / *) x_27) y_26))
  in
  let addCase_29 =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  in
  let rec createCase_30 n_31 =
    match n_31 with
    | 1 -> Div (Num 100, Num 0)
    | _ -> Add (addCase_29, createCase_30 ((_op_2 (* - *) n_31) 1))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_38 : int) -> Value _id_38);
          effect_clauses =
            (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
              match eff with
              | DivByZero -> fun () l_43 -> Value (_op_3 (* ~- *) 1)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (interp_6 (createCase_30 200)))
