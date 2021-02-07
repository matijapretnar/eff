open OcamlHeader

type (_, _) effect += Fetch : (unit, int) effect

let _op_0 (* - *) = ( - )

type int_list = Nil | Cons of (int * int_list)

let test_1 (n_2 : int) =
  let rec range_3 n_4 =
    match n_4 with
    | 0 -> Value Nil
    | _ ->
        Call (Fetch, (), fun (y_14 : int) -> Value y_14) >> fun _b_5 ->
        range_3 ((_op_0 (* - *) n_4) 1) >> fun _b_6 -> Value (Cons (_b_5, _b_6))
  in
  let rec range_16 (n_4, k_18) =
    match n_4 with
    | 0 -> k_18 Nil
    | _ ->
        range_16
          ( (_op_0 (* - *) n_4) 1,
            fun (_b_6 : int_list) -> k_18 (Cons (42, _b_6)) )
  in
  range_16 (n_2, fun (_x_10 : int_list) -> _x_10)
