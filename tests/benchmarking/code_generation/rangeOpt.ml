open OcamlHeader

type (_, _) effect += Fetch : (unit, int) effect

let _op_0 (* - *) = ( - )

type int_list = Nil | Cons of (int * int_list)

let _test_1 (_n_2 : int) =
  let rec _range_3 _x_15 =
    match _x_15 with
    | 0 -> Value Nil
    | _ ->
        Call
          ( Fetch,
            (),
            fun (_x_0 : int) ->
              _range_3 (_op_0 (* - *) _x_15 1) >> fun _b_6 ->
              Value (Cons (_x_0, _b_6)) )
  in
  let rec _range_18 (_x_15, _k_20) =
    match _x_15 with
    | 0 -> _k_20 Nil
    | _ ->
        _range_18
          ( _op_0 (* - *) _x_15 1,
            fun (_b_37 : int_list) -> _k_20 (Cons (42, _b_37)) )
  in
  _range_18 (_n_2, fun (_x_10 : int_list) -> _x_10)
