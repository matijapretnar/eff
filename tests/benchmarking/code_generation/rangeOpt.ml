open OcamlHeader

type (_, _) effect += Fetch : (unit, int) effect

type int_list = Nil | Cons of (int * int_list)

let _test_41 (_n_42 : int) =
  let rec _range_43 _x_55 =
    match _x_55 with
    | 0 -> Value Nil
    | _ ->
        Call
          ( Fetch,
            (),
            fun (_y_61 : int) ->
              _range_43 (_x_55 - 1) >> fun _b_69 -> Value (Cons (_y_61, _b_69))
          )
  in
  let rec _range_70 (_x_55, _k_72) =
    match _x_55 with
    | 0 -> _k_72 Nil
    | _ ->
        _range_70 (_x_55 - 1, fun (_b_79 : int_list) -> _k_72 (Cons (42, _b_79)))
  in
  _range_70 (_n_42, fun (_x_50 : int_list) -> _x_50)

let test = _test_41
