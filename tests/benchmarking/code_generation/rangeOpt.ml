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
            fun (_y_65 : int) ->
              _range_43 (_x_55 - 1) >> fun _b_68 -> Value (Cons (_y_65, _b_68))
          )
  in
  let rec _range_69 (_x_55, _k_71) =
    match _x_55 with
    | 0 -> _k_71 Nil
    | _ ->
        _range_69 (_x_55 - 1, fun (_b_78 : int_list) -> _k_71 (Cons (42, _b_78)))
  in
  _range_69 (_n_42, fun (_x_50 : int_list) -> _x_50)

let test = _test_41
