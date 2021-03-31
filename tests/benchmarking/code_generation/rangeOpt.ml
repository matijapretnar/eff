open OcamlHeader

type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect

type int_list = Nil | Cons of (int * int_list)

let _test_42 (_n_43 : int) =
  let rec _range_44 _x_56 =
    match _x_56 with
    | 0 -> Value Nil
    | _ ->
        Call
          ( Fetch,
            (),
            fun (_y_66 : int) ->
              _range_44 (_x_56 - 1) >> fun _b_69 -> Value (Cons (_y_66, _b_69))
          )
  in
  let rec _range_73 (_x_56, _k_75) =
    match _x_56 with
    | 0 -> _k_75 Nil
    | _ ->
        _range_73 (_x_56 - 1, fun (_b_82 : int_list) -> _k_75 (Cons (42, _b_82)))
  in
  _range_73 (_n_43, fun (_x_51 : int_list) -> _x_51)

let test = _test_42
