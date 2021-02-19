open OcamlHeader

type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect

type int_list = Nil | Cons of (int * int_list)

let _test_45 (_n_46 : int) =
  let rec _range_47 _x_59 =
    match _x_59 with
    | 0 -> Value Nil
    | _ ->
        Call
          ( Fetch,
            (),
            fun (_y_69 : int) ->
              _range_47 (_x_59 - 1) >> fun _b_72 -> Value (Cons (_y_69, _b_72))
          )
  in
  let rec _range_73 (_x_59, _k_75) =
    match _x_59 with
    | 0 -> _k_75 Nil
    | _ ->
        _range_73 (_x_59 - 1, fun (_b_82 : int_list) -> _k_75 (Cons (42, _b_82)))
  in
  _range_73 (_n_46, fun (_x_54 : int_list) -> _x_54)

let test = _test_45
