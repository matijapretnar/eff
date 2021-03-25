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
  let rec _range_76 (_x_59, _k_78) =
    match _x_59 with
    | 0 -> _k_78 Nil
    | _ ->
        _range_76 (_x_59 - 1, fun (_b_85 : int_list) -> _k_78 (Cons (42, _b_85)))
  in
  _range_76 (_n_46, fun (_x_54 : int_list) -> _x_54)

let test = _test_45
