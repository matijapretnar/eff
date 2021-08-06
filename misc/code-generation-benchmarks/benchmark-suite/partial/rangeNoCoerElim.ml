open OcamlHeader

type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect

type int_list = Nil | Cons of (int * int_list)

let _test_42 (_n_43 : int) =
  let rec _range_74 (_x_56, _k_76) =
    match _x_56 with
    | 0 -> _k_76 Nil
    | _ ->
        _range_74
          ( _x_56 - 1,
            fun (_b_96 : int_list) ->
              _k_76
                (Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (42, _b_96)))
          )
  in
  _range_74 (_n_43, fun (_x_51 : int_list) -> _x_51)

let test = _test_42

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_97 (_m_98 : int) =
  let rec _sum_250 _x_136 =
    if _x_136 = 0 then fun (_s_323 : int) -> _s_323
    else fun (_s_324 : int) -> _sum_250 (_x_136 - 1) (_s_324 + (_x_136 mod 42))
  in
  _sum_250 _m_98 _m_98

let testGenerator = _testGenerator_97
