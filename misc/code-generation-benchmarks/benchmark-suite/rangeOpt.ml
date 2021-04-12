open OcamlHeader

type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect

type int_list = Nil | Cons of (int * int_list)

let _test_42 (_n_43 : int) =
  let rec _range_73 (_x_56, _k_75) =
    match _x_56 with
    | 0 -> _k_75 Nil
    | _ ->
        _range_73 (_x_56 - 1, fun (_b_82 : int_list) -> _k_75 (Cons (42, _b_82)))
  in
  _range_73 (_n_43, fun (_x_51 : int_list) -> _x_51)

let test = _test_42

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_83 (_m_84 : int) =
  (let rec _sum_226 _x_227 (_x_0 : int) =
     if _x_227 = 0 then _x_0 else _sum_226 (_x_227 - 1) (_x_0 + (_x_227 mod 42))
   in
   _sum_226 _m_84)
    _m_84

let testGenerator = _testGenerator_83
