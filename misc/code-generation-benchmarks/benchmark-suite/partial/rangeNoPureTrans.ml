open OcamlHeader

type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect

type int_list = Nil | Cons of (int * int_list)

let _test_42 (_n_43 : int) =
  let rec _range_79 (_x_56, _k_81) =
    match _x_56 with
    | 0 -> _k_81 Nil
    | _ ->
        Value (( - ) _x_56) >>= fun _x_99 ->
        Value (_x_99 1) >>= fun _x_100 ->
        _range_79 (_x_100, fun (_b_101 : int_list) -> _k_81 (Cons (42, _b_101)))
  in
  _range_79 (_n_43, fun (_x_51 : int_list) -> Value _x_51)

let test x = force_unsafe (_test_42 x)

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_102 (_m_103 : int) : int computation =
  Value
    (let rec _sum_375 _x_376 : (int -> int computation) computation =
       Value (( = ) _x_376) >>= fun _x_377 ->
       Value (_x_377 0) >>= fun _x_378 ->
       if _x_378 then Value (fun (_s_379 : int) -> Value _s_379)
       else
         Value
           (fun (_s_380 : int) ->
             Value (( + ) _s_380) >>= fun _x_381 ->
             Value (( mod ) _x_376) >>= fun _x_382 ->
             Value (_x_382 42) >>= fun _x_383 ->
             Value (_x_381 _x_383) >>= fun _x_384 ->
             Value (( - ) _x_376) >>= fun _x_385 ->
             Value (_x_385 1) >>= fun _x_386 ->
             Value (_sum_375 _x_386) >>= fun _b_387 ->
             (force_unsafe _b_387) _x_384)
     in
     _sum_375 _m_103)
  >>= fun _b_361 -> (force_unsafe _b_361) _m_103

let testGenerator x = force_unsafe (_testGenerator_102 x)
