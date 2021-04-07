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

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_83 (_m_84 : int) =
  let rec _sum_200 _x_201 =
    if _x_201 = 0 then
      Call (GeneratorGet, (), fun (_y_204 : int) -> Value _y_204)
    else
      Call
        ( GeneratorGet,
          (),
          fun (_y_205 : int) ->
            Call
              ( GeneratorProduce,
                _x_201,
                fun (_y_207 : int) ->
                  Call
                    ( GeneratorPut,
                      _y_205 + _y_207,
                      fun (_y_209 : unit) -> _sum_200 (_x_201 - 1) ) ) )
  in
  (let rec _sum_213 _x_214 =
     if _x_214 = 0 then
       Call (GeneratorGet, (), fun (_y_217 : int) -> Value _y_217)
     else
       Call
         ( GeneratorGet,
           (),
           fun (_y_218 : int) ->
             Call
               ( GeneratorPut,
                 _y_218 + (_x_214 mod 42),
                 fun (_y_223 : unit) -> _sum_213 (_x_214 - 1) ) )
   in
   let rec _sum_226 _x_227 (_x_0 : int) =
     if _x_227 = 0 then _x_0 else _sum_226 (_x_227 - 1) (_x_0 + (_x_227 mod 42))
   in
   _sum_226 _m_84)
    _m_84

let testGenerator = _testGenerator_83
