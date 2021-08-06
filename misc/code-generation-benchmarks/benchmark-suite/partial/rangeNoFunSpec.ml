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
              _range_44 (_x_56 - 1) >>= fun _b_69 -> Value (Cons (_y_66, _b_69))
          )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x_51 : int_list) -> Value _x_51);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Fetch ->
                  fun _ _l_57 ->
                    Value (coer_arrow coer_refl_ty force_unsafe _l_57 42)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_range_44 _n_43))

let test = _test_42

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_284 (_m_285 : int) =
  let rec _sum_3891 _x_3892 =
    if _x_3892 = 0 then
      Call (GeneratorGet, (), fun (_y_3895 : int) -> Value _y_3895)
    else
      Call
        ( GeneratorGet,
          (),
          fun (_y_3896 : int) ->
            Call
              ( GeneratorProduce,
                _x_3892,
                fun (_y_3898 : int) ->
                  Call
                    ( GeneratorPut,
                      _y_3896 + _y_3898,
                      fun (_y_3900 : unit) -> _sum_3891 (_x_3892 - 1) ) ) )
  in
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_3909 : int) -> Value (fun (_ : int) -> _x_3909));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | GeneratorGet ->
                  fun () _l_3910 ->
                    Value
                      (fun (_s_3911 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_3910 _s_3911
                          _s_3911)
              | GeneratorPut ->
                  fun _s_3913 _l_3914 ->
                    Value
                      (fun (_ : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_3914 () _s_3913)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       ((handler
           {
             value_clause = (fun (_id_3904 : int) -> Value _id_3904);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | GeneratorProduce ->
                     fun _i_3905 _l_3906 -> _l_3906 (_i_3905 mod 42)
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_sum_3891 _m_285)))
    _m_285

let testGenerator = _testGenerator_284
