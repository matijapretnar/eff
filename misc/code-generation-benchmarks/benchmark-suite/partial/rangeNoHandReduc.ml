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
  let rec _range_70 _x_56 =
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
         (match _x_56 with
         | 0 -> Value Nil
         | _ ->
             Call
               ( Fetch,
                 (),
                 fun (_y_66 : int) ->
                   _range_44 (_x_56 - 1) >>= fun _b_69 ->
                   Value (Cons (_y_66, _b_69)) )))
  in
  _range_70 _n_43

let test = _test_42

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_71 (_m_72 : int) =
  let rec _sum_147 _x_148 =
    if _x_148 = 0 then
      Call (GeneratorGet, (), fun (_y_151 : int) -> Value _y_151)
    else
      Call
        ( GeneratorGet,
          (),
          fun (_y_152 : int) ->
            Call
              ( GeneratorProduce,
                _x_148,
                fun (_y_154 : int) ->
                  Call
                    ( GeneratorPut,
                      _y_152 + _y_154,
                      fun (_y_156 : unit) -> _sum_147 (_x_148 - 1) ) ) )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x_177 : int) -> Value (fun (_ : int) -> _x_177));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | GeneratorGet ->
                  fun () _l_178 ->
                    Value
                      (fun (_s_179 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_178 _s_179
                          _s_179)
              | GeneratorPut ->
                  fun _s_181 _l_182 ->
                    Value
                      (fun (_ : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_182 () _s_181)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (let rec _sum_160 _x_161 =
          (handler
             {
               value_clause = (fun (_id_172 : int) -> Value _id_172);
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | GeneratorProduce ->
                       fun _i_173 _l_174 -> _l_174 (_i_173 mod 42)
                   | eff' -> fun arg k -> Call (eff', arg, k));
             })
            (if _x_161 = 0 then
             Call (GeneratorGet, (), fun (_y_164 : int) -> Value _y_164)
            else
              Call
                ( GeneratorGet,
                  (),
                  fun (_y_165 : int) ->
                    Call
                      ( GeneratorProduce,
                        _x_161,
                        fun (_y_167 : int) ->
                          Call
                            ( GeneratorPut,
                              _y_165 + _y_167,
                              fun (_y_169 : unit) -> _sum_147 (_x_161 - 1) ) )
                ))
        in
        _sum_160 _m_72))
    _m_72

let testGenerator = _testGenerator_71
