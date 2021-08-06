open OcamlHeader

type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect

type int_list = Nil | Cons of (int * int_list)

let _test_42 (_n_43 : int) =
  let rec _range_98 (_x_56, _k_100) =
    match _x_56 with
    | 0 -> _k_100 Nil
    | _ ->
        _range_98
          ( coer_arrow coer_refl_ty coer_refl_ty (( - ) _x_56) 1,
            fun (_x_176 : int_list) ->
              _k_100
                (Cons (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (42, _x_176)))
          )
  in
  _range_98 (_n_43, fun (_x_62 : int_list) -> _x_62)

let test = _test_42

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_177 (_m_178 : int) =
  coer_arrow coer_refl_ty coer_refl_ty
    (coer_arrow coer_refl_ty coer_refl_ty
       (let rec _sum_577 ((_x_216, _k_285), _k_579) =
          if coer_arrow coer_refl_ty coer_refl_ty (( = ) _x_216) 0 then
            coer_arrow coer_refl_ty coer_refl_ty (fun (_s_1537 : int) ->
                coer_arrow coer_refl_ty coer_refl_ty
                  (coer_arrow coer_refl_ty coer_refl_ty
                     (force_unsafe
                        ((handler
                            {
                              value_clause =
                                (fun (_x_1685 : int) -> Value (_k_579 _x_1685));
                              effect_clauses =
                                (fun (type a b)
                                     (eff : (a, b) eff_internal_effect) :
                                     (a -> (b -> _) -> _) ->
                                  match eff with
                                  | GeneratorGet ->
                                      fun () _l_1686 ->
                                        Value
                                          (coer_arrow coer_refl_ty coer_refl_ty
                                             (fun (_s_1687 : int) ->
                                               coer_arrow coer_refl_ty
                                                 coer_refl_ty
                                                 (coer_arrow coer_refl_ty
                                                    coer_refl_ty
                                                    (coer_arrow coer_refl_ty
                                                       force_unsafe _l_1686
                                                       _s_1687))
                                                 _s_1687))
                                  | GeneratorPut ->
                                      fun _s_1689 _l_1690 ->
                                        Value
                                          (coer_arrow coer_refl_ty coer_refl_ty
                                             (fun (_ : int) ->
                                               coer_arrow coer_refl_ty
                                                 coer_refl_ty
                                                 (coer_arrow coer_refl_ty
                                                    coer_refl_ty
                                                    (coer_arrow coer_refl_ty
                                                       force_unsafe _l_1690 ()))
                                                 _s_1689))
                                  | eff' -> fun arg k -> Call (eff', arg, k));
                            })
                           (_k_285 _s_1537))))
                  _s_1537)
          else
            coer_arrow coer_refl_ty coer_refl_ty (fun (_s_1692 : int) ->
                coer_arrow coer_refl_ty coer_refl_ty
                  (coer_arrow coer_refl_ty coer_refl_ty
                     (coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) ->
                          coer_arrow coer_refl_ty coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty
                               (_sum_577
                                  ( ( coer_arrow coer_refl_ty coer_refl_ty
                                        (( - ) _x_216) 1,
                                      fun (_x_1700 : int) -> _k_285 _x_1700 ),
                                    fun (_x_1701 : int) -> _k_579 _x_1701 )))
                            (coer_arrow coer_refl_ty coer_refl_ty
                               (( + ) _s_1692)
                               (coer_arrow coer_refl_ty coer_refl_ty
                                  (( mod ) _x_216) 42)))))
                  _s_1692)
        in
        _sum_577
          ( (_m_178, fun (_x_230 : int) -> coer_return coer_refl_ty _x_230),
            fun (_x_251 : int) ->
              coer_arrow coer_refl_ty coer_refl_ty (fun (_ : int) -> _x_251) )))
    _m_178

let testGenerator = _testGenerator_177
