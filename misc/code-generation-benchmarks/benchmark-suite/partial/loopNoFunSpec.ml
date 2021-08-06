open OcamlHeader

let rec _loop_pure_42 _x_48 = if _x_48 = 0 then () else _loop_pure_42 (_x_48 - 1)

let loop_pure = _loop_pure_42

let _test_pure_54 (_n_55 : int) = _loop_pure_42 _n_55

let test_pure = _test_pure_54

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

let rec _loop_latent_56 _x_67 =
  if _x_67 = 0 then Value ()
  else if _x_67 < 0 then
    Call
      ( Fail,
        (),
        fun (_y_76 : empty) -> Value (match _y_76 with _ -> assert false) )
  else _loop_latent_56 (_x_67 - 1)

let loop_latent = _loop_latent_56

let _test_latent_79 (_n_80 : int) = _loop_latent_56 _n_80

let test_latent = _test_latent_79

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let rec _loop_incr_81 _x_89 =
  if _x_89 = 0 then Value ()
  else Call (Incr, (), fun (_y_95 : unit) -> _loop_incr_81 (_x_89 - 1))

let loop_incr = _loop_incr_81

let _test_incr_98 (_n_99 : int) =
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_106 : unit) -> Value (fun (_x_108 : int) -> _x_108));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Incr ->
                  fun () _l_111 ->
                    Value
                      (fun (_x_102 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_111 ()
                          (_x_102 + 1))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_loop_incr_81 _n_99))
    0

let test_incr = _test_incr_98

let rec _loop_incr'_339 _x_347 =
  if _x_347 = 0 then Value ()
  else
    _loop_incr'_339 (_x_347 - 1) >>= fun _ ->
    Call (Incr, (), fun (_y_355 : unit) -> Value _y_355)

let loop_incr' = _loop_incr'_339

let _test_incr'_356 (_n_357 : int) =
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_364 : unit) -> Value (fun (_x_366 : int) -> _x_366));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Incr ->
                  fun () _l_369 ->
                    Value
                      (fun (_x_360 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_369 ()
                          (_x_360 + 1))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_loop_incr'_339 _n_357))
    0

let test_incr' = _test_incr'_356

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_1198 _x_1211 =
  if _x_1211 = 0 then Value ()
  else
    Call
      ( Get,
        (),
        fun (_y_1220 : int) ->
          Call
            ( Put,
              _y_1220 + 1,
              fun (_y_1223 : unit) -> _loop_state_1198 (_x_1211 - 1) ) )

let loop_state = _loop_state_1198

let _test_state_1226 (_n_1227 : int) =
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_1235 : unit) -> Value (fun (_x_1237 : int) -> _x_1237));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Get ->
                  fun () _l_1240 ->
                    Value
                      (fun (_s_1230 : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_1240 _s_1230
                          _s_1230)
              | Put ->
                  fun _s'_1232 _l_1241 ->
                    Value
                      (fun (_ : int) ->
                        coer_arrow coer_refl_ty force_unsafe _l_1241 () _s'_1232)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_loop_state_1198 _n_1227))
    0

let test_state = _test_state_1226
