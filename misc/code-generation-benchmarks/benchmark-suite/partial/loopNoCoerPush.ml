open OcamlHeader

let rec _loop_pure_42 _x_48 = if _x_48 = 0 then () else _loop_pure_42 (_x_48 - 1)

let loop_pure = _loop_pure_42

let _test_pure_54 (_n_55 : int) = _loop_pure_42 _n_55

let test_pure = _test_pure_54

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

let rec _loop_latent_56 _x_67 =
  if _x_67 = 0 then Value ()
  else if _x_67 < 0 then
    Call (Fail, (), fun (_y_74 : empty) -> Value _y_74) >>= fun _b_73 ->
    Value (match _b_73 with _ -> assert false)
  else _loop_latent_56 (_x_67 - 1)

let loop_latent = _loop_latent_56

let _test_latent_79 (_n_80 : int) = _loop_latent_56 _n_80

let test_latent = _test_latent_79

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let rec _loop_incr_81 _x_89 =
  if _x_89 = 0 then Value ()
  else
    Call (Incr, (), fun (_y_96 : unit) -> Value _y_96) >>= fun _ ->
    _loop_incr_81 (_x_89 - 1)

let loop_incr = _loop_incr_81

let _test_incr_98 (_n_99 : int) =
  let rec _loop_incr_114 _x_89 (_x_0 : int) =
    if _x_89 = 0 then _x_0 else _loop_incr_114 (_x_89 - 1) (_x_0 + 1)
  in
  _loop_incr_114 _n_99 0

let test_incr = _test_incr_98

let rec _loop_incr'_140 _x_148 =
  if _x_148 = 0 then Value ()
  else
    _loop_incr'_140 (_x_148 - 1) >>= fun _ ->
    Call (Incr, (), fun (_y_153 : unit) -> Value _y_153)

let loop_incr' = _loop_incr'_140

let _test_incr'_157 (_n_158 : int) =
  let rec _loop_incr'_188 (_x_148, _k_191) =
    if _x_148 = 0 then _k_191 ()
    else
      _loop_incr'_188
        (_x_148 - 1, fun (_ : unit) (_x_233 : int) -> _k_191 () (_x_233 + 1))
  and _loop_incr_189 _x_89 (_x_1 : int) =
    if _x_89 = 0 then _x_1 else _loop_incr_189 (_x_89 - 1) (_x_1 + 1)
  in
  _loop_incr'_188 (_n_158, fun (_x_165 : unit) (_x_167 : int) -> _x_167) 0

let test_incr' = _test_incr'_157

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_245 _x_258 =
  if _x_258 = 0 then Value ()
  else
    ( ( ( Call (Get, (), fun (_y_271 : int) -> Value _y_271) >>= fun _b_270 ->
          Value (( + ) _b_270) )
      >>= fun _b_269 -> Value (_b_269 1) )
    >>= fun _b_267 -> Call (Put, _b_267, fun (_y_268 : unit) -> Value _y_268) )
    >>= fun _ -> _loop_state_245 (_x_258 - 1)

let loop_state = _loop_state_245

let _test_state_273 (_n_274 : int) =
  let rec _loop_state_291 _x_258 (_x_2 : int) =
    if _x_258 = 0 then _x_2 else _loop_state_291 (_x_258 - 1) (_x_2 + 1)
  in
  _loop_state_291 _n_274 0

let test_state = _test_state_273
