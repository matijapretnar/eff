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
  let rec _loop_incr_114 _x_89 (_x_0 : int) =
    if _x_89 = 0 then _x_0 else _loop_incr_114 (_x_89 - 1) (_x_0 + 1)
  in
  _loop_incr_114 _n_99 0

let test_incr = _test_incr_98

let rec _loop_incr'_120 _x_128 =
  if _x_128 = 0 then Value ()
  else
    _loop_incr'_120 (_x_128 - 1) >>= fun _ ->
    Call (Incr, (), fun (_y_136 : unit) -> Value _y_136)

let loop_incr' = _loop_incr'_120

let _test_incr'_137 (_n_138 : int) =
  let rec _loop_incr'_164 (_x_128, _k_167) =
    if _x_128 = 0 then _k_167 ()
    else
      _loop_incr'_164
        (_x_128 - 1, fun (_ : unit) (_x_171 : int) -> _k_167 () (_x_171 + 1))
  and _loop_incr_165 _x_89 (_x_1 : int) =
    if _x_89 = 0 then _x_1 else _loop_incr_165 (_x_89 - 1) (_x_1 + 1)
  in
  _loop_incr'_164 (_n_138, fun (_x_145 : unit) (_x_147 : int) -> _x_147) 0

let test_incr' = _test_incr'_137

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_181 _x_194 =
  if _x_194 = 0 then Value ()
  else
    Call
      ( Get,
        (),
        fun (_y_203 : int) ->
          Call
            ( Put,
              _y_203 + 1,
              fun (_y_206 : unit) -> _loop_state_181 (_x_194 - 1) ) )

let loop_state = _loop_state_181

let _test_state_209 (_n_210 : int) =
  let rec _loop_state_227 _x_194 (_x_2 : int) =
    if _x_194 = 0 then _x_2 else _loop_state_227 (_x_194 - 1) (_x_2 + 1)
  in
  _loop_state_227 _n_210 0

let test_state = _test_state_209
