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
  (let rec _loop_incr_114 _x_89 =
     if _x_89 = 0 then fun (_x_108 : int) -> _x_108
     else fun (_x_116 : int) -> _loop_incr_114 (_x_89 - 1) (_x_116 + 1)
   in
   _loop_incr_114 _n_99)
    0

let test_incr = _test_incr_98

let rec _loop_incr'_120 _x_128 =
  if _x_128 = 0 then Value ()
  else
    _loop_incr'_120 (_x_128 - 1) >> fun _ ->
    Call (Incr, (), fun (_y_136 : unit) -> Value _y_136)

let loop_incr' = _loop_incr'_120

let _test_incr'_137 (_n_138 : int) =
  (let rec _loop_incr'_163 (_x_128, _k_166) =
     if _x_128 = 0 then _k_166 ()
     else
       _loop_incr'_163
         (_x_128 - 1, fun (_ : unit) (_x_170 : int) -> _k_166 () (_x_170 + 1))
   and _loop_incr_164 _x_89 =
     if _x_89 = 0 then fun (_x_147 : int) -> _x_147
     else fun (_x_176 : int) -> _loop_incr_164 (_x_89 - 1) (_x_176 + 1)
   in
   _loop_incr'_163 (_n_138, fun (_x_145 : unit) (_x_147 : int) -> _x_147))
    0

let test_incr' = _test_incr'_137

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_180 _x_193 =
  if _x_193 = 0 then Value ()
  else
    Call
      ( Get,
        (),
        fun (_y_202 : int) ->
          Call
            ( Put,
              _y_202 + 1,
              fun (_y_205 : unit) -> _loop_state_180 (_x_193 - 1) ) )

let loop_state = _loop_state_180

let _test_state_208 (_n_209 : int) =
  (let rec _loop_state_226 _x_193 =
     if _x_193 = 0 then fun (_x_219 : int) -> _x_219
     else fun (_s_234 : int) -> _loop_state_226 (_x_193 - 1) (_s_234 + 1)
   in
   _loop_state_226 _n_209)
    0

let test_state = _test_state_208
