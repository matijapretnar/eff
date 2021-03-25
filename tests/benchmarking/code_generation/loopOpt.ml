open OcamlHeader

let rec _loop_pure_45 _x_51 = if _x_51 = 0 then () else _loop_pure_45 (_x_51 - 1)

let loop_pure = _loop_pure_45

let _test_pure_57 (_n_58 : int) = _loop_pure_45 _n_58

let test_pure = _test_pure_57

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

let rec _loop_latent_59 _x_70 =
  if _x_70 = 0 then Value ()
  else if _x_70 < 0 then
    Call
      ( Fail,
        (),
        fun (_y_79 : empty) -> Value (match _y_79 with _ -> assert false) )
  else _loop_latent_59 (_x_70 - 1)

let loop_latent = _loop_latent_59

let _test_latent_82 (_n_83 : int) = _loop_latent_59 _n_83

let test_latent = _test_latent_82

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let rec _loop_incr_84 _x_92 =
  if _x_92 = 0 then Value ()
  else Call (Incr, (), fun (_y_98 : unit) -> _loop_incr_84 (_x_92 - 1))

let loop_incr = _loop_incr_84

let _test_incr_101 (_n_102 : int) =
  (let rec _loop_incr_117 _x_92 =
     if _x_92 = 0 then fun (_x_111 : int) -> _x_111
     else fun (_x_119 : int) -> _loop_incr_117 (_x_92 - 1) (_x_119 + 1)
   in
   _loop_incr_117 _n_102)
    0

let test_incr = _test_incr_101

let rec _loop_incr'_123 _x_131 =
  if _x_131 = 0 then Value ()
  else
    _loop_incr'_123 (_x_131 - 1) >> fun _ ->
    Call (Incr, (), fun (_y_139 : unit) -> Value _y_139)

let loop_incr' = _loop_incr'_123

let _test_incr'_140 (_n_141 : int) =
  (let rec _loop_incr'_167 (_x_131, _k_170) =
     if _x_131 = 0 then _k_170 ()
     else
       _loop_incr'_167
         (_x_131 - 1, fun (_ : unit) (_x_174 : int) -> _k_170 () (_x_174 + 1))
   and _loop_incr_168 _x_92 =
     if _x_92 = 0 then fun (_x_150 : int) -> _x_150
     else fun (_x_180 : int) -> _loop_incr_168 (_x_92 - 1) (_x_180 + 1)
   in
   _loop_incr'_167 (_n_141, fun (_x_148 : unit) (_x_150 : int) -> _x_150))
    0

let test_incr' = _test_incr'_140

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_184 _x_197 =
  if _x_197 = 0 then Value ()
  else
    Call
      ( Get,
        (),
        fun (_y_206 : int) ->
          Call
            ( Put,
              _y_206 + 1,
              fun (_y_209 : unit) -> _loop_state_184 (_x_197 - 1) ) )

let loop_state = _loop_state_184

let _test_state_212 (_n_213 : int) =
  (let rec _loop_state_230 _x_197 =
     if _x_197 = 0 then fun (_x_223 : int) -> _x_223
     else fun (_s_238 : int) -> _loop_state_230 (_x_197 - 1) (_s_238 + 1)
   in
   _loop_state_230 _n_213)
    0

let test_state = _test_state_212
