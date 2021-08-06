open OcamlHeader

let rec _loop_pure_42 _x_48 = if _x_48 = 0 then () else _loop_pure_42 (_x_48 - 1)

let loop_pure = _loop_pure_42

let _test_pure_49 (_n_50 : int) = _loop_pure_42 _n_50

let test_pure = _test_pure_49

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

let rec _loop_latent_51 _x_62 =
  coer_return coer_refl_ty (( = ) _x_62) >>= fun _b_54 ->
  coer_return coer_refl_ty (_b_54 0) >>= fun _b_53 ->
  if _b_53 then coer_return coer_refl_ty ()
  else
    coer_return coer_refl_ty (( < ) _x_62) >>= fun _b_56 ->
    coer_return coer_refl_ty (_b_56 0) >>= fun _b_55 ->
    if _b_55 then
      Call
        ( Fail,
          (),
          fun (_y_64 : empty) ->
            coer_return coer_refl_ty (match _y_64 with _ -> assert false) )
    else
      coer_return coer_refl_ty (( - ) _x_62) >>= fun _b_59 ->
      coer_return coer_refl_ty (_b_59 1) >>= fun _b_58 -> _loop_latent_51 _b_58

let loop_latent = _loop_latent_51

let _test_latent_66 (_n_67 : int) = _loop_latent_51 _n_67

let test_latent = _test_latent_66

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let rec _loop_incr_68 _x_76 =
  coer_return coer_refl_ty (( = ) _x_76) >>= fun _b_71 ->
  coer_return coer_refl_ty (_b_71 0) >>= fun _b_70 ->
  if _b_70 then coer_return coer_refl_ty ()
  else
    Call
      ( Incr,
        (),
        fun (_y_78 : unit) ->
          coer_return coer_refl_ty (( - ) _x_76) >>= fun _b_73 ->
          coer_return coer_refl_ty (_b_73 1) >>= fun _b_72 ->
          _loop_incr_68 _b_72 )

let loop_incr = _loop_incr_68

let _test_incr_79 (_n_80 : int) =
  let rec _loop_incr_95 _x_76 =
    if _x_76 = 0 then fun (_x_122 : int) -> _x_122
    else fun (_x_123 : int) -> _loop_incr_95 (_x_76 - 1) (_x_123 + 1)
  in
  _loop_incr_95 _n_80 0

let test_incr = _test_incr_79

let rec _loop_incr'_129 _x_137 =
  coer_return coer_refl_ty (( = ) _x_137) >>= fun _b_132 ->
  coer_return coer_refl_ty (_b_132 0) >>= fun _b_131 ->
  if _b_131 then coer_return coer_refl_ty ()
  else
    coer_return coer_refl_ty (( - ) _x_137) >>= fun _b_134 ->
    coer_return coer_refl_ty (_b_134 1) >>= fun _b_133 ->
    _loop_incr'_129 _b_133 >>= fun _ ->
    Call (Incr, (), fun (_y_139 : unit) -> coer_return coer_refl_ty _y_139)

let loop_incr' = _loop_incr'_129

let _test_incr'_140 (_n_141 : int) =
  let rec _loop_incr'_174 (_x_137, _k_177) =
    if _x_137 = 0 then _k_177 ()
    else
      _loop_incr'_174
        (_x_137 - 1, fun (_ : unit) (_x_218 : int) -> _k_177 () (_x_218 + 1))
  and _loop_incr_175 _x_76 =
    if _x_76 = 0 then fun (_x_248 : int) -> _x_248
    else fun (_x_249 : int) -> _loop_incr_175 (_x_76 - 1) (_x_249 + 1)
  in
  _loop_incr'_174 (_n_141, fun (_x_148 : unit) (_x_150 : int) -> _x_150) 0

let test_incr' = _test_incr'_140

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_255 _x_268 =
  coer_return coer_refl_ty (( = ) _x_268) >>= fun _b_258 ->
  coer_return coer_refl_ty (_b_258 0) >>= fun _b_257 ->
  if _b_257 then coer_return coer_refl_ty ()
  else
    Call
      ( Get,
        (),
        fun (_y_272 : int) ->
          coer_computation coer_refl_ty
            (coer_return coer_refl_ty (( + ) _y_272))
          >>= fun _b_260 ->
          coer_computation coer_refl_ty (coer_return coer_refl_ty (_b_260 1))
          >>= fun _b_259 ->
          Call
            ( Put,
              _b_259,
              fun (_y_270 : unit) ->
                coer_return coer_refl_ty (( - ) _x_268) >>= fun _b_263 ->
                coer_return coer_refl_ty (_b_263 1) >>= fun _b_262 ->
                _loop_state_255 _b_262 ) )

let loop_state = _loop_state_255

let _test_state_274 (_n_275 : int) =
  let rec _loop_state_292 _x_268 =
    if _x_268 = 0 then fun (_x_352 : int) -> _x_352
    else fun (_s_353 : int) -> _loop_state_292 (_x_268 - 1) (_s_353 + 1)
  in
  _loop_state_292 _n_275 0

let test_state = _test_state_274
