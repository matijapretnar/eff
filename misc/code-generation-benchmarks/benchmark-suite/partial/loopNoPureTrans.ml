open OcamlHeader

let rec _loop_pure_42 _x_48 =
  Value (( = ) _x_48) >>= fun _b_50 ->
  Value (_b_50 0) >>= fun _b_51 ->
  if _b_51 then ()
  else
    Value (( - ) _x_48) >>= fun _b_52 ->
    Value (_b_52 1) >>= fun _b_53 -> _loop_pure_42 _b_53

let loop_pure = _loop_pure_42

let _test_pure_54 (_n_55 : int) = _loop_pure_42 _n_55

let test_pure = _test_pure_54

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

let rec _loop_latent_56 _x_67 =
  Value (( = ) _x_67) >>= fun _b_72 ->
  Value (_b_72 0) >>= fun _b_73 ->
  if _b_73 then Value ()
  else
    Value (( < ) _x_67) >>= fun _b_74 ->
    Value (_b_74 0) >>= fun _b_75 ->
    if _b_75 then
      Call
        ( Fail,
          (),
          fun (_y_76 : empty) -> Value (match _y_76 with _ -> assert false) )
    else
      Value (( - ) _x_67) >>= fun _b_77 ->
      Value (_b_77 1) >>= fun _b_78 -> _loop_latent_56 _b_78

let loop_latent = _loop_latent_56

let _test_latent_79 (_n_80 : int) = _loop_latent_56 _n_80

let test_latent = _test_latent_79

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let rec _loop_incr_81 _x_89 =
  Value (( = ) _x_89) >>= fun _b_93 ->
  Value (_b_93 0) >>= fun _b_94 ->
  if _b_94 then Value ()
  else
    Call
      ( Incr,
        (),
        fun (_y_95 : unit) ->
          Value (( - ) _x_89) >>= fun _b_96 ->
          Value (_b_96 1) >>= fun _b_97 -> _loop_incr_81 _b_97 )

let loop_incr = _loop_incr_81

let _test_incr_98 (_n_99 : int) =
  Value
    (let rec _loop_incr_114 _x_89 =
       Value (( = ) _x_89) >>= fun _x_130 ->
       Value (_x_130 0) >>= fun _x_140 ->
       if _x_140 then fun (_x_141 : int) -> _x_141
       else fun (_x_142 : int) ->
         Value (( - ) _x_89) >>= fun _x_143 ->
         Value (_x_143 1) >>= fun _x_144 ->
         Value (_loop_incr_114 _x_144) >>= fun _b_145 ->
         Value (( + ) _x_142) >>= fun _b_146 ->
         Value (_b_146 1) >>= fun _b_147 -> _b_145 _b_147
     in
     _loop_incr_114 _n_99)
  >>= fun _b_113 -> _b_113 0

let test_incr = _test_incr_98

let rec _loop_incr'_148 _x_156 =
  Value (( = ) _x_156) >>= fun _b_160 ->
  Value (_b_160 0) >>= fun _b_161 ->
  if _b_161 then Value ()
  else
    Value (( - ) _x_156) >>= fun _b_162 ->
    Value (_b_162 1) >>= fun _b_163 ->
    _loop_incr'_148 _b_163 >>= fun _ ->
    Call (Incr, (), fun (_y_164 : unit) -> Value _y_164)

let loop_incr' = _loop_incr'_148

let _test_incr'_165 (_n_166 : int) =
  Value
    (let rec _loop_incr'_200 (_x_156, _k_203) =
       Value (( = ) _x_156) >>= fun _x_232 ->
       Value (_x_232 0) >>= fun _x_257 ->
       if _x_257 then _k_203 ()
       else
         Value (( - ) _x_156) >>= fun _x_258 ->
         Value (_x_258 1) >>= fun _x_259 ->
         _loop_incr'_200
           ( _x_259,
             fun (_ : unit) (_x_260 : int) ->
               Value (_k_203 ()) >>= fun _b_261 ->
               Value (( + ) _x_260) >>= fun _b_262 ->
               Value (_b_262 1) >>= fun _b_263 -> _b_261 _b_263 )
     and _loop_incr_201 _x_89 =
       Value (( = ) _x_89) >>= fun _x_248 ->
       Value (_x_248 0) >>= fun _x_273 ->
       if _x_273 then fun (_x_274 : int) -> _x_274
       else fun (_x_275 : int) ->
         Value (( - ) _x_89) >>= fun _x_276 ->
         Value (_x_276 1) >>= fun _x_277 ->
         Value (_loop_incr_201 _x_277) >>= fun _b_278 ->
         Value (( + ) _x_275) >>= fun _b_279 ->
         Value (_b_279 1) >>= fun _b_280 -> _b_278 _b_280
     in
     _loop_incr'_200 (_n_166, fun (_x_173 : unit) (_x_175 : int) -> _x_175))
  >>= fun _b_180 -> _b_180 0

let test_incr' = _test_incr'_165

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_281 _x_294 =
  Value (( = ) _x_294) >>= fun _b_301 ->
  Value (_b_301 0) >>= fun _b_302 ->
  if _b_302 then Value ()
  else
    Call
      ( Get,
        (),
        fun (_y_303 : int) ->
          Value (( + ) _y_303) >>= fun _b_304 ->
          Value (_b_304 1) >>= fun _b_305 ->
          Call
            ( Put,
              _b_305,
              fun (_y_306 : unit) ->
                Value (( - ) _x_294) >>= fun _b_307 ->
                Value (_b_307 1) >>= fun _b_308 -> _loop_state_281 _b_308 ) )

let loop_state = _loop_state_281

let _test_state_309 (_n_310 : int) =
  Value
    (let rec _loop_state_327 _x_294 =
       Value (( = ) _x_294) >>= fun _x_376 ->
       Value (_x_376 0) >>= fun _x_386 ->
       if _x_386 then fun (_x_387 : int) -> _x_387
       else fun (_s_388 : int) ->
         Value (( + ) _s_388) >>= fun _x_389 ->
         Value (_x_389 1) >>= fun _x_390 ->
         Value (( - ) _x_294) >>= fun _x_391 ->
         Value (_x_391 1) >>= fun _x_392 ->
         Value (_loop_state_327 _x_392) >>= fun _b_393 -> _b_393 _x_390
     in
     _loop_state_327 _n_310)
  >>= fun _b_326 -> _b_326 0

let test_state = _test_state_309
