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
  let rec _loop_incr_114 _x_89 =
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
         (if _x_89 = 0 then Value ()
         else Call (Incr, (), fun (_y_95 : unit) -> _loop_incr_81 (_x_89 - 1))))
  in
  _loop_incr_114 _n_99 0

let test_incr = _test_incr_98

let rec _loop_incr'_115 _x_123 =
  if _x_123 = 0 then Value ()
  else
    _loop_incr'_115 (_x_123 - 1) >>= fun _ ->
    Call (Incr, (), fun (_y_131 : unit) -> Value _y_131)

let loop_incr' = _loop_incr'_115

let _test_incr'_132 (_n_133 : int) =
  let rec _loop_incr'_148 _x_123 =
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x_140 : unit) -> Value (fun (_x_142 : int) -> _x_142));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Incr ->
                    fun () _l_145 ->
                      Value
                        (fun (_x_136 : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_145 ()
                            (_x_136 + 1))
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (if _x_123 = 0 then Value ()
         else
           _loop_incr'_115 (_x_123 - 1) >>= fun _ ->
           Call (Incr, (), fun (_y_131 : unit) -> Value _y_131)))
  in
  _loop_incr'_148 _n_133 0

let test_incr' = _test_incr'_132

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_150 _x_163 =
  if _x_163 = 0 then Value ()
  else
    Call
      ( Get,
        (),
        fun (_y_172 : int) ->
          Call
            ( Put,
              _y_172 + 1,
              fun (_y_175 : unit) -> _loop_state_150 (_x_163 - 1) ) )

let loop_state = _loop_state_150

let _test_state_178 (_n_179 : int) =
  let rec _loop_state_196 _x_163 =
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x_187 : unit) -> Value (fun (_x_189 : int) -> _x_189));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Get ->
                    fun () _l_192 ->
                      Value
                        (fun (_s_182 : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_192 _s_182
                            _s_182)
                | Put ->
                    fun _s'_184 _l_193 ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _l_193 () _s'_184)
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (if _x_163 = 0 then Value ()
         else
           Call
             ( Get,
               (),
               fun (_y_172 : int) ->
                 Call
                   ( Put,
                     _y_172 + 1,
                     fun (_y_175 : unit) -> _loop_state_150 (_x_163 - 1) ) )))
  in
  _loop_state_196 _n_179 0

let test_state = _test_state_178
