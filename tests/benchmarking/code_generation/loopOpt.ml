open OcamlHeader

let rec _loop_pure_45 _x_51 =
  match _x_51 = 0 with true -> () | false -> _loop_pure_45 (_x_51 - 1)

let loop_pure = _loop_pure_45

let _test_pure_57 (_n_58 : int) = _loop_pure_45 _n_58

let test_pure = _test_pure_57

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

let rec _loop_latent_59 _x_70 =
  match _x_70 = 0 with
  | true -> Value ()
  | false -> (
      match _x_70 < 0 with
      | true ->
          Call
            ( Fail,
              (),
              fun (_y_79 : empty) ->
                Value (match _y_79 with _ -> assert false) )
      | false -> _loop_latent_59 (_x_70 - 1))

let loop_latent = _loop_latent_59

let _test_latent_82 (_n_83 : int) = _loop_latent_59 _n_83

let test_latent = _test_latent_82

type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect

let rec _loop_incr_84 _x_92 =
  match _x_92 = 0 with
  | true -> Value ()
  | false -> Call (Incr, (), fun (_y_98 : unit) -> _loop_incr_84 (_x_92 - 1))

let loop_incr = _loop_incr_84

let _test_incr_101 (_n_102 : int) =
  (let rec _loop_incr_117 (_x_92, _k_119) =
     match _x_92 = 0 with
     | true -> _k_119 ()
     | false ->
         fun (_x_122 : int) ->
           _loop_incr_117
             (_x_92 - 1, fun (_x_118 : unit) -> _k_119 _x_118)
             (_x_122 + 1)
   in
   _loop_incr_117 (_n_102, fun (_x_109 : unit) (_x_111 : int) -> _x_111))
    0

let test_incr = _test_incr_101

let rec _loop_incr'_126 _x_134 =
  match _x_134 = 0 with
  | true -> Value ()
  | false ->
      _loop_incr'_126 (_x_134 - 1) >> fun _ ->
      Call (Incr, (), fun (_y_142 : unit) -> Value _y_142)

let loop_incr' = _loop_incr'_126

let _test_incr'_143 (_n_144 : int) =
  (let rec _loop_incr'_159 (_x_134, _k_162) =
     match _x_134 = 0 with
     | true -> _k_162 ()
     | false ->
         _loop_incr'_159
           (_x_134 - 1, fun (_ : unit) (_x_166 : int) -> _k_162 () (_x_166 + 1))
   and _loop_incr_160 (_x_92, _k_172) =
     match _x_92 = 0 with
     | true -> _k_172 ()
     | false ->
         fun (_x_175 : int) ->
           _loop_incr_160
             (_x_92 - 1, fun (_x_171 : unit) -> _k_172 _x_171)
             (_x_175 + 1)
   in
   _loop_incr'_159 (_n_144, fun (_x_151 : unit) (_x_153 : int) -> _x_153))
    0

let test_incr' = _test_incr'_143

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect

let rec _loop_state_179 _x_192 =
  match _x_192 = 0 with
  | true -> Value ()
  | false ->
      Call
        ( Get,
          (),
          fun (_y_201 : int) ->
            Call
              ( Put,
                _y_201 + 1,
                fun (_y_204 : unit) -> _loop_state_179 (_x_192 - 1) ) )

let loop_state = _loop_state_179

let _test_state_207 (_n_208 : int) =
  (let rec _loop_state_225 (_x_192, _k_227) =
     match _x_192 = 0 with
     | true -> _k_227 ()
     | false ->
         fun (_s_237 : int) ->
           _loop_state_225
             (_x_192 - 1, fun (_x_245 : unit) -> _k_227 _x_245)
             (_s_237 + 1)
   in
   _loop_state_225 (_n_208, fun (_x_216 : unit) (_x_218 : int) -> _x_218))
    0

let test_state = _test_state_207
