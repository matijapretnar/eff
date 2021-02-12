open OcamlHeader

let rec _loop_pure_41 _x_47 =
  match _x_47 = 0 with true -> () | false -> _loop_pure_41 (_x_47 - 1)

let loop_pure = _loop_pure_41

let _test_pure_53 (_n_54 : int) = _loop_pure_41 _n_54

let test_pure = _test_pure_53

type (_, _) effect += Fail : (unit, empty) effect

let rec _loop_latent_55 _x_66 =
  match _x_66 = 0 with
  | true -> Value ()
  | false -> (
      match _x_66 < 0 with
      | true ->
          Call
            ( Fail,
              (),
              fun (_y_75 : empty) ->
                Value (match _y_75 with _ -> assert false) )
      | false -> _loop_latent_55 (_x_66 - 1))

let loop_latent = _loop_latent_55

let _test_latent_78 (_n_79 : int) = _loop_latent_55 _n_79

let test_latent = _test_latent_78

type (_, _) effect += Incr : (unit, unit) effect

let rec _loop_incr_80 _x_88 =
  match _x_88 = 0 with
  | true -> Value ()
  | false -> Call (Incr, (), fun (_y_94 : unit) -> _loop_incr_80 (_x_88 - 1))

let loop_incr = _loop_incr_80

let _test_incr_97 (_n_98 : int) =
  (let rec _loop_incr_113 (_x_88, _k_115) =
     match _x_88 = 0 with
     | true -> _k_115 ()
     | false ->
         fun (_x_118 : int) ->
           _loop_incr_113
             (_x_88 - 1, fun (_x_114 : unit) -> _k_115 _x_114)
             (_x_118 + 1)
   in
   _loop_incr_113 (_n_98, fun (_x_105 : unit) (_x_107 : int) -> _x_107))
    0

let test_incr = _test_incr_97

let rec _loop_incr'_122 _x_130 =
  match _x_130 = 0 with
  | true -> Value ()
  | false ->
      _loop_incr'_122 (_x_130 - 1) >> fun _ ->
      Call (Incr, (), fun (_y_138 : unit) -> Value _y_138)

let loop_incr' = _loop_incr'_122

let _test_incr'_139 (_n_140 : int) =
  (let rec _loop_incr'_155 (_x_130, _k_158) =
     match _x_130 = 0 with
     | true -> _k_158 ()
     | false ->
         _loop_incr'_155
           (_x_130 - 1, fun (_ : unit) (_x_162 : int) -> _k_158 () (_x_162 + 1))
   and _loop_incr_156 (_x_88, _k_168) =
     match _x_88 = 0 with
     | true -> _k_168 ()
     | false ->
         fun (_x_171 : int) ->
           _loop_incr_156
             (_x_88 - 1, fun (_x_167 : unit) -> _k_168 _x_167)
             (_x_171 + 1)
   in
   _loop_incr'_155 (_n_140, fun (_x_147 : unit) (_x_149 : int) -> _x_149))
    0

let test_incr' = _test_incr'_139

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec _loop_state_175 _x_188 =
  match _x_188 = 0 with
  | true -> Value ()
  | false ->
      Call
        ( Get,
          (),
          fun (_y_197 : int) ->
            Call
              ( Put,
                _y_197 + 1,
                fun (_y_200 : unit) -> _loop_state_175 (_x_188 - 1) ) )

let loop_state = _loop_state_175

let _test_state_203 (_n_204 : int) =
  (let rec _loop_state_221 (_x_188, _k_223) =
     match _x_188 = 0 with
     | true -> _k_223 ()
     | false ->
         fun (_s_233 : int) ->
           _loop_state_221
             (_x_188 - 1, fun (_x_241 : unit) -> _k_223 _x_241)
             (_s_233 + 1)
   in
   _loop_state_221 (_n_204, fun (_x_212 : unit) (_x_214 : int) -> _x_214))
    0

let test_state = _test_state_203
