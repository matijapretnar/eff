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
         let _l_110 (_y_94 : unit) =
           _loop_incr_113 (_x_88 - 1, fun (_x_114 : unit) -> _k_115 _x_114)
         in
         fun (_x_101 : int) -> _l_110 () (_x_101 + 1)
   in
   _loop_incr_113 (_n_98, fun (_x_105 : unit) (_x_107 : int) -> _x_107))
    0

let test_incr = _test_incr_97

let rec _loop_incr'_117 _x_125 =
  match _x_125 = 0 with
  | true -> Value ()
  | false ->
      _loop_incr'_117 (_x_125 - 1) >> fun _ ->
      Call (Incr, (), fun (_y_133 : unit) -> Value _y_133)

let loop_incr' = _loop_incr'_117

let _test_incr'_134 (_n_135 : int) =
  (let rec _loop_incr'_150 (_x_125, _k_153) =
     match _x_125 = 0 with
     | true -> _k_153 ()
     | false ->
         _loop_incr'_150
           ( _x_125 - 1,
             fun (_ : unit) ->
               let _l_147 (_y_133 : unit) = _k_153 _y_133 in
               fun (_x_138 : int) -> _l_147 () (_x_138 + 1) )
   and _loop_incr_151 (_x_88, _k_157) =
     match _x_88 = 0 with
     | true -> _k_157 ()
     | false ->
         let _l_147 (_y_94 : unit) =
           _loop_incr_151 (_x_88 - 1, fun (_x_156 : unit) -> _k_157 _x_156)
         in
         fun (_x_138 : int) -> _l_147 () (_x_138 + 1)
   in
   _loop_incr'_150 (_n_135, fun (_x_142 : unit) (_x_144 : int) -> _x_144))
    0

let test_incr' = _test_incr'_134

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec _loop_state_159 _x_172 =
  match _x_172 = 0 with
  | true -> Value ()
  | false ->
      Call
        ( Get,
          (),
          fun (_y_181 : int) ->
            Call
              ( Put,
                _y_181 + 1,
                fun (_y_184 : unit) -> _loop_state_159 (_x_172 - 1) ) )

let loop_state = _loop_state_159

let _test_state_187 (_n_188 : int) =
  (let rec _loop_state_205 (_x_172, _k_207) =
     match _x_172 = 0 with
     | true -> _k_207 ()
     | false ->
         let _l_201 (_y_181 : int) =
           let _b_183 = _y_181 + 1 in
           let _l_210 (_y_212 : unit) =
             _loop_state_205 (_x_172 - 1, fun (_x_215 : unit) -> _k_207 _x_215)
           in
           fun (_ : int) -> _l_210 () _b_183
         in
         fun (_s_191 : int) -> _l_201 _s_191 _s_191
   in
   _loop_state_205 (_n_188, fun (_x_196 : unit) (_x_198 : int) -> _x_198))
    0

let test_state = _test_state_187
