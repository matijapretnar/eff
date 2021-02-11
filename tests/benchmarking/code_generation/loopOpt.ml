open OcamlHeader

let _op_0 (* = *) = ( = )

let _op_1 (* < *) = ( < )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let rec _loop_pure_4 _x_10 =
  match _op_0 (* = *) _x_10 0 with
  | true -> ()
  | false -> _loop_pure_4 (_op_2 (* - *) _x_10 1)

let loop_pure = _loop_pure_4

let _test_pure_16 (_n_17 : int) = _loop_pure_4 _n_17

let test_pure = _test_pure_16

type (_, _) effect += Fail : (unit, empty) effect

let rec _loop_latent_18 _x_29 =
  match _op_0 (* = *) _x_29 0 with
  | true -> Value ()
  | false -> (
      match _op_1 (* < *) _x_29 0 with
      | true ->
          Call
            ( Fail,
              (),
              fun (_y_38 : empty) ->
                Value (match _y_38 with _ -> assert false) )
      | false -> _loop_latent_18 (_op_2 (* - *) _x_29 1))

let loop_latent = _loop_latent_18

let _test_latent_41 (_n_42 : int) = _loop_latent_18 _n_42

let test_latent = _test_latent_41

type (_, _) effect += Incr : (unit, unit) effect

let rec _loop_incr_43 _x_51 =
  match _op_0 (* = *) _x_51 0 with
  | true -> Value ()
  | false ->
      Call
        (Incr, (), fun (_y_57 : unit) -> _loop_incr_43 (_op_2 (* - *) _x_51 1))

let loop_incr = _loop_incr_43

let _test_incr_60 (_n_61 : int) =
  (let rec _loop_incr_76 (_x_51, _k_78) =
     match _op_0 (* = *) _x_51 0 with
     | true -> _k_78 ()
     | false ->
         let _l_73 (_y_57 : unit) =
           _loop_incr_76
             (_op_2 (* - *) _x_51 1, fun (_x_77 : unit) -> _k_78 _x_77)
         in
         fun (_x_64 : int) -> _l_73 () (_op_3 (* + *) _x_64 1)
   in
   _loop_incr_76 (_n_61, fun (_x_68 : unit) (_x_70 : int) -> _x_70))
    0

let test_incr = _test_incr_60

let rec _loop_incr'_80 _x_88 =
  match _op_0 (* = *) _x_88 0 with
  | true -> Value ()
  | false ->
      _loop_incr'_80 (_op_2 (* - *) _x_88 1) >> fun _ ->
      Call (Incr, (), fun (_y_96 : unit) -> Value _y_96)

let loop_incr' = _loop_incr'_80

let _test_incr'_97 (_n_98 : int) =
  (let rec _loop_incr'_113 (_x_88, _k_116) =
     match _op_0 (* = *) _x_88 0 with
     | true -> _k_116 ()
     | false ->
         _loop_incr'_113
           ( _op_2 (* - *) _x_88 1,
             fun (_ : unit) ->
               let _l_110 (_y_96 : unit) = _k_116 _y_96 in
               fun (_x_101 : int) -> _l_110 () (_op_3 (* + *) _x_101 1) )
   and _loop_incr_114 (_x_51, _k_120) =
     match _op_0 (* = *) _x_51 0 with
     | true -> _k_120 ()
     | false ->
         let _l_110 (_y_57 : unit) =
           _loop_incr_114
             (_op_2 (* - *) _x_51 1, fun (_x_119 : unit) -> _k_120 _x_119)
         in
         fun (_x_101 : int) -> _l_110 () (_op_3 (* + *) _x_101 1)
   in
   _loop_incr'_113 (_n_98, fun (_x_105 : unit) (_x_107 : int) -> _x_107))
    0

let test_incr' = _test_incr'_97

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec _loop_state_122 _x_135 =
  match _op_0 (* = *) _x_135 0 with
  | true -> Value ()
  | false ->
      Call
        ( Get,
          (),
          fun (_y_144 : int) ->
            Call
              ( Put,
                _op_3 (* + *) _y_144 1,
                fun (_y_147 : unit) -> _loop_state_122 (_op_2 (* - *) _x_135 1)
              ) )

let loop_state = _loop_state_122

let _test_state_150 (_n_151 : int) =
  (let rec _loop_state_168 (_x_135, _k_170) =
     match _op_0 (* = *) _x_135 0 with
     | true -> _k_170 ()
     | false ->
         let _l_164 (_y_144 : int) =
           let _b_146 = _op_3 (* + *) _y_144 1 in
           let _l_173 (_y_175 : unit) =
             _loop_state_168
               (_op_2 (* - *) _x_135 1, fun (_x_178 : unit) -> _k_170 _x_178)
           in
           fun (_ : int) -> _l_173 () _b_146
         in
         fun (_s_154 : int) -> _l_164 _s_154 _s_154
   in
   _loop_state_168 (_n_151, fun (_x_159 : unit) (_x_161 : int) -> _x_161))
    0

let test_state = _test_state_150
