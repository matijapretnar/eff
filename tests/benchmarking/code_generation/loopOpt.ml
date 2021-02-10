open OcamlHeader

let _op_0 (* = *) = ( = )

let _op_1 (* < *) = ( < )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let rec _loop_pure_4 _x_10 =
  match (_op_0 (* = *) _x_10) 0 with
  | true -> ()
  | false -> _loop_pure_4 ((_op_2 (* - *) _x_10) 1)

let _test_pure_16 (_n_17 : int) = _loop_pure_4 _n_17

type (_, _) effect += Fail : (unit, empty) effect

let rec _loop_latent_18 _x_29 =
  match (_op_0 (* = *) _x_29) 0 with
  | true -> Value ()
  | false -> (
      match (_op_1 (* < *) _x_29) 0 with
      | true ->
          Call
            ( Fail,
              (),
              fun (_y_38 : empty) ->
                Value (match _y_38 with _ -> assert false) )
      | false -> _loop_latent_18 ((_op_2 (* - *) _x_29) 1))

let _test_latent_41 (_n_42 : int) = _loop_latent_18 _n_42

type (_, _) effect += Incr : (unit, unit) effect

let rec _loop_incr_43 _x_51 =
  match (_op_0 (* = *) _x_51) 0 with
  | true -> Value ()
  | false ->
      Call
        (Incr, (), fun (_y_57 : unit) -> _loop_incr_43 ((_op_2 (* - *) _x_51) 1))

let _test_incr_60 (_n_61 : int) =
  (force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_68 : unit) -> Value (fun (_x_70 : int) -> _x_70));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () _l_73 ->
                     Value
                       (fun (_x_64 : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) _l_73) ())
                           ((_op_3 (* + *) _x_64) 1))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        (_loop_incr_43 _n_61)))
    0

let rec _loop_incr'_76 _x_84 =
  match (_op_0 (* = *) _x_84) 0 with
  | true -> Value ()
  | false ->
      _loop_incr'_76 ((_op_2 (* - *) _x_84) 1) >> fun _ ->
      Call (Incr, (), fun (_y_92 : unit) -> Value _y_92)

let _test_incr'_93 (_n_94 : int) =
  (force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_101 : unit) -> Value (fun (_x_103 : int) -> _x_103));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () _l_106 ->
                     Value
                       (fun (_x_97 : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) _l_106) ())
                           ((_op_3 (* + *) _x_97) 1))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        (_loop_incr'_76 _n_94)))
    0

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec _loop_state_109 _x_122 =
  match (_op_0 (* = *) _x_122) 0 with
  | true -> Value ()
  | false ->
      Call
        ( Get,
          (),
          fun (_y_131 : int) ->
            Call
              ( Put,
                (_op_3 (* + *) _y_131) 1,
                fun (_y_134 : unit) ->
                  _loop_state_109 ((_op_2 (* - *) _x_122) 1) ) )

let _test_state_137 (_n_138 : int) =
  (force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_146 : unit) -> Value (fun (_x_148 : int) -> _x_148));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Get ->
                   fun () _l_151 ->
                     Value
                       (fun (_s_141 : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) _l_151)
                            _s_141)
                           _s_141)
               | Put ->
                   fun _s'_143 _l_152 ->
                     Value
                       (fun (_ : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) _l_152) ())
                           _s'_143)
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        (_loop_state_109 _n_138)))
    0
