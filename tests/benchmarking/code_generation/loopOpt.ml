open OcamlHeader

let _op_0 (* = *) = ( = )

let _op_1 (* < *) = ( < )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let rec loop_pure_4 n_5 =
  match (_op_0 (* = *) n_5) 0 with
  | true -> ()
  | false -> loop_pure_4 ((_op_2 (* - *) n_5) 1)

let test_pure_10 (n_11 : int) = loop_pure_4 n_11

type (_, _) effect += Fail : (unit, empty) effect

let rec loop_latent_12 n_13 =
  match (_op_0 (* = *) n_13) 0 with
  | true -> Value ()
  | false -> (
      match (_op_1 (* < *) n_13) 0 with
      | true ->
          Call
            ( Fail,
              (),
              fun (y_22 : empty) -> Value (match y_22 with _ -> assert false) )
      | false -> loop_latent_12 ((_op_2 (* - *) n_13) 1))

let test_latent_23 (n_24 : int) = loop_latent_12 n_24

type (_, _) effect += Incr : (unit, unit) effect

let rec loop_incr_25 n_26 =
  match (_op_0 (* = *) n_26) 0 with
  | true -> Value ()
  | false ->
      Call (Incr, (), fun (y_32 : unit) -> loop_incr_25 ((_op_2 (* - *) n_26) 1))

let test_incr_33 (n_34 : int) =
  (force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_41 : unit) -> Value (fun (x_43 : int) -> x_43));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () l_46 ->
                     Value
                       (fun (x_37 : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) l_46) ())
                           ((_op_3 (* + *) x_37) 1))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        (loop_incr_25 n_34)))
    0

let rec loop_incr'_47 n_48 =
  match (_op_0 (* = *) n_48) 0 with
  | true -> Value ()
  | false ->
      loop_incr'_47 ((_op_2 (* - *) n_48) 1) >> fun _ ->
      Call (Incr, (), fun (y_54 : unit) -> Value y_54)

let test_incr'_55 (n_56 : int) =
  (force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_63 : unit) -> Value (fun (x_65 : int) -> x_65));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Incr ->
                   fun () l_68 ->
                     Value
                       (fun (x_59 : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) l_68) ())
                           ((_op_3 (* + *) x_59) 1))
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        (loop_incr'_47 n_56)))
    0

type (_, _) effect += Get : (unit, int) effect

type (_, _) effect += Put : (int, unit) effect

let rec loop_state_69 n_70 =
  match (_op_0 (* = *) n_70) 0 with
  | true -> Value ()
  | false ->
      Call
        ( Get,
          (),
          fun (y_79 : int) ->
            Call
              ( Put,
                (_op_3 (* + *) y_79) 1,
                fun (y_81 : unit) -> loop_state_69 ((_op_2 (* - *) n_70) 1) ) )

let test_state_82 (n_83 : int) =
  (force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_91 : unit) -> Value (fun (x_93 : int) -> x_93));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Get ->
                   fun () l_96 ->
                     Value
                       (fun (s_86 : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) l_96) s_86)
                           s_86)
               | Put ->
                   fun s'_88 l_97 ->
                     Value
                       (fun (_ : int) ->
                         (((coer_arrow coer_refl_ty force_unsafe) l_97) ())
                           s'_88)
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        (loop_state_69 n_83)))
    0
