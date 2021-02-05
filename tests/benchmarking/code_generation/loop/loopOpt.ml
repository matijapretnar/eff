type empty

type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
      -> 'a computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
  ('eff_arg, 'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b

type ('a, 'b) handler_clauses = {
  value_clause : 'a -> 'b;
  effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses;
}

let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> k y >> f)

let handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler = function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff in
        clause arg (fun y -> handler (k y))
  in
  handler

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let run = function Value x -> x | Call (_, _, _) -> failwith "Uncaught effect"

let ( ** ) =
  let rec pow a =
    Stdlib.(
      function
      | 0 -> 1
      | 1 -> a
      | n ->
          let b = pow a (n / 2) in
          b * b * if n mod 2 = 0 then 1 else a)
  in
  pow

let string_length _ = assert false

let to_string _ = assert false

let lift_unary f x = Value (f x)

let lift_binary f x = Value (fun y -> Value (f x y))

let coer_refl_ty term = term

let rec coer_computation coer comp =
  match comp with
  | Value t -> Value (coer t)
  | Call (eff, arg, k) -> Call (eff, arg, fun x -> coer_computation coer (k x))

let coer_return coer term = Value (coer term)

let coer_unsafe coer = function
  | Value v -> coer v
  | Call (_eff, _arg, _k) -> failwith "Unsafe coercion"

let force_unsafe = function
  | Value v -> v
  | Call (_eff, _arg, _k) -> failwith "Unsafe value force"

(* Manual tuple coercions, one way to do this a bit better is to use GADT and map over them *)

let coer_tuple_2 (c1, c2) (a1, a2) = (c1 a1, c2 a2)

let coer_tuple_3 (c1, c2, c3) (a1, a2, a3) = (c1 a1, c2 a2, c3 a3)

let coer_tuple_4 (c1, c2, c3, c4) (a1, a2, a3, a4) = (c1 a1, c2 a2, c3 a3, c4 a4)

let coer_tuple_5 (c1, c2, c3, c4, c5) (a1, a2, a3, a4, a5) =
  (c1 a1, c2 a2, c3 a3, c4 a4, c5 a5)

(* This should be enough *)

let coer_arrow coer1 coer2 f x = coer2 (f (coer1 x))

let coer_handler coer1 coer2 h x = coer2 (h (coer1 x))

let coer_hand_to_fun coer1 coer2 h x = coer2 (h (Value (coer1 x)))

let rec coer_fun_to_hand coer1 coer2 f comp =
  match comp with
  | Value t -> coer2 (f (coer1 t))
  | Call (eff, arg, k) ->
      Call (eff, arg, fun x -> coer_fun_to_hand coer1 coer2 f (k x))

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
