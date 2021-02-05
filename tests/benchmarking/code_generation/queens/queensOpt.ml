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

let _op_0 (* < *) = ( < )

let _op_1 (* = *) = ( = )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let _op_4 (* ~- *) = ( ~- )

type (_, _) effect += Decide : (unit, bool) effect

type (_, _) effect += Fail : (unit, empty) effect

type inttuple = IntTuple of (int * int)

type intlist = IntNil | IntCons of (int * intlist)

type inttuplist = IntTupNil | IntTupCons of (inttuple * inttuplist)

type void = Void

let test_queens_5 (n_6 : int) =
  let absurd_7 (void_8 : empty) = match void_8 with _ -> assert false in
  let _op_9 (* > *) (x_10 : int) (y_11 : int) = (_op_0 (* < *) y_11) x_10 in
  let _op_13 (* <> *) (x_14 : int) (y_15 : int) =
    match (_op_1 (* = *) y_15) x_14 with true -> false | false -> true
  in
  let abs_18 (x_19 : int) =
    match (_op_0 (* < *) x_19) 0 with
    | true -> _op_4 (* ~- *) x_19
    | false -> x_19
  in
  let no_attack_22 (q1_23 : inttuple) (q2_24 : inttuple) =
    match q1_23 with
    | IntTuple (x_25, y_26) -> (
        match q2_24 with
        | IntTuple (x'_27, y'_28) -> (
            match (_op_13 (* <> *) x_25) x'_27 with
            | true -> (
                match (_op_13 (* <> *) y_26) y'_28 with
                | true ->
                    (_op_13 (* <> *) (abs_18 ((_op_2 (* - *) x_25) x'_27)))
                      (abs_18 ((_op_2 (* - *) y_26) y'_28))
                | false -> false)
            | false -> false))
  in
  let rec not_attacked_40 x'_41 (qs_42 : inttuplist) =
    match qs_42 with
    | IntTupNil -> true
    | IntTupCons (x_43, xs_44) -> (
        match (no_attack_22 x'_41) x_43 with
        | true -> (not_attacked_40 x'_41) xs_44
        | false -> false)
  in
  let available_48 (number_of_queens_49 : int) (x_50 : int) (qs_51 : inttuplist)
      =
    let rec loop_52 possible_53 (y_54 : int) =
      match (_op_0 (* < *) y_54) 1 with
      | true -> possible_53
      | false -> (
          match (not_attacked_40 (IntTuple (x_50, y_54))) qs_51 with
          | true ->
              (loop_52 (IntCons (y_54, possible_53))) ((_op_2 (* - *) y_54) 1)
          | false -> (loop_52 possible_53) ((_op_2 (* - *) y_54) 1))
    in
    (loop_52 IntNil) number_of_queens_49
  in
  let rec choose_66 xs_67 =
    match xs_67 with
    | IntNil ->
        (fun (x_103 : unit) ->
          Call (Fail, x_103, fun (y_104 : empty) -> Value y_104))
          ()
        >> fun _b_68 -> Value (match _b_68 with _ -> assert false)
    | IntCons (x_69, xs'_70) -> (
        (fun (x_101 : unit) ->
          Call (Decide, x_101, fun (y_102 : bool) -> Value y_102))
          ()
        >> fun _b_71 ->
        match _b_71 with true -> Value x_69 | false -> choose_66 xs'_70)
  in
  (let rec place_84 x_85 (qs_86 : inttuplist) =
     match (_op_9 (* > *) x_85) n_6 with
     | true -> Value qs_86
     | false ->
         choose_66 (((available_48 n_6) x_85) qs_86) >> fun y_89 ->
         (place_84 ((_op_3 (* + *) x_85) 1))
           (IntTupCons (IntTuple (x_85, y_89), qs_86))
   in
   force_unsafe
     ((handler
         {
           value_clause =
             (fun (_x_79 : inttuplist) ->
               Value
                 ((coer_arrow coer_refl_ty (coer_return coer_refl_ty))
                    (fun (_ : unit -> inttuplist computation) -> _x_79)));
           effect_clauses =
             (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
               match eff with
               | Decide ->
                   fun _ l_105 ->
                     Value
                       (fun (kf_74 : unit -> inttuplist computation) ->
                         (((coer_arrow coer_refl_ty force_unsafe) l_105) true)
                           (fun (_ : unit) ->
                             (((coer_arrow coer_refl_ty force_unsafe) l_105)
                                false)
                               kf_74))
               | Fail ->
                   fun _ l_106 ->
                     Value
                       (fun (kf_78 : unit -> inttuplist computation) ->
                         kf_78 ())
               | eff' -> fun arg k -> Call (eff', arg, k));
         })
        ((place_84 1) IntTupNil))) (fun (() : unit) ->
      Call (Fail, (), fun (y_108 : empty) -> Value (absurd_7 y_108)))
