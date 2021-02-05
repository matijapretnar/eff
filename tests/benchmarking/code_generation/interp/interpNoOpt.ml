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

let _op_0 (* + *) = ( + )

let _op_1 (* * *) = ( * )

let _op_2 (* - *) = ( - )

let _op_3 (* ~- *) = ( ~- )

let _op_4 (* / *) = ( / )

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) effect += DivByZero : (unit, int) effect

let bigTest_5 (() : unit) =
  let rec interp_6 _x_7 =
    match coer_refl_ty _x_7 with
    | Num b_8 -> (coer_return coer_refl_ty) b_8
    | Add (l_9, r_10) ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                     interp_6))
                 l_9)
          >> fun x_11 ->
            (coer_computation coer_refl_ty)
              ( (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         interp_6))
                     r_10)
              >> fun y_12 ->
                (coer_return coer_refl_ty)
                  (let _b_13 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_0 (* + *))
                          x_11)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_13) y_12)) ) )
    | Mul (l_14, r_15) ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                     interp_6))
                 l_14)
          >> fun x_16 ->
            (coer_computation coer_refl_ty)
              ( (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         interp_6))
                     r_15)
              >> fun y_17 ->
                (coer_return coer_refl_ty)
                  (let _b_18 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_1 (* * *))
                          x_16)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_18) y_17)) ) )
    | Sub (l_19, r_20) ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                     interp_6))
                 l_19)
          >> fun x_21 ->
            (coer_computation coer_refl_ty)
              ( (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         interp_6))
                     r_20)
              >> fun y_22 ->
                (coer_return coer_refl_ty)
                  (let _b_23 =
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty
                            (coer_arrow coer_refl_ty coer_refl_ty))
                           _op_2 (* - *))
                          x_21)
                   in
                   coer_refl_ty
                     (((coer_arrow coer_refl_ty coer_refl_ty) _b_23) y_22)) ) )
    | Div (l_24, r_25) ->
        (coer_computation coer_refl_ty)
          ( (coer_computation coer_refl_ty)
              (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                  ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                     interp_6))
                 r_25)
          >> fun y_26 ->
            (coer_computation coer_refl_ty)
              ( (coer_computation coer_refl_ty)
                  (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                      ((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                         interp_6))
                     l_24)
              >> fun x_27 ->
                (coer_computation coer_refl_ty)
                  (match coer_refl_ty y_26 with
                  | 0 ->
                      (coer_computation coer_refl_ty)
                        (((coer_arrow coer_refl_ty
                             (coer_computation coer_refl_ty))
                            (fun (x_41 : unit) ->
                              Call
                                ( DivByZero,
                                  x_41,
                                  fun (y_42 : int) ->
                                    (coer_return coer_refl_ty) y_42 )))
                           ())
                  | _ ->
                      (coer_return coer_refl_ty)
                        (let _b_28 =
                           coer_refl_ty
                             (((coer_arrow coer_refl_ty
                                  (coer_arrow coer_refl_ty coer_refl_ty))
                                 _op_4 (* / *))
                                x_27)
                         in
                         coer_refl_ty
                           (((coer_arrow coer_refl_ty coer_refl_ty) _b_28) y_26)))
              ) )
  in
  let addCase_29 =
    Add
      (coer_refl_ty
         ( Add
             (coer_refl_ty
                ( Add
                    (coer_refl_ty (Num (coer_refl_ty 20), Num (coer_refl_ty 2))),
                  Mul
                    (coer_refl_ty (Num (coer_refl_ty 1), Num (coer_refl_ty 2)))
                )),
           Sub
             (coer_refl_ty
                ( Add (coer_refl_ty (Num (coer_refl_ty 2), Num (coer_refl_ty 2))),
                  Div
                    (coer_refl_ty (Num (coer_refl_ty 1), Num (coer_refl_ty 10)))
                )) ))
  in
  let rec createCase_30 n_31 =
    match coer_refl_ty n_31 with
    | 1 ->
        coer_refl_ty
          (Div (coer_refl_ty (Num (coer_refl_ty 100), Num (coer_refl_ty 0))))
    | _ ->
        coer_refl_ty
          (let _b_32 =
             coer_refl_ty
               (let _b_33 =
                  coer_refl_ty
                    (let _b_34 =
                       coer_refl_ty
                         (((coer_arrow coer_refl_ty
                              (coer_arrow coer_refl_ty coer_refl_ty))
                             _op_2 (* - *))
                            n_31)
                     in
                     coer_refl_ty
                       (((coer_arrow coer_refl_ty coer_refl_ty) _b_34) 1))
                in
                coer_refl_ty
                  (((coer_arrow coer_refl_ty coer_refl_ty)
                      ((coer_arrow coer_refl_ty coer_refl_ty) createCase_30))
                     _b_33))
           in
           coer_refl_ty
             (Add
                (((* tuple_coer *) coer_tuple_2 (coer_refl_ty, coer_refl_ty))
                   (addCase_29, _b_32))))
  in
  let finalCase_35 =
    coer_refl_ty (((coer_arrow coer_refl_ty coer_refl_ty) createCase_30) 200)
  in
  coer_refl_ty
    (let arithmeticHandler_36 =
       (coer_handler
          (coer_computation coer_refl_ty)
          (coer_computation coer_refl_ty))
         (handler
            {
              value_clause = (fun (_id_38 : int) -> Value (coer_refl_ty _id_38));
              effect_clauses =
                (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
                  match eff with
                  | DivByZero ->
                      fun () l_43 ->
                        Value
                          (coer_refl_ty
                             (((coer_arrow coer_refl_ty coer_refl_ty)
                                 _op_3 (* ~- *))
                                1))
                  | eff' -> fun arg k -> Call (eff', arg, k));
            })
     in
     (coer_unsafe (*unsafe*) coer_refl_ty)
       (((coer_handler
            (coer_computation coer_refl_ty)
            (coer_computation coer_refl_ty))
           arithmeticHandler_36)
          ((coer_computation coer_refl_ty)
             ( (coer_return coer_refl_ty)
                 (((coer_arrow coer_refl_ty coer_refl_ty) createCase_30) 200)
             >> fun _b_40 ->
               (coer_computation coer_refl_ty)
                 (((coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
                     interp_6)
                    _b_40) ))))
