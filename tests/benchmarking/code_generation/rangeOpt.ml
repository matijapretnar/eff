open OcamlHeader

type (_, _) effect += Fetch : (unit, int) effect

let _op_0 (* - *) = ( - )

type int_list = Nil | Cons of (int * int_list)

let test_1 (n_2 : int) =
  let rec range_3 n_4 =
    match n_4 with
    | 0 -> Value Nil
    | _ ->
        (fun (x_13 : unit) ->
          Call (Fetch, x_13, fun (y_14 : int) -> Value y_14))
          ()
        >> fun _b_5 ->
        range_3 ((_op_0 (* - *) n_4) 1) >> fun _b_6 -> Value (Cons (_b_5, _b_6))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x_10 : int_list) -> Value _x_10);
          effect_clauses =
            (fun (type a b) (eff : (a, b) effect) : (a -> (b -> _) -> _) ->
              match eff with
              | Fetch ->
                  fun _ l_15 ->
                    Value (((coer_arrow coer_refl_ty force_unsafe) l_15) 42)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (range_3 n_2))
