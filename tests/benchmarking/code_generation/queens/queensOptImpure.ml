(*
=== GENERATED FROM queens.eff ===
commit SHA: 03cdc167bd82ae792396973571e61b43009cf73a
=== BEGIN SOURCE ===

external ( <> ) : int -> int -> bool = "<>"
external ( < ) : int -> int -> bool = "<"
external ( > ) : int -> int -> bool = ">"
external ( - ) : int -> int -> int = "-"
external ( + ) : int -> int -> int = "+"
external ( ~- ) : int -> int = "~-"

let absurd void = match void with;;

let abs x = if x < 0 then -x else x

let rec (@) xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (xs @ ys)

(******************************************************************************)
let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec not_attacked x' = function
  | [] -> true
  | x :: xs -> if no_attack x' x then not_attacked x' xs else false

let available (number_of_queens, x, qs) =
  let rec loop (possible, y) =
    if y < 1 then
      possible
    else if not_attacked (x, y) qs then
      loop ((y :: possible), (y - 1))
    else
      loop (possible, (y - 1))
  in
  loop ([], number_of_queens)

(******************************************************************************)

effect Decide : unit -> bool
effect Fail : unit -> empty

type 'a option = None | Some of 'a

let rec choose = function
  | [] -> (match (#Fail ()) with)
  | x::xs -> if #Decide () then x else choose xs

let optionalize = handler
  | val y -> (Some y)
  | #Decide _ k -> (match k true with Some x -> Some x | None -> k false)
  | #Fail _ _ -> None

let backtrack = handler
  | val y -> (fun _ -> y)
  | #Decide _ k -> (fun kf -> k true (fun () -> k false kf) )  
  | #Fail _ _ -> (fun kf -> kf ())

let choose_all = handler
  | val x -> [x]
  | #Decide _ k -> k true @ k false
  | #Fail _ _ -> []

(******************************************************************************)

let queens number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then qs else
      let y = choose (available (number_of_queens, x, qs)) in
      place ((x + 1), ((x, y) :: qs))
  in
  place (1, [])

let queens_one_option number_of_queens =
  with optionalize handle queens number_of_queens

let queens_one_cps number_of_queens =
  (with backtrack handle queens number_of_queens) (fun () -> (absurd (#Fail ())))

let queens_all number_of_queens =
  with choose_all handle queens number_of_queens

=== END SOURCE ===
*)

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

let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler = function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff in
        clause arg (fun y -> handler (k y))
  in
  handler

let value (x : 'a) : 'a computation = Value x

let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
    'c computation =
  Call (eff, arg, cont)

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let effect eff arg = call eff arg value

let run = function
  | Value x -> x
  | Call (eff, _, _) -> failwith "Uncaught effect"

let ( ** ) =
  let rec pow a =
    let open Pervasives in
    function
    | 0 -> 1
    | 1 -> a
    | n ->
        let b = pow a (n / 2) in
        b * b * if n mod 2 = 0 then 1 else a
  in
  pow

let string_length _ = assert false

let to_string _ = assert false

let lift_unary f x = value (f x)

let lift_binary f x = value (fun y -> value (f x y))

;;
value "End of pervasives"

let _var_1 x = lift_binary ( <> ) x

let _var_2 x = lift_binary ( < ) x

let _var_3 x = lift_binary ( > ) x

let _var_4 x = lift_binary ( - ) x

let _var_5 x = lift_binary ( + ) x

let _var_6 x = lift_unary ( ~- ) x

let _absurd_7 _void_8 = match _void_8 with _ -> assert false

let _abs_9 _x_10 =
  match run ((run (lift_binary ( < ) _x_10)) 0) with
  | true -> lift_unary ( ~- ) _x_10
  | false -> value _x_10

let rec _var_13 _xs_14 =
  value (fun _ys_15 ->
      match _xs_14 with
      | [] -> value _ys_15
      | _x_16 :: _xs_17 -> value (_x_16 :: run ((run (_var_13 _xs_17)) _ys_15)))

let _no_attack_20 (_x_21, _y_22) =
  value (fun (_x'_23, _y'_24) ->
      match run ((run (lift_binary ( <> ) _x_21)) _x'_23) with
      | true -> (
          match run ((run (lift_binary ( <> ) _y_22)) _y'_24) with
          | true ->
              (run
                 (lift_binary ( <> )
                    (run
                       (_abs_9 (run ((run (lift_binary ( - ) _x_21)) _x'_23))))))
                (run (_abs_9 (run ((run (lift_binary ( - ) _y_22)) _y'_24))))
          | false -> value false)
      | false -> value false)

let rec _not_attacked_36 _x'_37 =
  value (fun _gen_function_38 ->
      match _gen_function_38 with
      | [] -> value true
      | _x_39 :: _xs_40 -> (
          match run ((run (_no_attack_20 _x'_37)) _x_39) with
          | true -> (run (_not_attacked_36 _x'_37)) _xs_40
          | false -> value false))

let _available_44 (_number_of_queens_45, _x_46, _qs_47) =
  let rec _loop_48 (_possible_49, _y_50) =
    match run ((run (lift_binary ( < ) _y_50)) 1) with
    | true -> value _possible_49
    | false -> (
        match run ((run (_not_attacked_36 (_x_46, _y_50))) _qs_47) with
        | true ->
            _loop_48
              (_y_50 :: _possible_49, run ((run (lift_binary ( - ) _y_50)) 1))
        | false ->
            _loop_48 (_possible_49, run ((run (lift_binary ( - ) _y_50)) 1)))
  in
  _loop_48 ([], _number_of_queens_45)

type (_, _) effect += Effect_Decide : (unit, bool) effect

type (_, _) effect += Effect_Fail : (unit, unit) effect

type 't1 option = None | Some of 't1

let rec _choose_59 _gen_let_rec_function_60 =
  match _gen_let_rec_function_60 with
  | [] ->
      call Effect_Fail () (fun _result_3 ->
          match _result_3 with _ -> assert false)
  | _x_62 :: _xs_63 ->
      call Effect_Decide () (fun _result_6 ->
          match _result_6 with
          | true -> value _x_62
          | false -> _choose_59 _xs_63)

let _optionalize_65 c =
  handler
    {
      value_clause = (fun _y_69 -> value (Some _y_69));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Decide -> (
              fun (_ : unit) (_k_66 : bool -> _ computation) ->
                _k_66 true >> fun _gen_bind_68 ->
                match _gen_bind_68 with
                | Some _x_67 -> value (Some _x_67)
                | None -> _k_66 false)
          | Effect_Fail ->
              fun (_ : unit) (_ : unit -> _ computation) -> value None
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _backtrack_70 c =
  handler
    {
      value_clause = (fun _y_76 -> value (fun _ -> value _y_76));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Decide ->
              fun (_ : unit) (_k_72 : bool -> _ computation) ->
                value (fun _kf_73 ->
                    _k_72 true >> fun _gen_bind_74 ->
                    _gen_bind_74 (fun () ->
                        _k_72 false >> fun _gen_bind_75 -> _gen_bind_75 _kf_73))
          | Effect_Fail ->
              fun (_ : unit) (_ : unit -> _ computation) ->
                value (fun _kf_71 -> _kf_71 ())
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _choose_all_77 c =
  handler
    {
      value_clause = (fun _x_82 -> value [ _x_82 ]);
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Decide ->
              fun (_ : unit) (_k_78 : bool -> _ computation) ->
                _k_78 true >> fun _gen_bind_80 ->
                let _gen_bind_79 = run (_var_13 _gen_bind_80) in
                _k_78 false >> fun _gen_bind_81 -> _gen_bind_79 _gen_bind_81
          | Effect_Fail ->
              fun (_ : unit) (_ : unit -> _ computation) -> value []
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _queens_83 _number_of_queens_84 =
  let rec _place_85 (_x_86, _qs_87) =
    match run ((run (lift_binary ( > ) _x_86)) _number_of_queens_84) with
    | true -> value _qs_87
    | false ->
        _choose_59 (run (_available_44 (_number_of_queens_84, _x_86, _qs_87)))
        >> fun _y_90 ->
        _place_85
          (run ((run (lift_binary ( + ) _x_86)) 1), (_x_86, _y_90) :: _qs_87)
  in
  _place_85 (1, [])

let _queens_one_option_94 _number_of_queens_95 =
  let rec _place_17 (_x_14, _qs_13) =
    match run ((run (lift_binary ( > ) _x_14)) _number_of_queens_95) with
    | true -> value (Some _qs_13)
    | false ->
        let rec _choose_35 _gen_let_rec_function_60 =
          match _gen_let_rec_function_60 with
          | [] -> value None
          | _x_62 :: _xs_63 -> (
              match
                run
                  (_place_17
                     ( run ((run (lift_binary ( + ) _x_14)) 1),
                       (_x_14, _x_62) :: _qs_13 ))
              with
              | Some _x_70 -> value (Some _x_70)
              | None -> _choose_35 _xs_63)
        in
        _choose_35 (run (_available_44 (_number_of_queens_95, _x_14, _qs_13)))
  in
  _place_17 (1, [])

let _queens_one_cps_96 _number_of_queens_97 =
  let rec _place_86 (_x_83, _qs_82) =
    match run ((run (lift_binary ( > ) _x_83)) _number_of_queens_97) with
    | true -> value (fun _ -> value _qs_82)
    | false ->
        let rec _choose_112 _gen_let_rec_function_60 =
          match _gen_let_rec_function_60 with
          | [] -> value (fun _kf_132 -> _kf_132 ())
          | _x_62 :: _xs_63 ->
              value (fun _kf_159 ->
                  (run
                     (_place_86
                        ( run ((run (lift_binary ( + ) _x_83)) 1),
                          (_x_83, _x_62) :: _qs_82 ))) (fun () ->
                      (run (_choose_112 _xs_63)) _kf_159))
        in
        _choose_112 (run (_available_44 (_number_of_queens_97, _x_83, _qs_82)))
  in
  (run (_place_86 (1, []))) (fun () ->
      call Effect_Fail () (fun _result_73 -> _absurd_7 _result_73))

let _queens_all_100 _number_of_queens_101 =
  let rec _place_173 (_x_170, _qs_169) =
    match run ((run (lift_binary ( > ) _x_170)) _number_of_queens_101) with
    | true -> value [ _qs_169 ]
    | false ->
        let rec _choose_195 _gen_let_rec_function_60 =
          match _gen_let_rec_function_60 with
          | [] -> value []
          | _x_62 :: _xs_63 ->
              (run
                 (_var_13
                    (run
                       (_place_173
                          ( run ((run (lift_binary ( + ) _x_170)) 1),
                            (_x_170, _x_62) :: _qs_169 )))))
                (run (_choose_195 _xs_63))
        in
        _choose_195
          (run (_available_44 (_number_of_queens_101, _x_170, _qs_169)))
  in
  _place_173 (1, [])
