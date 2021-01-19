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
"End of pervasives"

let _var_1 = ( <> )

let _var_2 = ( < )

let _var_3 = ( > )

let _var_4 = ( - )

let _var_5 = ( + )

let _var_6 = ( ~- )

let _absurd_7 _void_8 = match _void_8 with _ -> assert false

let _abs_9 _x_10 =
  let _gen_bind_11 =
    let _gen_bind_12 = _var_2 _x_10 in
    _gen_bind_12 0
  in
  if _gen_bind_11 then _var_6 _x_10 else _x_10

let rec _var_13 _xs_14 _ys_15 =
  match _xs_14 with
  | [] -> _ys_15
  | _x_16 :: _xs_17 ->
      let _gen_bind_18 =
        let _gen_bind_19 = _var_13 _xs_17 in
        _gen_bind_19 _ys_15
      in
      _x_16 :: _gen_bind_18

let _no_attack_20 (_x_21, _y_22) (_x'_23, _y'_24) =
  let _gen_bind_25 =
    let _gen_bind_26 = _var_1 _x_21 in
    _gen_bind_26 _x'_23
  in
  if _gen_bind_25 then
    let _gen_bind_27 =
      let _gen_bind_28 = _var_1 _y_22 in
      _gen_bind_28 _y'_24
    in
    if _gen_bind_27 then
      let _gen_bind_29 =
        let _gen_bind_30 =
          let _gen_bind_31 =
            let _gen_bind_32 = _var_4 _x_21 in
            _gen_bind_32 _x'_23
          in
          _abs_9 _gen_bind_31
        in
        _var_1 _gen_bind_30
      in
      let _gen_bind_33 =
        let _gen_bind_34 =
          let _gen_bind_35 = _var_4 _y_22 in
          _gen_bind_35 _y'_24
        in
        _abs_9 _gen_bind_34
      in
      _gen_bind_29 _gen_bind_33
    else false
  else false

let rec _not_attacked_36 _x'_37 _gen_function_38 =
  match _gen_function_38 with
  | [] -> true
  | _x_39 :: _xs_40 ->
      let _gen_bind_41 =
        let _gen_bind_42 = _no_attack_20 _x'_37 in
        _gen_bind_42 _x_39
      in
      if _gen_bind_41 then
        let _gen_bind_43 = _not_attacked_36 _x'_37 in
        _gen_bind_43 _xs_40
      else false

let _available_44 (_number_of_queens_45, _x_46, _qs_47) =
  let rec _loop_48 (_possible_49, _y_50) =
    let _gen_bind_51 =
      let _gen_bind_52 = _var_2 _y_50 in
      _gen_bind_52 1
    in
    if _gen_bind_51 then _possible_49
    else
      let _gen_bind_53 =
        let _gen_bind_54 = _not_attacked_36 (_x_46, _y_50) in
        _gen_bind_54 _qs_47
      in
      if _gen_bind_53 then
        let _gen_bind_55 =
          let _gen_bind_56 = _var_4 _y_50 in
          _gen_bind_56 1
        in
        _loop_48 (_y_50 :: _possible_49, _gen_bind_55)
      else
        let _gen_bind_57 =
          let _gen_bind_58 = _var_4 _y_50 in
          _gen_bind_58 1
        in
        _loop_48 (_possible_49, _gen_bind_57)
  in
  _loop_48 ([], _number_of_queens_45)

type (_, _) effect += Effect_Decide : (unit, bool) effect

type (_, _) effect += Effect_Fail : (unit, unit) effect

type 't1 option = None | Some of 't1

let rec _choose_59 _gen_let_rec_function_60 =
  match _gen_let_rec_function_60 with
  | [] ->
      (effect Effect_Fail) () >> fun _gen_bind_61 ->
      value (match _gen_bind_61 with _ -> assert false)
  | _x_62 :: _xs_63 ->
      (effect Effect_Decide) () >> fun _gen_bind_64 ->
      if _gen_bind_64 then value _x_62 else _choose_59 _xs_63

let _optionalize_65 comp =
  handler
    {
      value_clause = (fun _y_69 -> value (Some _y_69));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) : (a -> (b -> _) -> _) ->
          match x with
          | Effect_Decide -> (
              fun (_ : unit) (_k_66 : bool -> _) ->
                _k_66 true >> fun _gen_bind_68 ->
                match _gen_bind_68 with
                | Some _x_67 -> value (Some _x_67)
                | None -> _k_66 false)
          | Effect_Fail -> fun (_ : unit) (_ : unit -> _) -> value None
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    comp

let _backtrack_70 comp =
  handler
    {
      value_clause =
        (fun _y_76 ->
          value (fun _lift_fun_1 -> value ((fun _ -> _y_76) _lift_fun_1)));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) : (a -> (b -> _) -> _) ->
          match x with
          | Effect_Decide ->
              fun (_ : unit) (_k_72 : bool -> _) ->
                value (fun _kf_73 ->
                    _k_72 true >> fun _gen_bind_74 ->
                    _gen_bind_74 (fun () ->
                        _k_72 false >> fun _gen_bind_75 -> _gen_bind_75 _kf_73))
          | Effect_Fail ->
              fun (_ : unit) (_ : unit -> _) -> value (fun _kf_71 -> _kf_71 ())
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    comp

let _choose_all_77 comp =
  handler
    {
      value_clause = (fun _x_82 -> value [ _x_82 ]);
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) : (a -> (b -> _) -> _) ->
          match x with
          | Effect_Decide ->
              fun (_ : unit) (_k_78 : bool -> _) ->
                (_k_78 true >> fun _gen_bind_80 -> value (_var_13 _gen_bind_80))
                >> fun _gen_bind_79 ->
                _k_78 false >> fun _gen_bind_81 ->
                value (_gen_bind_79 _gen_bind_81)
          | Effect_Fail -> fun (_ : unit) (_ : unit -> _) -> value []
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    comp

let _queens_83 _number_of_queens_84 =
  let rec _place_85 (_x_86, _qs_87) =
    let _gen_bind_88 =
      let _gen_bind_89 = _var_3 _x_86 in
      _gen_bind_89 _number_of_queens_84
    in
    if _gen_bind_88 then value _qs_87
    else
      (let _gen_bind_91 = _available_44 (_number_of_queens_84, _x_86, _qs_87) in
       _choose_59 _gen_bind_91)
      >> fun _y_90 ->
      let _gen_bind_92 =
        let _gen_bind_93 = _var_5 _x_86 in
        _gen_bind_93 1
      in
      _place_85 (_gen_bind_92, (_x_86, _y_90) :: _qs_87)
  in
  _place_85 (1, [])

let _queens_one_option_94 _number_of_queens_95 =
  _optionalize_65 (_queens_83 _number_of_queens_95)

let _queens_one_cps_96 _number_of_queens_97 =
  _backtrack_70 (_queens_83 _number_of_queens_97) >> fun _gen_bind_98 ->
  _gen_bind_98 (fun () ->
      (effect Effect_Fail) () >> fun _gen_bind_99 ->
      value (_absurd_7 _gen_bind_99))

let _queens_all_100 _number_of_queens_101 =
  _choose_all_77 (_queens_83 _number_of_queens_101)
