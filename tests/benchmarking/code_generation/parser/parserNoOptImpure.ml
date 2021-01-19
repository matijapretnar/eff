(*
=== GENERATED FROM parser.eff ===
commit SHA: 03cdc167bd82ae792396973571e61b43009cf73a
=== BEGIN SOURCE ===

let absurd void = match void with;;
external ( = ) : 'a -> 'a -> bool = "="
let rec (@) xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (xs @ ys)
external ( + ) : int -> int -> int = "+"
external ( * ) : int -> int -> int = "*"

(***********************************
*********** The Parser *************
***********************************)

(********************************
* Effects
********************************)

effect Symbol : string -> string;;
effect Fail : unit -> empty;;
effect Decide : unit -> bool

(********************************
* Handlers
********************************)

let parse = handler
    | val y -> (fun s ->
        begin match s with
        | [] -> y
        | _ -> (absurd (#Fail ()))
        end
    )
    | #Symbol c k ->
        fun s ->
        (begin match s with
            | [] -> (absurd (#Fail ()))
            | (x :: xs) -> if (c = x) then k x xs else (absurd (#Fail ()))
        end
        )
;;

let allsols = handler
  | val x -> [x]
  | #Decide _ k -> k true @ k false
  | #Fail _ _ -> []
;;

let backtrack = handler
    | #Decide _ k ->
        handle k true with
            | #Fail _ _ -> k false
;;
(********************************
* Parser :: string list to int
********************************)

let createNumber (prev, num) = prev * 10 + num;;

let rec parseNum (l, v) =
    begin match l with
    | [] -> v
    | (x :: xs) ->
        begin match x with
        | "0" -> parseNum (xs, (createNumber (v, 0)))
        | "1" -> parseNum (xs, (createNumber (v, 1)))
        | "2" -> parseNum (xs, (createNumber (v, 2)))
        | "3" -> parseNum (xs, (createNumber (v, 3)))
        | "4" -> parseNum (xs, (createNumber (v, 4)))
        | "5" -> parseNum (xs, (createNumber (v, 5)))
        | "6" -> parseNum (xs, (createNumber (v, 6)))
        | "7" -> parseNum (xs, (createNumber (v, 7)))
        | "8" -> parseNum (xs, (createNumber (v, 8)))
        | "9" -> parseNum (xs, (createNumber (v, 9)))
        end
    end
;;

let rec toNum l = parseNum (l, 0);;

(********************************
* Parser :: main
********************************)

let digit () =

        let nums = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] in
        let rec checkNums n =
            begin match n with
            | [] -> (absurd (#Fail ()))
            | (x :: xs) ->
                if (#Decide ()) then (#Symbol x) else (checkNums xs)
            end in
        checkNums nums
;;

let rec many m = if (#Decide ()) then (m ()) else ([]);;

let rec many1 () =
    let x = digit () in
    let xs = many many1 in
    [x] @ xs
;;

let rec expr () =
    let rec term () =
        let rec factor () =
            if (#Decide ()) then (
                let i = many1 () in
                (toNum i)
            ) else (
                let p = #Symbol "(" in
                let j = expr () in
                let p = #Symbol ")" in
                j
            )
        in
        if (#Decide ()) then (
            let i = factor () in
            let p = #Symbol "*" in
            let j = term () in
            i * j
        ) else (
            factor ()
        )
    in
    if (#Decide ()) then (
        let i = term () in
        let p = #Symbol "+" in
        let j = expr () in
        i + j
    ) else (
        term ()
    )
;;

(********************************
* Example
********************************)

let parseTest () =
    with allsols handle (with parse handle (
            expr ()
        )) ["4"; "3"; "*"; "("; "3"; "+"; "3"; ")"]
;;

let x = parseTest ()
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

let _absurd_1 _void_2 = match _void_2 with _ -> assert false

let _var_3 x = lift_binary ( = ) x

let rec _var_4 _xs_5 =
  value (fun _ys_6 ->
      match _xs_5 with
      | [] -> value _ys_6
      | _x_7 :: _xs_8 ->
          (_var_4 _xs_8 >> fun _gen_bind_10 -> _gen_bind_10 _ys_6)
          >> fun _gen_bind_9 -> value (_x_7 :: _gen_bind_9))

let _var_11 x = lift_binary ( + ) x

let _var_12 x = lift_binary ( * ) x

type (_, _) effect += Effect_Symbol : (string, string) effect

type (_, _) effect += Effect_Fail : (unit, unit) effect

type (_, _) effect += Effect_Decide : (unit, bool) effect

let _parse_13 c =
  handler
    {
      value_clause =
        (fun _y_24 ->
          value (fun _s_25 ->
              match _s_25 with
              | [] -> value _y_24
              | _ ->
                  (effect Effect_Fail) () >> fun _gen_bind_26 ->
                  _absurd_1 _gen_bind_26));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Symbol ->
              fun (_c_14 : string) (_k_15 : string -> _ computation) ->
                value (fun _s_16 ->
                    match _s_16 with
                    | [] ->
                        (effect Effect_Fail) () >> fun _gen_bind_17 ->
                        _absurd_1 _gen_bind_17
                    | _x_18 :: _xs_19 -> (
                        (_var_3 _c_14 >> fun _gen_bind_21 -> _gen_bind_21 _x_18)
                        >> fun _gen_bind_20 ->
                        match _gen_bind_20 with
                        | true ->
                            _k_15 _x_18 >> fun _gen_bind_22 ->
                            _gen_bind_22 _xs_19
                        | false ->
                            (effect Effect_Fail) () >> fun _gen_bind_23 ->
                            _absurd_1 _gen_bind_23))
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _allsols_27 c =
  handler
    {
      value_clause = (fun _x_32 -> value [ _x_32 ]);
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Decide ->
              fun (_ : unit) (_k_28 : bool -> _ computation) ->
                (_k_28 true >> fun _gen_bind_30 -> _var_4 _gen_bind_30)
                >> fun _gen_bind_29 ->
                _k_28 false >> fun _gen_bind_31 -> _gen_bind_29 _gen_bind_31
          | Effect_Fail ->
              fun (_ : unit) (_ : unit -> _ computation) -> value []
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _backtrack_33 c =
  handler
    {
      value_clause = (fun _gen_id_par_94 -> value _gen_id_par_94);
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Decide ->
              fun (_ : unit) (_k_34 : bool -> _ computation) ->
                (fun c ->
                  handler
                    {
                      value_clause =
                        (fun _gen_id_par_95 -> value _gen_id_par_95);
                      effect_clauses =
                        (fun (type a b) (x : (a, b) effect) :
                             (a -> (b -> _ computation) -> _ computation) ->
                          match x with
                          | Effect_Fail ->
                              fun (_ : unit) (_ : unit -> _ computation) ->
                                _k_34 false
                          | eff' -> fun arg k -> Call (eff', arg, k));
                    }
                    c)
                  (_k_34 true)
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    c

let _createNumber_35 (_prev_36, _num_37) =
  ( (_var_12 _prev_36 >> fun _gen_bind_40 -> _gen_bind_40 10)
  >> fun _gen_bind_39 -> _var_11 _gen_bind_39 )
  >> fun _gen_bind_38 -> _gen_bind_38 _num_37

let rec _parseNum_41 (_l_42, _v_43) =
  match _l_42 with
  | [] -> value _v_43
  | _x_44 :: _xs_45 -> (
      match _x_44 with
      | "0" ->
          _createNumber_35 (_v_43, 0) >> fun _gen_bind_46 ->
          _parseNum_41 (_xs_45, _gen_bind_46)
      | "1" ->
          _createNumber_35 (_v_43, 1) >> fun _gen_bind_47 ->
          _parseNum_41 (_xs_45, _gen_bind_47)
      | "2" ->
          _createNumber_35 (_v_43, 2) >> fun _gen_bind_48 ->
          _parseNum_41 (_xs_45, _gen_bind_48)
      | "3" ->
          _createNumber_35 (_v_43, 3) >> fun _gen_bind_49 ->
          _parseNum_41 (_xs_45, _gen_bind_49)
      | "4" ->
          _createNumber_35 (_v_43, 4) >> fun _gen_bind_50 ->
          _parseNum_41 (_xs_45, _gen_bind_50)
      | "5" ->
          _createNumber_35 (_v_43, 5) >> fun _gen_bind_51 ->
          _parseNum_41 (_xs_45, _gen_bind_51)
      | "6" ->
          _createNumber_35 (_v_43, 6) >> fun _gen_bind_52 ->
          _parseNum_41 (_xs_45, _gen_bind_52)
      | "7" ->
          _createNumber_35 (_v_43, 7) >> fun _gen_bind_53 ->
          _parseNum_41 (_xs_45, _gen_bind_53)
      | "8" ->
          _createNumber_35 (_v_43, 8) >> fun _gen_bind_54 ->
          _parseNum_41 (_xs_45, _gen_bind_54)
      | "9" ->
          _createNumber_35 (_v_43, 9) >> fun _gen_bind_55 ->
          _parseNum_41 (_xs_45, _gen_bind_55))

let rec _toNum_56 _l_57 = _parseNum_41 (_l_57, 0)

let _digit_58 () =
  let _nums_59 = [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ] in
  let rec _checkNums_60 _n_61 =
    match _n_61 with
    | [] ->
        (effect Effect_Fail) () >> fun _gen_bind_62 -> _absurd_1 _gen_bind_62
    | _x_63 :: _xs_64 -> (
        (effect Effect_Decide) () >> fun _gen_bind_65 ->
        match _gen_bind_65 with
        | true -> (effect Effect_Symbol) _x_63
        | false -> _checkNums_60 _xs_64)
  in
  _checkNums_60 _nums_59

let rec _many_66 _m_67 =
  (effect Effect_Decide) () >> fun _gen_bind_68 ->
  match _gen_bind_68 with true -> _m_67 () | false -> value []

let rec _many1_69 () =
  _digit_58 () >> fun _x_70 ->
  _many_66 _many1_69 >> fun _xs_71 ->
  _var_4 [ _x_70 ] >> fun _gen_bind_72 -> _gen_bind_72 _xs_71

let rec _expr_73 () =
  let rec _term_74 () =
    let rec _factor_75 () =
      (effect Effect_Decide) () >> fun _gen_bind_76 ->
      match _gen_bind_76 with
      | true -> _many1_69 () >> fun _i_77 -> _toNum_56 _i_77
      | false ->
          (effect Effect_Symbol) "(" >> fun _p_78 ->
          _expr_73 () >> fun _j_79 ->
          (effect Effect_Symbol) ")" >> fun _p_80 -> value _j_79
    in
    (effect Effect_Decide) () >> fun _gen_bind_81 ->
    match _gen_bind_81 with
    | true ->
        _factor_75 () >> fun _i_82 ->
        (effect Effect_Symbol) "*" >> fun _p_83 ->
        _term_74 () >> fun _j_84 ->
        _var_12 _i_82 >> fun _gen_bind_85 -> _gen_bind_85 _j_84
    | false -> _factor_75 ()
  in
  (effect Effect_Decide) () >> fun _gen_bind_86 ->
  match _gen_bind_86 with
  | true ->
      _term_74 () >> fun _i_87 ->
      (effect Effect_Symbol) "+" >> fun _p_88 ->
      _expr_73 () >> fun _j_89 ->
      _var_11 _i_87 >> fun _gen_bind_90 -> _gen_bind_90 _j_89
  | false -> _term_74 ()

let _parseTest_91 () =
  _allsols_27
    ( _parse_13 (_expr_73 ()) >> fun _gen_bind_92 ->
      _gen_bind_92 [ "4"; "3"; "*"; "("; "3"; "+"; "3"; ")" ] )

let _x_93 = run (_parseTest_91 ())
