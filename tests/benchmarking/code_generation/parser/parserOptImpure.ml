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
      | _x_7 :: _xs_8 -> value (_x_7 :: run ((run (_var_4 _xs_8)) _ys_6)))

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
              | _ -> call Effect_Fail () (fun _result_3 -> _absurd_1 _result_3)));
      effect_clauses =
        (fun (type a b) (x : (a, b) effect) :
             (a -> (b -> _ computation) -> _ computation) ->
          match x with
          | Effect_Symbol ->
              fun (_c_14 : string) (_k_15 : string -> _ computation) ->
                value (fun _s_16 ->
                    match _s_16 with
                    | [] ->
                        call Effect_Fail () (fun _result_6 ->
                            _absurd_1 _result_6)
                    | _x_18 :: _xs_19 -> (
                        match run ((run (lift_binary ( = ) _c_14)) _x_18) with
                        | true ->
                            _k_15 _x_18 >> fun _gen_bind_22 ->
                            _gen_bind_22 _xs_19
                        | false ->
                            call Effect_Fail () (fun _result_9 ->
                                _absurd_1 _result_9)))
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
                _k_28 true >> fun _gen_bind_30 ->
                let _gen_bind_29 = run (_var_4 _gen_bind_30) in
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
  (run (lift_binary ( + ) (run ((run (lift_binary ( * ) _prev_36)) 10))))
    _num_37

let rec _parseNum_41 (_l_42, _v_43) =
  match _l_42 with
  | [] -> value _v_43
  | _x_44 :: _xs_45 -> (
      match _x_44 with
      | "0" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 0)))
      | "1" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 1)))
      | "2" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 2)))
      | "3" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 3)))
      | "4" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 4)))
      | "5" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 5)))
      | "6" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 6)))
      | "7" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 7)))
      | "8" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 8)))
      | "9" -> _parseNum_41 (_xs_45, run (_createNumber_35 (_v_43, 9))))

let rec _toNum_56 _l_57 = _parseNum_41 (_l_57, 0)

let _digit_58 () =
  let rec _checkNums_60 _n_61 =
    match _n_61 with
    | [] -> call Effect_Fail () (fun _result_12 -> _absurd_1 _result_12)
    | _x_63 :: _xs_64 ->
        call Effect_Decide () (fun _result_17 ->
            match _result_17 with
            | true ->
                call Effect_Symbol _x_63 (fun _result_14 -> value _result_14)
            | false -> _checkNums_60 _xs_64)
  in
  _checkNums_60 [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ]

let rec _many_66 _m_67 =
  call Effect_Decide () (fun _result_20 ->
      match _result_20 with true -> _m_67 () | false -> value [])

let rec _many1_69 () =
  _digit_58 () >> fun _x_70 ->
  _many_66 _many1_69 >> fun _xs_71 -> (run (_var_4 [ _x_70 ])) _xs_71

let rec _expr_73 () =
  let rec _term_74 () =
    let rec _factor_75 () =
      call Effect_Decide () (fun _result_41 ->
          match _result_41 with
          | true -> _many1_69 () >> fun _i_77 -> _toNum_56 _i_77
          | false ->
              call Effect_Symbol "(" (fun _result_38 ->
                  _expr_73 () >> fun _j_79 ->
                  call Effect_Symbol ")" (fun _result_35 -> value _j_79)))
    in
    call Effect_Decide () (fun _result_32 ->
        match _result_32 with
        | true ->
            _factor_75 () >> fun _i_82 ->
            call Effect_Symbol "*" (fun _result_29 ->
                _term_74 () >> fun _j_84 ->
                (run (lift_binary ( * ) _i_82)) _j_84)
        | false -> _factor_75 ())
  in
  call Effect_Decide () (fun _result_26 ->
      match _result_26 with
      | true ->
          _term_74 () >> fun _i_87 ->
          call Effect_Symbol "+" (fun _result_23 ->
              _expr_73 () >> fun _j_89 -> (run (lift_binary ( + ) _i_87)) _j_89)
      | false -> _term_74 ())

let _parseTest_91 () =
  _allsols_27
    ( (let rec _expr_53 () =
         let rec _term_74 () =
           let rec _factor_75 () =
             call Effect_Decide () (fun _result_74 ->
                 match _result_74 with
                 | true -> _many1_69 () >> fun _i_77 -> _toNum_56 _i_77
                 | false ->
                     call Effect_Symbol "(" (fun _result_71 ->
                         _expr_73 () >> fun _j_79 ->
                         call Effect_Symbol ")" (fun _result_68 -> value _j_79)))
           in
           call Effect_Decide () (fun _result_65 ->
               match _result_65 with
               | true ->
                   _factor_75 () >> fun _i_82 ->
                   call Effect_Symbol "*" (fun _result_62 ->
                       _term_74 () >> fun _j_84 ->
                       (run (lift_binary ( * ) _i_82)) _j_84)
               | false -> _factor_75 ())
         in
         call Effect_Decide () (fun _result_75 ->
             match _result_75 with
             | true ->
                 (fun c ->
                   handler
                     {
                       value_clause =
                         (fun _i_411 ->
                           value (fun _s_412 ->
                               match _s_412 with
                               | [] ->
                                   call Effect_Fail () (fun _result_413 ->
                                       _absurd_1 _result_413)
                               | _x_415 :: _xs_414 -> (
                                   match
                                     run ((run (lift_binary ( = ) "+")) _x_415)
                                   with
                                   | true ->
                                       let rec _new_special_var_416
                                           ((), _k_val_417) =
                                         let rec _term_418 () =
                                           let rec _factor_419 () =
                                             call Effect_Decide ()
                                               (fun _result_420 ->
                                                 match _result_420 with
                                                 | true ->
                                                     _many1_69 ()
                                                     >> fun _i_421 ->
                                                     _toNum_56 _i_421
                                                 | false ->
                                                     call Effect_Symbol "("
                                                       (fun _result_422 ->
                                                         _expr_73 ()
                                                         >> fun _j_423 ->
                                                         call Effect_Symbol ")"
                                                           (fun _result_424 ->
                                                             value _j_423)))
                                           in
                                           call Effect_Decide ()
                                             (fun _result_425 ->
                                               match _result_425 with
                                               | true ->
                                                   _factor_419 ()
                                                   >> fun _i_426 ->
                                                   call Effect_Symbol "*"
                                                     (fun _result_427 ->
                                                       _term_418 ()
                                                       >> fun _j_428 ->
                                                       (run
                                                          (lift_binary ( * )
                                                             _i_426))
                                                         _j_428)
                                               | false -> _factor_419 ())
                                         in
                                         call Effect_Decide ()
                                           (fun _result_429 ->
                                             match _result_429 with
                                             | true ->
                                                 (fun c ->
                                                   handler
                                                     {
                                                       value_clause =
                                                         (fun _i_430 ->
                                                           value (fun _s_431 ->
                                                               match _s_431 with
                                                               | [] ->
                                                                   call
                                                                     Effect_Fail
                                                                     ()
                                                                     (fun
                                                                       _result_432
                                                                     ->
                                                                       _absurd_1
                                                                         _result_432)
                                                               | _x_434
                                                                 :: _xs_433 -> (
                                                                   match
                                                                     run
                                                                       ((run
                                                                           (lift_binary
                                                                              ( = )
                                                                              "+"))
                                                                          _x_434)
                                                                   with
                                                                   | true ->
                                                                       (run
                                                                          (_new_special_var_416
                                                                             ( (),
                                                                               fun _j_435
                                                                                ->
                                                                                _k_val_417
                                                                                (
                                                                                run
                                                                                (
                                                                                (
                                                                                run
                                                                                (
                                                                                lift_binary
                                                                                ( + )
                                                                                _i_430))
                                                                                _j_435))
                                                                             )))
                                                                         _xs_433
                                                                   | false ->
                                                                       call
                                                                         Effect_Fail
                                                                         ()
                                                                         (fun
                                                                           _result_436
                                                                         ->
                                                                           _absurd_1
                                                                             _result_436)
                                                                   )));
                                                       effect_clauses =
                                                         (fun (type a b)
                                                              (x :
                                                                (a, b) effect) :
                                                              (a ->
                                                              (b ->
                                                              _ computation) ->
                                                              _ computation) ->
                                                           match x with
                                                           | Effect_Symbol ->
                                                               fun (_c_438 :
                                                                     string)
                                                                   (_k_437 :
                                                                     string ->
                                                                     _
                                                                     computation)
                                                                   ->
                                                                 value
                                                                   (fun _s_439
                                                                   ->
                                                                     match
                                                                       _s_439
                                                                     with
                                                                     | [] ->
                                                                         call
                                                                           Effect_Fail
                                                                           ()
                                                                           (fun
                                                                             _result_440
                                                                           ->
                                                                             _absurd_1
                                                                               _result_440)
                                                                     | _x_442
                                                                       :: _xs_441
                                                                       -> (
                                                                         match
                                                                           run
                                                                             ((run
                                                                                (
                                                                                lift_binary
                                                                                ( = )
                                                                                _c_438))
                                                                                _x_442)
                                                                         with
                                                                         | true
                                                                           ->
                                                                             _k_437
                                                                               _x_442
                                                                             >>
                                                                             fun 
                                                                               _gen_bind_443
                                                                               ->
                                                                             _gen_bind_443
                                                                               _xs_441
                                                                         | false
                                                                           ->
                                                                             call
                                                                               Effect_Fail
                                                                               ()
                                                                               (fun
                                                                                _result_444
                                                                               ->
                                                                                _absurd_1
                                                                                _result_444)
                                                                         ))
                                                           | eff' ->
                                                               fun arg k ->
                                                                 Call
                                                                   (eff', arg, k));
                                                     }
                                                     c)
                                                   (_term_418 ())
                                             | false ->
                                                 (fun c ->
                                                   handler
                                                     {
                                                       value_clause =
                                                         (fun _vcvar_445 ->
                                                           _k_val_417 _vcvar_445);
                                                       effect_clauses =
                                                         (fun (type a b)
                                                              (x :
                                                                (a, b) effect) :
                                                              (a ->
                                                              (b ->
                                                              _ computation) ->
                                                              _ computation) ->
                                                           match x with
                                                           | Effect_Symbol ->
                                                               fun (_c_447 :
                                                                     string)
                                                                   (_k_446 :
                                                                     string ->
                                                                     _
                                                                     computation)
                                                                   ->
                                                                 value
                                                                   (fun _s_448
                                                                   ->
                                                                     match
                                                                       _s_448
                                                                     with
                                                                     | [] ->
                                                                         call
                                                                           Effect_Fail
                                                                           ()
                                                                           (fun
                                                                             _result_449
                                                                           ->
                                                                             _absurd_1
                                                                               _result_449)
                                                                     | _x_451
                                                                       :: _xs_450
                                                                       -> (
                                                                         match
                                                                           run
                                                                             ((run
                                                                                (
                                                                                lift_binary
                                                                                ( = )
                                                                                _c_447))
                                                                                _x_451)
                                                                         with
                                                                         | true
                                                                           ->
                                                                             _k_446
                                                                               _x_451
                                                                             >>
                                                                             fun 
                                                                               _gen_bind_452
                                                                               ->
                                                                             _gen_bind_452
                                                                               _xs_450
                                                                         | false
                                                                           ->
                                                                             call
                                                                               Effect_Fail
                                                                               ()
                                                                               (fun
                                                                                _result_453
                                                                               ->
                                                                                _absurd_1
                                                                                _result_453)
                                                                         ))
                                                           | eff' ->
                                                               fun arg k ->
                                                                 Call
                                                                   (eff', arg, k));
                                                     }
                                                     c)
                                                   (_term_418 ()))
                                       in
                                       (run
                                          (_new_special_var_416
                                             ( (),
                                               fun _j_454 ->
                                                 let _y_455 =
                                                   run
                                                     ((run
                                                         (lift_binary ( + )
                                                            _i_411))
                                                        _j_454)
                                                 in
                                                 value (fun _s_456 ->
                                                     match _s_456 with
                                                     | [] -> value _y_455
                                                     | _ ->
                                                         call Effect_Fail ()
                                                           (fun _result_457 ->
                                                             _absurd_1
                                                               _result_457)) )))
                                         _xs_414
                                   | false ->
                                       call Effect_Fail () (fun _result_458 ->
                                           _absurd_1 _result_458))));
                       effect_clauses =
                         (fun (type a b) (x : (a, b) effect) :
                              (a -> (b -> _ computation) -> _ computation) ->
                           match x with
                           | Effect_Symbol ->
                               fun (_c_460 : string)
                                   (_k_459 : string -> _ computation) ->
                                 value (fun _s_461 ->
                                     match _s_461 with
                                     | [] ->
                                         call Effect_Fail () (fun _result_462 ->
                                             _absurd_1 _result_462)
                                     | _x_464 :: _xs_463 -> (
                                         match
                                           run
                                             ((run (lift_binary ( = ) _c_460))
                                                _x_464)
                                         with
                                         | true ->
                                             _k_459 _x_464
                                             >> fun _gen_bind_465 ->
                                             _gen_bind_465 _xs_463
                                         | false ->
                                             call Effect_Fail ()
                                               (fun _result_466 ->
                                                 _absurd_1 _result_466)))
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     c)
                   (_term_74 ())
             | false ->
                 (fun c ->
                   handler
                     {
                       value_clause =
                         (fun _y_467 ->
                           value (fun _s_468 ->
                               match _s_468 with
                               | [] -> value _y_467
                               | _ ->
                                   call Effect_Fail () (fun _result_469 ->
                                       _absurd_1 _result_469)));
                       effect_clauses =
                         (fun (type a b) (x : (a, b) effect) :
                              (a -> (b -> _ computation) -> _ computation) ->
                           match x with
                           | Effect_Symbol ->
                               fun (_c_471 : string)
                                   (_k_470 : string -> _ computation) ->
                                 value (fun _s_472 ->
                                     match _s_472 with
                                     | [] ->
                                         call Effect_Fail () (fun _result_473 ->
                                             _absurd_1 _result_473)
                                     | _x_475 :: _xs_474 -> (
                                         match
                                           run
                                             ((run (lift_binary ( = ) _c_471))
                                                _x_475)
                                         with
                                         | true ->
                                             _k_470 _x_475
                                             >> fun _gen_bind_476 ->
                                             _gen_bind_476 _xs_474
                                         | false ->
                                             call Effect_Fail ()
                                               (fun _result_477 ->
                                                 _absurd_1 _result_477)))
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     c)
                   (_term_74 ()))
       in
       _expr_53 ())
    >> fun _gen_bind_92 ->
      _gen_bind_92 [ "4"; "3"; "*"; "("; "3"; "+"; "3"; ")" ] )

let _x_93 = run (_parseTest_91 ())
