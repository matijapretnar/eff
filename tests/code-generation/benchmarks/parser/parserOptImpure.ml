(*
=== GENERATED FROM parser.eff ===
commit SHA: 0a8185f252df28fb2b1a33ec39799392a1190567
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

effect Symbol : string -> unit -> string;;
effect Fail : unit -> empty;;
effect Decide : unit -> bool

(********************************
* Handlers
********************************)

let parse = handler
    | val y -> (fun s ->
        begin match s with
        | [] -> y
        | _ -> absurd (#Fail ())
        end
    )
    | #Symbol c k ->
        fun s ->
        (begin match s with
            | [] -> k (fun () -> (absurd (#Fail ()))) []
            | (x :: xs) -> if (c = x) then k (fun () -> x) xs else k (fun () -> (absurd (#Fail ()))) s
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
    with backtrack handle (
        let nums = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] in
        let rec checkNums n =
            begin match n with
            | [] -> (absurd (#Fail ()))
            | (x :: xs) ->
                if (#Decide ()) then (#Symbol x ()) else (checkNums xs)
            end in
        checkNums nums
    )
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
                let p = #Symbol "(" () in
                let j = expr () in
                let p = #Symbol ")" () in
                j
            )
        in
        if (#Decide ()) then (
            let i = factor () in
            let p = #Symbol "*" () in
            let j = term () in
            i * j
        ) else (
            factor ()
        )
    in
    if (#Decide ()) then (
        let i = term () in
        let p = #Symbol "+" () in
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
    with allsols handle (
        (with parse handle (
            expr ()
        )) ["4"; "3"; "*"; "("; "3"; "+"; "3"; ")"]
    )
;;

=== END SOURCE ===
*)

type ('eff_arg,'eff_res) effect = ..
type 'a computation =
  | Value: 'a -> 'a computation 
  | Call: ('eff_arg,'eff_res) effect* 'eff_arg* ('eff_res -> 'a computation)
  -> 'a computation 
type ('eff_arg,'eff_res,'b) effect_clauses =
  ('eff_arg,'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b
type ('a,'b) handler_clauses =
  {
  value_clause: 'a -> 'b ;
  effect_clauses: 'eff_arg 'eff_res . ('eff_arg,'eff_res,'b) effect_clauses }
let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> (k y) >> f))) 
let rec handler (h : ('a,'b) handler_clauses) =
  (let rec handler =
     function
     | Value x -> h.value_clause x
     | Call (eff,arg,k) ->
         let clause = h.effect_clauses eff  in
         clause arg (fun y  -> handler (k y))
      in
   handler : 'a computation -> 'b)
  
let value (x : 'a) = (Value x : 'a computation) 
let call (eff : ('a,'b) effect) (arg : 'a) (cont : 'b -> 'c computation) =
  (Call (eff, arg, cont) : 'c computation) 
let rec lift (f : 'a -> 'b) =
  (function
   | Value x -> Value (f x)
   | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> lift f (k y)))) : 
  'a computation -> 'b computation) 
let effect eff arg = call eff arg value 
let run =
  function | Value x -> x | Call (eff,_,_) -> failwith "Uncaught effect" 
let ( ** ) =
  let rec pow a =
    let open Pervasives in
      function
      | 0 -> 1
      | 1 -> a
      | n ->
          let b = pow a (n / 2)  in
          (b * b) * (if (n mod 2) = 0 then 1 else a)
     in
  pow 
let string_length _ = assert false 
let to_string _ = assert false 
let lift_unary f x = value (f x) 
let lift_binary f x = value (fun y  -> value (f x y)) 
;;value "End of pervasives"
let _absurd_1 _void_2 = match _void_2 with | _ -> assert false 
let _var_3 x = lift_binary (=) x 
let rec _var_4 _xs_5 =
  value
    (fun _ys_6  ->
       match _xs_5 with
       | [] -> value _ys_6
       | _x_7::_xs_8 -> value (_x_7 :: (run ((run (_var_4 _xs_8)) _ys_6))))
  
let _var_11 x = lift_binary (+) x 
let _var_12 x = lift_binary ( * ) x 
type (_,_) effect +=
  | Effect_Symbol: (string,unit -> string computation) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
let _parse_13 c =
  handler
    {
      value_clause =
        (fun _y_26  ->
           value
             (fun _s_27  ->
                match _s_27 with
                | [] -> value _y_26
                | _ ->
                    call Effect_Fail ()
                      (fun _result_3  -> _absurd_1 _result_3)));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Symbol  ->
               (fun (_c_14 : string)  ->
                  fun (_k_15 : (unit -> string computation) -> _ computation)
                     ->
                    value
                      (fun _s_16  ->
                         match _s_16 with
                         | [] ->
                             (run
                                (_k_15
                                   (fun ()  ->
                                      call Effect_Fail ()
                                        (fun _result_6  ->
                                           _absurd_1 _result_6)))) []
                         | _x_19::_xs_20 ->
                             (match run ((run (lift_binary (=) _c_14)) _x_19)
                              with
                              | true  ->
                                  (run (_k_15 (fun ()  -> value _x_19)))
                                    _xs_20
                              | false  ->
                                  (run
                                     (_k_15
                                        (fun ()  ->
                                           call Effect_Fail ()
                                             (fun _result_9  ->
                                                _absurd_1 _result_9)))) _s_16)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _allsols_29 c =
  handler
    {
      value_clause = (fun _x_34  -> value [_x_34]);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_30 : bool -> _ computation)  ->
                    (_k_30 true) >>
                      (fun _gen_bind_32  ->
                         let _gen_bind_31 = run (_var_4 _gen_bind_32)  in
                         (_k_30 false) >>
                           (fun _gen_bind_33  -> _gen_bind_31 _gen_bind_33)))
           | Effect_Fail  ->
               (fun (_ : unit)  ->
                  fun (_ : unit -> _ computation)  -> value [])
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _backtrack_35 c =
  handler
    {
      value_clause = (fun _gen_id_par_100  -> value _gen_id_par_100);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_36 : bool -> _ computation)  ->
                    value (run (_k_36 true)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _createNumber_37 (_prev_38,_num_39) =
  (run (lift_binary (+) (run ((run (lift_binary ( * ) _prev_38)) 10))))
    _num_39
  
let rec _parseNum_43 (_l_44,_v_45) =
  match _l_44 with
  | [] -> value _v_45
  | _x_46::_xs_47 ->
      (match _x_46 with
       | "0" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 0))))
       | "1" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 1))))
       | "2" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 2))))
       | "3" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 3))))
       | "4" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 4))))
       | "5" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 5))))
       | "6" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 6))))
       | "7" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 7))))
       | "8" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 8))))
       | "9" -> _parseNum_43 (_xs_47, (run (_createNumber_37 (_v_45, 9)))))
  
let rec _toNum_58 _l_59 = _parseNum_43 (_l_59, 0) 
let _digit_60 () =
  let rec _checkNums_62 _n_63 =
    match _n_63 with
    | [] -> call Effect_Fail () (fun _result_12  -> _absurd_1 _result_12)
    | _x_65::_xs_66 ->
        call Effect_Decide ()
          (fun _result_18  ->
             match _result_18 with
             | true  ->
                 call Effect_Symbol _x_65 (fun _result_15  -> _result_15 ())
             | false  -> _checkNums_62 _xs_66)
     in
  let rec _newvar_21 _n_63 =
    match _n_63 with
    | [] ->
        call Effect_Fail ()
          (fun _result_24  -> value (run (_absurd_1 _result_24)))
    | _x_65::_xs_66 ->
        value
          (run
             (call Effect_Symbol _x_65
                (fun _result_33  -> value (run (_result_33 ())))))
     in
  _newvar_21 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] 
let rec _many_69 _m_70 =
  call Effect_Decide ()
    (fun _result_41  ->
       match _result_41 with | true  -> _m_70 () | false  -> value [])
  
let rec _many1_72 () =
  (_digit_60 ()) >>
    (fun _x_73  ->
       (_many_69 _many1_72) >> (fun _xs_74  -> (run (_var_4 [_x_73])) _xs_74))
  
let rec _expr_76 () =
  let rec _term_77 () =
    let rec _factor_78 () =
      call Effect_Decide ()
        (fun _result_66  ->
           match _result_66 with
           | true  -> (_many1_72 ()) >> ((fun _i_80  -> _toNum_58 _i_80))
           | false  ->
               call Effect_Symbol "("
                 (fun _result_63  ->
                    (_expr_76 ()) >>
                      (fun _j_83  ->
                         call Effect_Symbol ")"
                           (fun _result_59  -> value _j_83))))
       in
    call Effect_Decide ()
      (fun _result_55  ->
         match _result_55 with
         | true  ->
             (_factor_78 ()) >>
               ((fun _i_87  ->
                   call Effect_Symbol "*"
                     (fun _result_52  ->
                        (_term_77 ()) >>
                          (fun _j_90  ->
                             (run (lift_binary ( * ) _i_87)) _j_90))))
         | false  -> _factor_78 ())
     in
  call Effect_Decide ()
    (fun _result_48  ->
       match _result_48 with
       | true  ->
           (_term_77 ()) >>
             ((fun _i_93  ->
                 call Effect_Symbol "+"
                   (fun _result_45  ->
                      (_expr_76 ()) >>
                        (fun _j_96  -> (run (lift_binary (+) _i_93)) _j_96))))
       | false  -> _term_77 ())
  
let _parseTest_98 () =
  let rec _newvar_283 () =
    let rec _term_284 () =
      let rec _factor_285 () =
        call Effect_Decide ()
          (fun _result_286  ->
             match _result_286 with
             | true  -> (_many1_72 ()) >> ((fun _i_287  -> _toNum_58 _i_287))
             | false  ->
                 call Effect_Symbol "("
                   (fun _result_288  ->
                      (_expr_76 ()) >>
                        (fun _j_289  ->
                           call Effect_Symbol ")"
                             (fun _result_290  -> value _j_289))))
         in
      call Effect_Decide ()
        (fun _result_291  ->
           match _result_291 with
           | true  ->
               (_factor_285 ()) >>
                 ((fun _i_292  ->
                     call Effect_Symbol "*"
                       (fun _result_293  ->
                          (_term_284 ()) >>
                            (fun _j_294  ->
                               (run (lift_binary ( * ) _i_292)) _j_294))))
           | false  -> _factor_285 ())
       in
    call Effect_Decide ()
      (fun _result_295  ->
         match _result_295 with
         | true  ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _i_296  ->
                          value
                            (fun _s_297  ->
                               match _s_297 with
                               | [] ->
                                   (run
                                      ((fun c  ->
                                          handler
                                            {
                                              value_clause =
                                                (fun _j_298  ->
                                                   let _y_299 =
                                                     run
                                                       ((run
                                                           (lift_binary (+)
                                                              _i_296)) _j_298)
                                                      in
                                                   value
                                                     (fun _s_300  ->
                                                        match _s_300 with
                                                        | [] -> value _y_299
                                                        | _ ->
                                                            call Effect_Fail
                                                              ()
                                                              (fun
                                                                 _result_301 
                                                                 ->
                                                                 _absurd_1
                                                                   _result_301)));
                                              effect_clauses = fun (type a)
                                                -> fun (type b) ->
                                                fun (x : (a,b) effect)  ->
                                                  (match x with
                                                   | Effect_Symbol  ->
                                                       (fun (_c_303 : string)
                                                           ->
                                                          fun
                                                            (_k_302 :
                                                              (unit ->
                                                                 string
                                                                   computation)
                                                                ->
                                                                _ computation)
                                                             ->
                                                            value
                                                              (fun _s_304  ->
                                                                 match _s_304
                                                                 with
                                                                 | [] ->
                                                                    (run
                                                                    (_k_302
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_305
                                                                     ->
                                                                    _absurd_1
                                                                    _result_305))))
                                                                    []
                                                                 | _x_307::_xs_306
                                                                    ->
                                                                    (match 
                                                                    run
                                                                    ((run
                                                                    (lift_binary
                                                                    (=)
                                                                    _c_303))
                                                                    _x_307)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    (run
                                                                    (_k_302
                                                                    (fun () 
                                                                    ->
                                                                    value
                                                                    _x_307)))
                                                                    _xs_306
                                                                    | 
                                                                    false  ->
                                                                    (run
                                                                    (_k_302
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_308
                                                                     ->
                                                                    _absurd_1
                                                                    _result_308))))
                                                                    _s_304)))
                                                   | eff' ->
                                                       (fun arg  ->
                                                          fun k  ->
                                                            Call
                                                              (eff', arg, k)) : 
                                                  a ->
                                                    (b -> _ computation) ->
                                                      _ computation)
                                            } c) (_expr_76 ()))) []
                               | _x_310::_xs_309 ->
                                   (match run
                                            ((run (lift_binary (=) "+"))
                                               _x_310)
                                    with
                                    | true  ->
                                        (run
                                           ((fun c  ->
                                               handler
                                                 {
                                                   value_clause =
                                                     (fun _j_311  ->
                                                        let _y_312 =
                                                          run
                                                            ((run
                                                                (lift_binary
                                                                   (+) _i_296))
                                                               _j_311)
                                                           in
                                                        value
                                                          (fun _s_313  ->
                                                             match _s_313
                                                             with
                                                             | [] ->
                                                                 value _y_312
                                                             | _ ->
                                                                 call
                                                                   Effect_Fail
                                                                   ()
                                                                   (fun
                                                                    _result_314
                                                                     ->
                                                                    _absurd_1
                                                                    _result_314)));
                                                   effect_clauses = fun (type
                                                     a) -> fun (type b) ->
                                                     fun (x : (a,b) effect) 
                                                       ->
                                                       (match x with
                                                        | Effect_Symbol  ->
                                                            (fun
                                                               (_c_316 :
                                                                 string)
                                                                ->
                                                               fun
                                                                 (_k_315 :
                                                                   (unit ->
                                                                    string
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
                                                                  ->
                                                                 value
                                                                   (fun
                                                                    _s_317 
                                                                    ->
                                                                    match _s_317
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (run
                                                                    (_k_315
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_318
                                                                     ->
                                                                    _absurd_1
                                                                    _result_318))))
                                                                    []
                                                                    | 
                                                                    _x_320::_xs_319
                                                                    ->
                                                                    (match 
                                                                    run
                                                                    ((run
                                                                    (lift_binary
                                                                    (=)
                                                                    _c_316))
                                                                    _x_320)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    (run
                                                                    (_k_315
                                                                    (fun () 
                                                                    ->
                                                                    value
                                                                    _x_320)))
                                                                    _xs_319
                                                                    | 
                                                                    false  ->
                                                                    (run
                                                                    (_k_315
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_321
                                                                     ->
                                                                    _absurd_1
                                                                    _result_321))))
                                                                    _s_317)))
                                                        | eff' ->
                                                            (fun arg  ->
                                                               fun k  ->
                                                                 Call
                                                                   (eff',
                                                                    arg, k)) : 
                                                       a ->
                                                         (b -> _ computation)
                                                           -> _ computation)
                                                 } c) (_expr_76 ()))) _xs_309
                                    | false  ->
                                        (run
                                           ((fun c  ->
                                               handler
                                                 {
                                                   value_clause =
                                                     (fun _j_322  ->
                                                        let _y_323 =
                                                          run
                                                            ((run
                                                                (lift_binary
                                                                   (+) _i_296))
                                                               _j_322)
                                                           in
                                                        value
                                                          (fun _s_324  ->
                                                             match _s_324
                                                             with
                                                             | [] ->
                                                                 value _y_323
                                                             | _ ->
                                                                 call
                                                                   Effect_Fail
                                                                   ()
                                                                   (fun
                                                                    _result_325
                                                                     ->
                                                                    _absurd_1
                                                                    _result_325)));
                                                   effect_clauses = fun (type
                                                     a) -> fun (type b) ->
                                                     fun (x : (a,b) effect) 
                                                       ->
                                                       (match x with
                                                        | Effect_Symbol  ->
                                                            (fun
                                                               (_c_327 :
                                                                 string)
                                                                ->
                                                               fun
                                                                 (_k_326 :
                                                                   (unit ->
                                                                    string
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
                                                                  ->
                                                                 value
                                                                   (fun
                                                                    _s_328 
                                                                    ->
                                                                    match _s_328
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (run
                                                                    (_k_326
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_329
                                                                     ->
                                                                    _absurd_1
                                                                    _result_329))))
                                                                    []
                                                                    | 
                                                                    _x_331::_xs_330
                                                                    ->
                                                                    (match 
                                                                    run
                                                                    ((run
                                                                    (lift_binary
                                                                    (=)
                                                                    _c_327))
                                                                    _x_331)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    (run
                                                                    (_k_326
                                                                    (fun () 
                                                                    ->
                                                                    value
                                                                    _x_331)))
                                                                    _xs_330
                                                                    | 
                                                                    false  ->
                                                                    (run
                                                                    (_k_326
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_332
                                                                     ->
                                                                    _absurd_1
                                                                    _result_332))))
                                                                    _s_328)))
                                                        | eff' ->
                                                            (fun arg  ->
                                                               fun k  ->
                                                                 Call
                                                                   (eff',
                                                                    arg, k)) : 
                                                       a ->
                                                         (b -> _ computation)
                                                           -> _ computation)
                                                 } c) (_expr_76 ()))) _s_297)));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_Symbol  ->
                              (fun (_c_334 : string)  ->
                                 fun
                                   (_k_333 :
                                     (unit -> string computation) ->
                                       _ computation)
                                    ->
                                   value
                                     (fun _s_335  ->
                                        match _s_335 with
                                        | [] ->
                                            (run
                                               (_k_333
                                                  (fun ()  ->
                                                     call Effect_Fail ()
                                                       (fun _result_336  ->
                                                          _absurd_1
                                                            _result_336))))
                                              []
                                        | _x_338::_xs_337 ->
                                            (match run
                                                     ((run
                                                         (lift_binary (=)
                                                            _c_334)) _x_338)
                                             with
                                             | true  ->
                                                 (run
                                                    (_k_333
                                                       (fun ()  ->
                                                          value _x_338)))
                                                   _xs_337
                                             | false  ->
                                                 (run
                                                    (_k_333
                                                       (fun ()  ->
                                                          call Effect_Fail ()
                                                            (fun _result_339 
                                                               ->
                                                               _absurd_1
                                                                 _result_339))))
                                                   _s_335)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_term_284 ())
         | false  ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_340  ->
                          value
                            (fun _s_341  ->
                               match _s_341 with
                               | [] -> value _y_340
                               | _ ->
                                   call Effect_Fail ()
                                     (fun _result_342  ->
                                        _absurd_1 _result_342)));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_Symbol  ->
                              (fun (_c_344 : string)  ->
                                 fun
                                   (_k_343 :
                                     (unit -> string computation) ->
                                       _ computation)
                                    ->
                                   value
                                     (fun _s_345  ->
                                        match _s_345 with
                                        | [] ->
                                            (run
                                               (_k_343
                                                  (fun ()  ->
                                                     call Effect_Fail ()
                                                       (fun _result_346  ->
                                                          _absurd_1
                                                            _result_346))))
                                              []
                                        | _x_348::_xs_347 ->
                                            (match run
                                                     ((run
                                                         (lift_binary (=)
                                                            _c_344)) _x_348)
                                             with
                                             | true  ->
                                                 (run
                                                    (_k_343
                                                       (fun ()  ->
                                                          value _x_348)))
                                                   _xs_347
                                             | false  ->
                                                 (run
                                                    (_k_343
                                                       (fun ()  ->
                                                          call Effect_Fail ()
                                                            (fun _result_349 
                                                               ->
                                                               _absurd_1
                                                                 _result_349))))
                                                   _s_345)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_term_284 ()))
     in
  let rec _newvar_360 () =
    (fun c  ->
       handler
         {
           value_clause =
             (fun _gen_bind_350  ->
                (fun c  ->
                   handler
                     {
                       value_clause = (fun _x_351  -> value [_x_351]);
                       effect_clauses = fun (type a) -> fun (type b) ->
                         fun (x : (a,b) effect)  ->
                           (match x with
                            | Effect_Decide  ->
                                (fun (_ : unit)  ->
                                   fun (_k_352 : bool -> _ computation)  ->
                                     (_k_352 true) >>
                                       (fun _gen_bind_353  ->
                                          let _gen_bind_354 =
                                            run (_var_4 _gen_bind_353)  in
                                          (_k_352 false) >>
                                            (fun _gen_bind_355  ->
                                               _gen_bind_354 _gen_bind_355)))
                            | Effect_Fail  ->
                                (fun (_ : unit)  ->
                                   fun (_ : unit -> _ computation)  ->
                                     value [])
                            | eff' ->
                                (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                           a -> (b -> _ computation) -> _ computation)
                     } c)
                  (_gen_bind_350 ["4"; "3"; "*"; "("; "3"; "+"; "3"; ")"]));
           effect_clauses = fun (type a) -> fun (type b) ->
             fun (x : (a,b) effect)  ->
               (match x with
                | Effect_Decide  ->
                    (fun (_ : unit)  ->
                       fun (_k_356 : bool -> _ computation)  ->
                         (_k_356 true) >>
                           (fun _gen_bind_357  ->
                              let _gen_bind_358 = run (_var_4 _gen_bind_357)
                                 in
                              (_k_356 false) >>
                                (fun _gen_bind_359  ->
                                   _gen_bind_358 _gen_bind_359)))
                | Effect_Fail  ->
                    (fun (_ : unit)  ->
                       fun (_ : unit -> _ computation)  -> value [])
                | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
               a -> (b -> _ computation) -> _ computation)
         } c)
      (let rec _term_284 () =
         let rec _factor_285 () =
           call Effect_Decide ()
             (fun _result_286  ->
                match _result_286 with
                | true  ->
                    (_many1_72 ()) >> ((fun _i_287  -> _toNum_58 _i_287))
                | false  ->
                    call Effect_Symbol "("
                      (fun _result_288  ->
                         (_expr_76 ()) >>
                           (fun _j_289  ->
                              call Effect_Symbol ")"
                                (fun _result_290  -> value _j_289))))
            in
         call Effect_Decide ()
           (fun _result_291  ->
              match _result_291 with
              | true  ->
                  (_factor_285 ()) >>
                    ((fun _i_292  ->
                        call Effect_Symbol "*"
                          (fun _result_293  ->
                             (_term_284 ()) >>
                               (fun _j_294  ->
                                  (run (lift_binary ( * ) _i_292)) _j_294))))
              | false  -> _factor_285 ())
          in
       call Effect_Decide ()
         (fun _result_295  ->
            match _result_295 with
            | true  ->
                ((fun c  ->
                    handler
                      {
                        value_clause =
                          (fun _i_296  ->
                             value
                               (fun _s_297  ->
                                  match _s_297 with
                                  | [] ->
                                      (run
                                         (let rec _newvar_361 () =
                                            let rec _term_77 () =
                                              let rec _factor_78 () =
                                                call Effect_Decide ()
                                                  (fun _result_386  ->
                                                     match _result_386 with
                                                     | true  ->
                                                         (_many1_72 ()) >>
                                                           ((fun _i_80  ->
                                                               _toNum_58
                                                                 _i_80))
                                                     | false  ->
                                                         call Effect_Symbol
                                                           "("
                                                           (fun _result_383 
                                                              ->
                                                              (_expr_76 ())
                                                                >>
                                                                (fun _j_83 
                                                                   ->
                                                                   call
                                                                    Effect_Symbol
                                                                    ")"
                                                                    (fun
                                                                    _result_379
                                                                     ->
                                                                    value
                                                                    _j_83))))
                                                 in
                                              call Effect_Decide ()
                                                (fun _result_375  ->
                                                   match _result_375 with
                                                   | true  ->
                                                       (_factor_78 ()) >>
                                                         ((fun _i_87  ->
                                                             call
                                                               Effect_Symbol
                                                               "*"
                                                               (fun
                                                                  _result_372
                                                                   ->
                                                                  (_term_77
                                                                    ()) >>
                                                                    (
                                                                    fun _j_90
                                                                     ->
                                                                    (run
                                                                    (lift_binary
                                                                    ( * )
                                                                    _i_87))
                                                                    _j_90))))
                                                   | false  -> _factor_78 ())
                                               in
                                            (fun c  ->
                                               handler
                                                 {
                                                   value_clause =
                                                     (fun _j_298  ->
                                                        let _y_299 =
                                                          run
                                                            ((run
                                                                (lift_binary
                                                                   (+) _i_296))
                                                               _j_298)
                                                           in
                                                        value
                                                          (fun _s_300  ->
                                                             match _s_300
                                                             with
                                                             | [] ->
                                                                 value _y_299
                                                             | _ ->
                                                                 call
                                                                   Effect_Fail
                                                                   ()
                                                                   (fun
                                                                    _result_301
                                                                     ->
                                                                    _absurd_1
                                                                    _result_301)));
                                                   effect_clauses = fun (type
                                                     a) -> fun (type b) ->
                                                     fun (x : (a,b) effect) 
                                                       ->
                                                       (match x with
                                                        | Effect_Symbol  ->
                                                            (fun
                                                               (_c_303 :
                                                                 string)
                                                                ->
                                                               fun
                                                                 (_k_302 :
                                                                   (unit ->
                                                                    string
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
                                                                  ->
                                                                 value
                                                                   (fun
                                                                    _s_304 
                                                                    ->
                                                                    match _s_304
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (run
                                                                    (_k_302
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_305
                                                                     ->
                                                                    _absurd_1
                                                                    _result_305))))
                                                                    []
                                                                    | 
                                                                    _x_307::_xs_306
                                                                    ->
                                                                    (match 
                                                                    run
                                                                    ((run
                                                                    (lift_binary
                                                                    (=)
                                                                    _c_303))
                                                                    _x_307)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    (run
                                                                    (_k_302
                                                                    (fun () 
                                                                    ->
                                                                    value
                                                                    _x_307)))
                                                                    _xs_306
                                                                    | 
                                                                    false  ->
                                                                    (run
                                                                    (_k_302
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_308
                                                                     ->
                                                                    _absurd_1
                                                                    _result_308))))
                                                                    _s_304)))
                                                        | eff' ->
                                                            (fun arg  ->
                                                               fun k  ->
                                                                 Call
                                                                   (eff',
                                                                    arg, k)) : 
                                                       a ->
                                                         (b -> _ computation)
                                                           -> _ computation)
                                                 } c)
                                              (call Effect_Decide ()
                                                 (fun _result_368  ->
                                                    match _result_368 with
                                                    | true  ->
                                                        (_term_77 ()) >>
                                                          ((fun _i_93  ->
                                                              call
                                                                Effect_Symbol
                                                                "+"
                                                                (fun
                                                                   _result_365
                                                                    ->
                                                                   (_expr_76
                                                                    ()) >>
                                                                    (fun
                                                                    _j_96  ->
                                                                    (run
                                                                    (lift_binary
                                                                    (+) _i_93))
                                                                    _j_96))))
                                                    | false  -> _term_77 ()))
                                             in
                                          _newvar_361 ())) []
                                  | _x_310::_xs_309 ->
                                      (match run
                                               ((run (lift_binary (=) "+"))
                                                  _x_310)
                                       with
                                       | true  ->
                                           (run
                                              ((fun c  ->
                                                  handler
                                                    {
                                                      value_clause =
                                                        (fun _j_311  ->
                                                           let _y_312 =
                                                             run
                                                               ((run
                                                                   (lift_binary
                                                                    (+)
                                                                    _i_296))
                                                                  _j_311)
                                                              in
                                                           value
                                                             (fun _s_313  ->
                                                                match _s_313
                                                                with
                                                                | [] ->
                                                                    value
                                                                    _y_312
                                                                | _ ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_314
                                                                     ->
                                                                    _absurd_1
                                                                    _result_314)));
                                                      effect_clauses = fun
                                                        (type a) -> fun (type
                                                        b) ->
                                                        fun
                                                          (x : (a,b) effect) 
                                                          ->
                                                          (match x with
                                                           | Effect_Symbol 
                                                               ->
                                                               (fun
                                                                  (_c_316 :
                                                                    string)
                                                                   ->
                                                                  fun
                                                                    (_k_315 :
                                                                    (unit ->
                                                                    string
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
                                                                     ->
                                                                    value
                                                                    (fun
                                                                    _s_317 
                                                                    ->
                                                                    match _s_317
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (run
                                                                    (_k_315
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_318
                                                                     ->
                                                                    _absurd_1
                                                                    _result_318))))
                                                                    []
                                                                    | 
                                                                    _x_320::_xs_319
                                                                    ->
                                                                    (match 
                                                                    run
                                                                    ((run
                                                                    (lift_binary
                                                                    (=)
                                                                    _c_316))
                                                                    _x_320)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    (run
                                                                    (_k_315
                                                                    (fun () 
                                                                    ->
                                                                    value
                                                                    _x_320)))
                                                                    _xs_319
                                                                    | 
                                                                    false  ->
                                                                    (run
                                                                    (_k_315
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_321
                                                                     ->
                                                                    _absurd_1
                                                                    _result_321))))
                                                                    _s_317)))
                                                           | eff' ->
                                                               (fun arg  ->
                                                                  fun k  ->
                                                                    Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                          a ->
                                                            (b ->
                                                               _ computation)
                                                              ->
                                                              _ computation)
                                                    } c) (_expr_76 ())))
                                             _xs_309
                                       | false  ->
                                           (run
                                              ((fun c  ->
                                                  handler
                                                    {
                                                      value_clause =
                                                        (fun _j_322  ->
                                                           let _y_323 =
                                                             run
                                                               ((run
                                                                   (lift_binary
                                                                    (+)
                                                                    _i_296))
                                                                  _j_322)
                                                              in
                                                           value
                                                             (fun _s_324  ->
                                                                match _s_324
                                                                with
                                                                | [] ->
                                                                    value
                                                                    _y_323
                                                                | _ ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_325
                                                                     ->
                                                                    _absurd_1
                                                                    _result_325)));
                                                      effect_clauses = fun
                                                        (type a) -> fun (type
                                                        b) ->
                                                        fun
                                                          (x : (a,b) effect) 
                                                          ->
                                                          (match x with
                                                           | Effect_Symbol 
                                                               ->
                                                               (fun
                                                                  (_c_327 :
                                                                    string)
                                                                   ->
                                                                  fun
                                                                    (_k_326 :
                                                                    (unit ->
                                                                    string
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
                                                                     ->
                                                                    value
                                                                    (fun
                                                                    _s_328 
                                                                    ->
                                                                    match _s_328
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (run
                                                                    (_k_326
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_329
                                                                     ->
                                                                    _absurd_1
                                                                    _result_329))))
                                                                    []
                                                                    | 
                                                                    _x_331::_xs_330
                                                                    ->
                                                                    (match 
                                                                    run
                                                                    ((run
                                                                    (lift_binary
                                                                    (=)
                                                                    _c_327))
                                                                    _x_331)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    (run
                                                                    (_k_326
                                                                    (fun () 
                                                                    ->
                                                                    value
                                                                    _x_331)))
                                                                    _xs_330
                                                                    | 
                                                                    false  ->
                                                                    (run
                                                                    (_k_326
                                                                    (fun () 
                                                                    ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_332
                                                                     ->
                                                                    _absurd_1
                                                                    _result_332))))
                                                                    _s_328)))
                                                           | eff' ->
                                                               (fun arg  ->
                                                                  fun k  ->
                                                                    Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                          a ->
                                                            (b ->
                                                               _ computation)
                                                              ->
                                                              _ computation)
                                                    } c) (_expr_76 ())))
                                             _s_297)));
                        effect_clauses = fun (type a) -> fun (type b) ->
                          fun (x : (a,b) effect)  ->
                            (match x with
                             | Effect_Symbol  ->
                                 (fun (_c_334 : string)  ->
                                    fun
                                      (_k_333 :
                                        (unit -> string computation) ->
                                          _ computation)
                                       ->
                                      value
                                        (fun _s_335  ->
                                           match _s_335 with
                                           | [] ->
                                               (run
                                                  (_k_333
                                                     (fun ()  ->
                                                        call Effect_Fail ()
                                                          (fun _result_336 
                                                             ->
                                                             _absurd_1
                                                               _result_336))))
                                                 []
                                           | _x_338::_xs_337 ->
                                               (match run
                                                        ((run
                                                            (lift_binary (=)
                                                               _c_334))
                                                           _x_338)
                                                with
                                                | true  ->
                                                    (run
                                                       (_k_333
                                                          (fun ()  ->
                                                             value _x_338)))
                                                      _xs_337
                                                | false  ->
                                                    (run
                                                       (_k_333
                                                          (fun ()  ->
                                                             call Effect_Fail
                                                               ()
                                                               (fun
                                                                  _result_339
                                                                   ->
                                                                  _absurd_1
                                                                    _result_339))))
                                                      _s_335)))
                             | eff' ->
                                 (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                            a -> (b -> _ computation) -> _ computation)
                      } c)) (_term_284 ())
            | false  ->
                ((fun c  ->
                    handler
                      {
                        value_clause =
                          (fun _y_340  ->
                             value
                               (fun _s_341  ->
                                  match _s_341 with
                                  | [] -> value _y_340
                                  | _ ->
                                      call Effect_Fail ()
                                        (fun _result_342  ->
                                           _absurd_1 _result_342)));
                        effect_clauses = fun (type a) -> fun (type b) ->
                          fun (x : (a,b) effect)  ->
                            (match x with
                             | Effect_Symbol  ->
                                 (fun (_c_344 : string)  ->
                                    fun
                                      (_k_343 :
                                        (unit -> string computation) ->
                                          _ computation)
                                       ->
                                      value
                                        (fun _s_345  ->
                                           match _s_345 with
                                           | [] ->
                                               (run
                                                  (_k_343
                                                     (fun ()  ->
                                                        call Effect_Fail ()
                                                          (fun _result_346 
                                                             ->
                                                             _absurd_1
                                                               _result_346))))
                                                 []
                                           | _x_348::_xs_347 ->
                                               (match run
                                                        ((run
                                                            (lift_binary (=)
                                                               _c_344))
                                                           _x_348)
                                                with
                                                | true  ->
                                                    (run
                                                       (_k_343
                                                          (fun ()  ->
                                                             value _x_348)))
                                                      _xs_347
                                                | false  ->
                                                    (run
                                                       (_k_343
                                                          (fun ()  ->
                                                             call Effect_Fail
                                                               ()
                                                               (fun
                                                                  _result_349
                                                                   ->
                                                                  _absurd_1
                                                                    _result_349))))
                                                      _s_345)))
                             | eff' ->
                                 (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                            a -> (b -> _ computation) -> _ computation)
                      } c)) (_term_284 ())))
     in
  _newvar_360 () 
