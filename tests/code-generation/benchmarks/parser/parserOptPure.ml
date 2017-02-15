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
;;"End of pervasives"
let _absurd_1 _void_2 = match _void_2 with | _ -> assert false 
let _var_3 = (=) 
let rec _var_4 _xs_5 _ys_6 =
  match _xs_5 with
  | [] -> _ys_6
  | _x_7::_xs_8 -> _x_7 :: (_var_4 _xs_8 _ys_6) 
let _var_11 = (+) 
let _var_12 = ( * ) 
type (_,_) effect +=
  | Effect_Symbol: (string,unit -> string computation) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
let _parse_13 comp =
  handler
    {
      value_clause =
        (fun _y_26  ->
           fun _s_27  ->
             match _s_27 with
             | [] -> value _y_26
             | _ ->
                 call Effect_Fail ()
                   (fun _result_3  -> value (_absurd_1 _result_3)));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Symbol  ->
               (fun (_c_14 : string)  ->
                  fun (_k_15 : (unit -> string computation) -> _)  ->
                    fun _s_16  ->
                      match _s_16 with
                      | [] ->
                          _k_15
                            (fun ()  ->
                               call Effect_Fail ()
                                 (fun _result_6  ->
                                    value (_absurd_1 _result_6))) []
                      | _x_19::_xs_20 ->
                          if _c_14 = _x_19
                          then
                            _k_15
                              (fun _lift_fun_387  ->
                                 value ((fun ()  -> _x_19) _lift_fun_387))
                              _xs_20
                          else
                            _k_15
                              (fun ()  ->
                                 call Effect_Fail ()
                                   (fun _result_9  ->
                                      value (_absurd_1 _result_9))) _s_16)
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _allsols_29 comp =
  handler
    {
      value_clause = (fun _x_34  -> value [_x_34]);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_30 : bool -> _)  ->
                    (_k_30 true) >>
                      (fun _gen_bind_32  ->
                         let _gen_bind_31 = _var_4 _gen_bind_32  in
                         (_k_30 false) >>
                           (fun _gen_bind_33  ->
                              value (_gen_bind_31 _gen_bind_33))))
           | Effect_Fail  ->
               (fun (_ : unit)  -> fun (_ : unit -> _)  -> value [])
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _backtrack_35 comp =
  handler
    {
      value_clause = (fun _gen_id_par_100  -> _gen_id_par_100);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  -> fun (_k_36 : bool -> _)  -> _k_36 true)
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _createNumber_37 (_prev_38,_num_39) = (_prev_38 * 10) + _num_39 
let rec _parseNum_43 (_l_44,_v_45) =
  match _l_44 with
  | [] -> _v_45
  | _x_46::_xs_47 ->
      (match _x_46 with
       | "0" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 0)))
       | "1" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 1)))
       | "2" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 2)))
       | "3" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 3)))
       | "4" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 4)))
       | "5" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 5)))
       | "6" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 6)))
       | "7" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 7)))
       | "8" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 8)))
       | "9" -> _parseNum_43 (_xs_47, (_createNumber_37 (_v_45, 9))))
  
let rec _toNum_58 _l_59 = _parseNum_43 (_l_59, 0) 
let _digit_60 () =
  let rec _checkNums_62 _n_63 =
    match _n_63 with
    | [] ->
        call Effect_Fail () (fun _result_12  -> value (_absurd_1 _result_12))
    | _x_65::_xs_66 ->
        call Effect_Decide ()
          (fun _result_18  ->
             if _result_18
             then
               call Effect_Symbol _x_65
                 (fun _result_15  -> value (_result_15 ()))
             else _checkNums_62 _xs_66)
     in
  let rec _newvar_21 _n_63 =
    match _n_63 with
    | [] ->
        call Effect_Fail () (fun _result_24  -> value (_absurd_1 _result_24))
    | _x_65::_xs_66 ->
        value
          (call Effect_Symbol _x_65
             (fun _result_33  -> value (_result_33 ())))
     in
  _newvar_21 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] 
let rec _many_69 _m_70 =
  call Effect_Decide ()
    (fun _result_41  -> value (if _result_41 then _m_70 () else []))
  
let rec _many1_72 () =
  (_digit_60 ()) >>
    (fun _x_73  ->
       (_many_69 _many1_72) >> (fun _xs_74  -> value (_var_4 [_x_73] _xs_74)))
  
let rec _expr_76 () =
  let rec _term_77 () =
    let rec _factor_78 () =
      call Effect_Decide ()
        (fun _result_66  ->
           if _result_66
           then (_many1_72 ()) >> (fun _i_80  -> value (_toNum_58 _i_80))
           else
             call Effect_Symbol "("
               (fun _result_63  ->
                  (_expr_76 ()) >>
                    (fun _j_83  ->
                       call Effect_Symbol ")"
                         (fun _result_59  -> value _j_83))))
       in
    call Effect_Decide ()
      (fun _result_55  ->
         if _result_55
         then
           (_factor_78 ()) >>
             (fun _i_87  ->
                call Effect_Symbol "*"
                  (fun _result_52  ->
                     (_term_77 ()) >> (fun _j_90  -> value (_i_87 * _j_90))))
         else _factor_78 ())
     in
  call Effect_Decide ()
    (fun _result_48  ->
       if _result_48
       then
         (_term_77 ()) >>
           (fun _i_93  ->
              call Effect_Symbol "+"
                (fun _result_45  ->
                   (_expr_76 ()) >> (fun _j_96  -> value (_i_93 + _j_96))))
       else _term_77 ())
  
let _parseTest_98 () =
  let rec _newvar_283 () =
    let rec _term_284 () =
      let rec _factor_285 () =
        call Effect_Decide ()
          (fun _result_286  ->
             if _result_286
             then (_many1_72 ()) >> (fun _i_287  -> value (_toNum_58 _i_287))
             else
               call Effect_Symbol "("
                 (fun _result_288  ->
                    (_expr_76 ()) >>
                      (fun _j_289  ->
                         call Effect_Symbol ")"
                           (fun _result_290  -> value _j_289))))
         in
      call Effect_Decide ()
        (fun _result_291  ->
           if _result_291
           then
             (_factor_285 ()) >>
               (fun _i_292  ->
                  call Effect_Symbol "*"
                    (fun _result_293  ->
                       (_term_284 ()) >>
                         (fun _j_294  -> value (_i_292 * _j_294))))
           else _factor_285 ())
       in
    call Effect_Decide ()
      (fun _result_295  ->
         if _result_295
         then
           (fun comp  ->
              handler
                {
                  value_clause =
                    (fun _i_296  ->
                       fun _s_297  ->
                         match _s_297 with
                         | [] ->
                             ((fun comp  ->
                                 handler
                                   {
                                     value_clause =
                                       (fun _j_298  ->
                                          let _y_299 = _i_296 + _j_298  in
                                          fun _s_300  ->
                                            match _s_300 with
                                            | [] -> value _y_299
                                            | _ ->
                                                call Effect_Fail ()
                                                  (fun _result_301  ->
                                                     value
                                                       (_absurd_1 _result_301)));
                                     effect_clauses = fun (type a) -> fun
                                       (type b) ->
                                       fun (x : (a,b) effect)  ->
                                         (match x with
                                          | Effect_Symbol  ->
                                              (fun (_c_303 : string)  ->
                                                 fun
                                                   (_k_302 :
                                                     (unit ->
                                                        string computation)
                                                       -> _)
                                                    ->
                                                   fun _s_304  ->
                                                     match _s_304 with
                                                     | [] ->
                                                         _k_302
                                                           (fun ()  ->
                                                              call
                                                                Effect_Fail
                                                                ()
                                                                (fun
                                                                   _result_305
                                                                    ->
                                                                   value
                                                                    (_absurd_1
                                                                    _result_305)))
                                                           []
                                                     | _x_307::_xs_306 ->
                                                         if _c_303 = _x_307
                                                         then
                                                           _k_302
                                                             (fun
                                                                _lift_fun_388
                                                                 ->
                                                                value
                                                                  ((fun () 
                                                                    -> _x_307)
                                                                    _lift_fun_388))
                                                             _xs_306
                                                         else
                                                           _k_302
                                                             (fun ()  ->
                                                                call
                                                                  Effect_Fail
                                                                  ()
                                                                  (fun
                                                                    _result_308
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_308)))
                                                             _s_304)
                                          | eff' ->
                                              (fun arg  ->
                                                 fun k  ->
                                                   Call (eff', arg, k)) : 
                                         a -> (b -> _) -> _)
                                   } comp)) (_expr_76 ()) []
                         | _x_310::_xs_309 ->
                             if "+" = _x_310
                             then
                               ((fun comp  ->
                                   handler
                                     {
                                       value_clause =
                                         (fun _j_311  ->
                                            let _y_312 = _i_296 + _j_311  in
                                            fun _s_313  ->
                                              match _s_313 with
                                              | [] -> value _y_312
                                              | _ ->
                                                  call Effect_Fail ()
                                                    (fun _result_314  ->
                                                       value
                                                         (_absurd_1
                                                            _result_314)));
                                       effect_clauses = fun (type a) -> fun
                                         (type b) ->
                                         fun (x : (a,b) effect)  ->
                                           (match x with
                                            | Effect_Symbol  ->
                                                (fun (_c_316 : string)  ->
                                                   fun
                                                     (_k_315 :
                                                       (unit ->
                                                          string computation)
                                                         -> _)
                                                      ->
                                                     fun _s_317  ->
                                                       match _s_317 with
                                                       | [] ->
                                                           _k_315
                                                             (fun ()  ->
                                                                call
                                                                  Effect_Fail
                                                                  ()
                                                                  (fun
                                                                    _result_318
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_318)))
                                                             []
                                                       | _x_320::_xs_319 ->
                                                           if _c_316 = _x_320
                                                           then
                                                             _k_315
                                                               (fun
                                                                  _lift_fun_389
                                                                   ->
                                                                  value
                                                                    (
                                                                    (fun () 
                                                                    -> _x_320)
                                                                    _lift_fun_389))
                                                               _xs_319
                                                           else
                                                             _k_315
                                                               (fun ()  ->
                                                                  call
                                                                    Effect_Fail
                                                                    ()
                                                                    (
                                                                    fun
                                                                    _result_321
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_321)))
                                                               _s_317)
                                            | eff' ->
                                                (fun arg  ->
                                                   fun k  ->
                                                     Call (eff', arg, k)) : 
                                           a -> (b -> _) -> _)
                                     } comp)) (_expr_76 ()) _xs_309
                             else
                               ((fun comp  ->
                                   handler
                                     {
                                       value_clause =
                                         (fun _j_322  ->
                                            let _y_323 = _i_296 + _j_322  in
                                            fun _s_324  ->
                                              match _s_324 with
                                              | [] -> value _y_323
                                              | _ ->
                                                  call Effect_Fail ()
                                                    (fun _result_325  ->
                                                       value
                                                         (_absurd_1
                                                            _result_325)));
                                       effect_clauses = fun (type a) -> fun
                                         (type b) ->
                                         fun (x : (a,b) effect)  ->
                                           (match x with
                                            | Effect_Symbol  ->
                                                (fun (_c_327 : string)  ->
                                                   fun
                                                     (_k_326 :
                                                       (unit ->
                                                          string computation)
                                                         -> _)
                                                      ->
                                                     fun _s_328  ->
                                                       match _s_328 with
                                                       | [] ->
                                                           _k_326
                                                             (fun ()  ->
                                                                call
                                                                  Effect_Fail
                                                                  ()
                                                                  (fun
                                                                    _result_329
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_329)))
                                                             []
                                                       | _x_331::_xs_330 ->
                                                           if _c_327 = _x_331
                                                           then
                                                             _k_326
                                                               (fun
                                                                  _lift_fun_390
                                                                   ->
                                                                  value
                                                                    (
                                                                    (fun () 
                                                                    -> _x_331)
                                                                    _lift_fun_390))
                                                               _xs_330
                                                           else
                                                             _k_326
                                                               (fun ()  ->
                                                                  call
                                                                    Effect_Fail
                                                                    ()
                                                                    (
                                                                    fun
                                                                    _result_332
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_332)))
                                                               _s_328)
                                            | eff' ->
                                                (fun arg  ->
                                                   fun k  ->
                                                     Call (eff', arg, k)) : 
                                           a -> (b -> _) -> _)
                                     } comp)) (_expr_76 ()) _s_297);
                  effect_clauses = fun (type a) -> fun (type b) ->
                    fun (x : (a,b) effect)  ->
                      (match x with
                       | Effect_Symbol  ->
                           (fun (_c_334 : string)  ->
                              fun
                                (_k_333 : (unit -> string computation) -> _) 
                                ->
                                fun _s_335  ->
                                  match _s_335 with
                                  | [] ->
                                      _k_333
                                        (fun ()  ->
                                           call Effect_Fail ()
                                             (fun _result_336  ->
                                                value (_absurd_1 _result_336)))
                                        []
                                  | _x_338::_xs_337 ->
                                      if _c_334 = _x_338
                                      then
                                        _k_333
                                          (fun _lift_fun_391  ->
                                             value
                                               ((fun ()  -> _x_338)
                                                  _lift_fun_391)) _xs_337
                                      else
                                        _k_333
                                          (fun ()  ->
                                             call Effect_Fail ()
                                               (fun _result_339  ->
                                                  value
                                                    (_absurd_1 _result_339)))
                                          _s_335)
                       | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                      a -> (b -> _) -> _)
                } comp) (_term_284 ())
         else
           ((fun comp  ->
               handler
                 {
                   value_clause =
                     (fun _y_340  ->
                        fun _s_341  ->
                          match _s_341 with
                          | [] -> value _y_340
                          | _ ->
                              call Effect_Fail ()
                                (fun _result_342  ->
                                   value (_absurd_1 _result_342)));
                   effect_clauses = fun (type a) -> fun (type b) ->
                     fun (x : (a,b) effect)  ->
                       (match x with
                        | Effect_Symbol  ->
                            (fun (_c_344 : string)  ->
                               fun
                                 (_k_343 : (unit -> string computation) -> _)
                                  ->
                                 fun _s_345  ->
                                   match _s_345 with
                                   | [] ->
                                       _k_343
                                         (fun ()  ->
                                            call Effect_Fail ()
                                              (fun _result_346  ->
                                                 value
                                                   (_absurd_1 _result_346)))
                                         []
                                   | _x_348::_xs_347 ->
                                       if _c_344 = _x_348
                                       then
                                         _k_343
                                           (fun _lift_fun_392  ->
                                              value
                                                ((fun ()  -> _x_348)
                                                   _lift_fun_392)) _xs_347
                                       else
                                         _k_343
                                           (fun ()  ->
                                              call Effect_Fail ()
                                                (fun _result_349  ->
                                                   value
                                                     (_absurd_1 _result_349)))
                                           _s_345)
                        | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                       a -> (b -> _) -> _)
                 } comp)) (_term_284 ()))
     in
  let rec _newvar_360 () =
    (fun comp  ->
       handler
         {
           value_clause =
             (fun _gen_bind_350  ->
                (fun comp  ->
                   handler
                     {
                       value_clause = (fun _x_351  -> [_x_351]);
                       effect_clauses = fun (type a) -> fun (type b) ->
                         fun (x : (a,b) effect)  ->
                           (match x with
                            | Effect_Decide  ->
                                (fun (_ : unit)  ->
                                   fun (_k_352 : bool -> _)  ->
                                     let _gen_bind_353 = _k_352 true  in
                                     let _gen_bind_354 = _var_4 _gen_bind_353
                                        in
                                     let _gen_bind_355 = _k_352 false  in
                                     _gen_bind_354 _gen_bind_355)
                            | Effect_Fail  ->
                                (fun (_ : unit)  ->
                                   fun (_ : unit -> _)  -> [])
                            | eff' ->
                                (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                           a -> (b -> _) -> _)
                     } comp)
                  (_gen_bind_350 ["4"; "3"; "*"; "("; "3"; "+"; "3"; ")"]));
           effect_clauses = fun (type a) -> fun (type b) ->
             fun (x : (a,b) effect)  ->
               (match x with
                | Effect_Decide  ->
                    (fun (_ : unit)  ->
                       fun (_k_356 : bool -> _)  ->
                         let _gen_bind_357 = _k_356 true  in
                         let _gen_bind_358 = _var_4 _gen_bind_357  in
                         let _gen_bind_359 = _k_356 false  in
                         _gen_bind_358 _gen_bind_359)
                | Effect_Fail  ->
                    (fun (_ : unit)  -> fun (_ : unit -> _)  -> [])
                | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
               a -> (b -> _) -> _)
         } comp)
      (let rec _term_284 () =
         let rec _factor_285 () =
           call Effect_Decide ()
             (fun _result_286  ->
                if _result_286
                then
                  (_many1_72 ()) >> (fun _i_287  -> value (_toNum_58 _i_287))
                else
                  call Effect_Symbol "("
                    (fun _result_288  ->
                       (_expr_76 ()) >>
                         (fun _j_289  ->
                            call Effect_Symbol ")"
                              (fun _result_290  -> value _j_289))))
            in
         call Effect_Decide ()
           (fun _result_291  ->
              if _result_291
              then
                (_factor_285 ()) >>
                  (fun _i_292  ->
                     call Effect_Symbol "*"
                       (fun _result_293  ->
                          (_term_284 ()) >>
                            (fun _j_294  -> value (_i_292 * _j_294))))
              else _factor_285 ())
          in
       call Effect_Decide ()
         (fun _result_295  ->
            if _result_295
            then
              (fun comp  ->
                 handler
                   {
                     value_clause =
                       (fun _i_296  ->
                          fun _s_297  ->
                            match _s_297 with
                            | [] ->
                                (let rec _newvar_361 () =
                                   let rec _term_77 () =
                                     let rec _factor_78 () =
                                       call Effect_Decide ()
                                         (fun _result_386  ->
                                            if _result_386
                                            then
                                              (_many1_72 ()) >>
                                                (fun _i_80  ->
                                                   value (_toNum_58 _i_80))
                                            else
                                              call Effect_Symbol "("
                                                (fun _result_383  ->
                                                   (_expr_76 ()) >>
                                                     (fun _j_83  ->
                                                        call Effect_Symbol
                                                          ")"
                                                          (fun _result_379 
                                                             -> value _j_83))))
                                        in
                                     call Effect_Decide ()
                                       (fun _result_375  ->
                                          if _result_375
                                          then
                                            (_factor_78 ()) >>
                                              (fun _i_87  ->
                                                 call Effect_Symbol "*"
                                                   (fun _result_372  ->
                                                      (_term_77 ()) >>
                                                        (fun _j_90  ->
                                                           value
                                                             (_i_87 * _j_90))))
                                          else _factor_78 ())
                                      in
                                   (fun comp  ->
                                      handler
                                        {
                                          value_clause =
                                            (fun _j_298  ->
                                               let _y_299 = _i_296 + _j_298
                                                  in
                                               fun _s_300  ->
                                                 match _s_300 with
                                                 | [] -> value _y_299
                                                 | _ ->
                                                     call Effect_Fail ()
                                                       (fun _result_301  ->
                                                          value
                                                            (_absurd_1
                                                               _result_301)));
                                          effect_clauses = fun (type a) ->
                                            fun (type b) ->
                                            fun (x : (a,b) effect)  ->
                                              (match x with
                                               | Effect_Symbol  ->
                                                   (fun (_c_303 : string)  ->
                                                      fun
                                                        (_k_302 :
                                                          (unit ->
                                                             string
                                                               computation)
                                                            -> _)
                                                         ->
                                                        fun _s_304  ->
                                                          match _s_304 with
                                                          | [] ->
                                                              _k_302
                                                                (fun ()  ->
                                                                   call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_305
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_305)))
                                                                []
                                                          | _x_307::_xs_306
                                                              ->
                                                              if
                                                                _c_303 =
                                                                  _x_307
                                                              then
                                                                _k_302
                                                                  (fun
                                                                    _lift_fun_393
                                                                     ->
                                                                    value
                                                                    ((fun () 
                                                                    -> _x_307)
                                                                    _lift_fun_393))
                                                                  _xs_306
                                                              else
                                                                _k_302
                                                                  (fun ()  ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_308
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_308)))
                                                                  _s_304)
                                               | eff' ->
                                                   (fun arg  ->
                                                      fun k  ->
                                                        Call (eff', arg, k)) : 
                                              a -> (b -> _) -> _)
                                        } comp)
                                     (call Effect_Decide ()
                                        (fun _result_368  ->
                                           if _result_368
                                           then
                                             (_term_77 ()) >>
                                               (fun _i_93  ->
                                                  call Effect_Symbol "+"
                                                    (fun _result_365  ->
                                                       (_expr_76 ()) >>
                                                         (fun _j_96  ->
                                                            value
                                                              (_i_93 + _j_96))))
                                           else _term_77 ()))
                                    in
                                 _newvar_361 ()) []
                            | _x_310::_xs_309 ->
                                if "+" = _x_310
                                then
                                  ((fun comp  ->
                                      handler
                                        {
                                          value_clause =
                                            (fun _j_311  ->
                                               let _y_312 = _i_296 + _j_311
                                                  in
                                               fun _s_313  ->
                                                 match _s_313 with
                                                 | [] -> value _y_312
                                                 | _ ->
                                                     call Effect_Fail ()
                                                       (fun _result_314  ->
                                                          value
                                                            (_absurd_1
                                                               _result_314)));
                                          effect_clauses = fun (type a) ->
                                            fun (type b) ->
                                            fun (x : (a,b) effect)  ->
                                              (match x with
                                               | Effect_Symbol  ->
                                                   (fun (_c_316 : string)  ->
                                                      fun
                                                        (_k_315 :
                                                          (unit ->
                                                             string
                                                               computation)
                                                            -> _)
                                                         ->
                                                        fun _s_317  ->
                                                          match _s_317 with
                                                          | [] ->
                                                              _k_315
                                                                (fun ()  ->
                                                                   call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_318
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_318)))
                                                                []
                                                          | _x_320::_xs_319
                                                              ->
                                                              if
                                                                _c_316 =
                                                                  _x_320
                                                              then
                                                                _k_315
                                                                  (fun
                                                                    _lift_fun_394
                                                                     ->
                                                                    value
                                                                    ((fun () 
                                                                    -> _x_320)
                                                                    _lift_fun_394))
                                                                  _xs_319
                                                              else
                                                                _k_315
                                                                  (fun ()  ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_321
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_321)))
                                                                  _s_317)
                                               | eff' ->
                                                   (fun arg  ->
                                                      fun k  ->
                                                        Call (eff', arg, k)) : 
                                              a -> (b -> _) -> _)
                                        } comp)) (_expr_76 ()) _xs_309
                                else
                                  ((fun comp  ->
                                      handler
                                        {
                                          value_clause =
                                            (fun _j_322  ->
                                               let _y_323 = _i_296 + _j_322
                                                  in
                                               fun _s_324  ->
                                                 match _s_324 with
                                                 | [] -> value _y_323
                                                 | _ ->
                                                     call Effect_Fail ()
                                                       (fun _result_325  ->
                                                          value
                                                            (_absurd_1
                                                               _result_325)));
                                          effect_clauses = fun (type a) ->
                                            fun (type b) ->
                                            fun (x : (a,b) effect)  ->
                                              (match x with
                                               | Effect_Symbol  ->
                                                   (fun (_c_327 : string)  ->
                                                      fun
                                                        (_k_326 :
                                                          (unit ->
                                                             string
                                                               computation)
                                                            -> _)
                                                         ->
                                                        fun _s_328  ->
                                                          match _s_328 with
                                                          | [] ->
                                                              _k_326
                                                                (fun ()  ->
                                                                   call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_329
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_329)))
                                                                []
                                                          | _x_331::_xs_330
                                                              ->
                                                              if
                                                                _c_327 =
                                                                  _x_331
                                                              then
                                                                _k_326
                                                                  (fun
                                                                    _lift_fun_395
                                                                     ->
                                                                    value
                                                                    ((fun () 
                                                                    -> _x_331)
                                                                    _lift_fun_395))
                                                                  _xs_330
                                                              else
                                                                _k_326
                                                                  (fun ()  ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_332
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_332)))
                                                                  _s_328)
                                               | eff' ->
                                                   (fun arg  ->
                                                      fun k  ->
                                                        Call (eff', arg, k)) : 
                                              a -> (b -> _) -> _)
                                        } comp)) (_expr_76 ()) _s_297);
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_Symbol  ->
                              (fun (_c_334 : string)  ->
                                 fun
                                   (_k_333 :
                                     (unit -> string computation) -> _)
                                    ->
                                   fun _s_335  ->
                                     match _s_335 with
                                     | [] ->
                                         _k_333
                                           (fun ()  ->
                                              call Effect_Fail ()
                                                (fun _result_336  ->
                                                   value
                                                     (_absurd_1 _result_336)))
                                           []
                                     | _x_338::_xs_337 ->
                                         if _c_334 = _x_338
                                         then
                                           _k_333
                                             (fun _lift_fun_396  ->
                                                value
                                                  ((fun ()  -> _x_338)
                                                     _lift_fun_396)) _xs_337
                                         else
                                           _k_333
                                             (fun ()  ->
                                                call Effect_Fail ()
                                                  (fun _result_339  ->
                                                     value
                                                       (_absurd_1 _result_339)))
                                             _s_335)
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _) -> _)
                   } comp) (_term_284 ())
            else
              ((fun comp  ->
                  handler
                    {
                      value_clause =
                        (fun _y_340  ->
                           fun _s_341  ->
                             match _s_341 with
                             | [] -> value _y_340
                             | _ ->
                                 call Effect_Fail ()
                                   (fun _result_342  ->
                                      value (_absurd_1 _result_342)));
                      effect_clauses = fun (type a) -> fun (type b) ->
                        fun (x : (a,b) effect)  ->
                          (match x with
                           | Effect_Symbol  ->
                               (fun (_c_344 : string)  ->
                                  fun
                                    (_k_343 :
                                      (unit -> string computation) -> _)
                                     ->
                                    fun _s_345  ->
                                      match _s_345 with
                                      | [] ->
                                          _k_343
                                            (fun ()  ->
                                               call Effect_Fail ()
                                                 (fun _result_346  ->
                                                    value
                                                      (_absurd_1 _result_346)))
                                            []
                                      | _x_348::_xs_347 ->
                                          if _c_344 = _x_348
                                          then
                                            _k_343
                                              (fun _lift_fun_397  ->
                                                 value
                                                   ((fun ()  -> _x_348)
                                                      _lift_fun_397)) _xs_347
                                          else
                                            _k_343
                                              (fun ()  ->
                                                 call Effect_Fail ()
                                                   (fun _result_349  ->
                                                      value
                                                        (_absurd_1
                                                           _result_349)))
                                              _s_345)
                           | eff' ->
                               (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                          a -> (b -> _) -> _)
                    } comp)) (_term_284 ())))
     in
  _newvar_360 () 
File "_tmp/parser.eff.ml", line 150, characters 93-112:
Error: This expression has type 'a computation
       but an expression was expected of type string list -> 'b
