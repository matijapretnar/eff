(*
=== GENERATED FROM parser.eff ===
commit SHA: ec8d6d094577edb51f0603c9a7d9f74d8bd5c47a
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
  | Effect_Symbol: (string,string) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
let _parse_13 comp =
  handler
    {
      value_clause =
        (fun _y_24  ->
           value
             (fun _s_25  ->
                match _s_25 with
                | [] -> value _y_24
                | _ ->
                    call Effect_Fail ()
                      (fun _result_3  -> value (_absurd_1 _result_3))));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Symbol  ->
               (fun (_c_14 : string)  ->
                  fun (_k_15 : string -> _)  ->
                    value
                      (fun _s_16  ->
                         match _s_16 with
                         | [] ->
                             call Effect_Fail ()
                               (fun _result_6  -> value (_absurd_1 _result_6))
                         | _x_18::_xs_19 ->
                             if _c_14 = _x_18
                             then
                               (_k_15 _x_18) >>
                                 ((fun _gen_bind_22  -> _gen_bind_22 _xs_19))
                             else
                               call Effect_Fail ()
                                 (fun _result_9  ->
                                    value (_absurd_1 _result_9))))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _allsols_27 comp =
  handler
    {
      value_clause = (fun _x_32  -> value [_x_32]);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_28 : bool -> _)  ->
                    (_k_28 true) >>
                      (fun _gen_bind_30  ->
                         let _gen_bind_29 = _var_4 _gen_bind_30  in
                         (_k_28 false) >>
                           (fun _gen_bind_31  ->
                              value (_gen_bind_29 _gen_bind_31))))
           | Effect_Fail  ->
               (fun (_ : unit)  -> fun (_ : unit -> _)  -> value [])
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _backtrack_33 comp =
  handler
    {
      value_clause = (fun _gen_id_par_94  -> value _gen_id_par_94);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_34 : bool -> _)  ->
                    (fun comp  ->
                       handler
                         {
                           value_clause =
                             (fun _gen_id_par_95  -> value _gen_id_par_95);
                           effect_clauses = fun (type a) -> fun (type b) ->
                             fun (x : (a,b) effect)  ->
                               (match x with
                                | Effect_Fail  ->
                                    (fun (_ : unit)  ->
                                       fun (_ : unit -> _)  -> _k_34 false)
                                | eff' ->
                                    (fun arg  ->
                                       fun k  -> Call (eff', arg, k)) : 
                               a -> (b -> _) -> _)
                         } comp) (_k_34 true))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _createNumber_35 (_prev_36,_num_37) = (_prev_36 * 10) + _num_37 
let rec _parseNum_41 (_l_42,_v_43) =
  match _l_42 with
  | [] -> _v_43
  | _x_44::_xs_45 ->
      (match _x_44 with
       | "0" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 0)))
       | "1" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 1)))
       | "2" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 2)))
       | "3" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 3)))
       | "4" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 4)))
       | "5" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 5)))
       | "6" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 6)))
       | "7" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 7)))
       | "8" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 8)))
       | "9" -> _parseNum_41 (_xs_45, (_createNumber_35 (_v_43, 9))))
  
let rec _toNum_56 _l_57 = _parseNum_41 (_l_57, 0) 
let _digit_58 () =
  let rec _checkNums_60 _n_61 =
    match _n_61 with
    | [] ->
        call Effect_Fail () (fun _result_12  -> value (_absurd_1 _result_12))
    | _x_63::_xs_64 ->
        call Effect_Decide ()
          (fun _result_17  ->
             if _result_17
             then
               call Effect_Symbol _x_63 (fun _result_14  -> value _result_14)
             else _checkNums_60 _xs_64)
     in
  _checkNums_60 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] 
let rec _many_66 _m_67 =
  call Effect_Decide ()
    (fun _result_20  -> if _result_20 then _m_67 () else value [])
  
let rec _many1_69 () =
  (_digit_58 ()) >>
    (fun _x_70  ->
       (_many_66 _many1_69) >> (fun _xs_71  -> value (_var_4 [_x_70] _xs_71)))
  
let rec _expr_73 () =
  let rec _term_74 () =
    let rec _factor_75 () =
      call Effect_Decide ()
        (fun _result_41  ->
           if _result_41
           then (_many1_69 ()) >> (fun _i_77  -> value (_toNum_56 _i_77))
           else
             call Effect_Symbol "("
               (fun _result_38  ->
                  (_expr_73 ()) >>
                    (fun _j_79  ->
                       call Effect_Symbol ")"
                         (fun _result_35  -> value _j_79))))
       in
    call Effect_Decide ()
      (fun _result_32  ->
         if _result_32
         then
           (_factor_75 ()) >>
             (fun _i_82  ->
                call Effect_Symbol "*"
                  (fun _result_29  ->
                     (_term_74 ()) >> (fun _j_84  -> value (_i_82 * _j_84))))
         else _factor_75 ())
     in
  call Effect_Decide ()
    (fun _result_26  ->
       if _result_26
       then
         (_term_74 ()) >>
           (fun _i_87  ->
              call Effect_Symbol "+"
                (fun _result_23  ->
                   (_expr_73 ()) >> (fun _j_89  -> value (_i_87 + _j_89))))
       else _term_74 ())
  
let _parseTest_91 () =
  let rec _newvar_222 () =
    let rec _term_223 () =
      let rec _factor_224 () =
        call Effect_Decide ()
          (fun _result_225  ->
             if _result_225
             then (_many1_69 ()) >> (fun _i_226  -> value (_toNum_56 _i_226))
             else
               call Effect_Symbol "("
                 (fun _result_227  ->
                    (_expr_73 ()) >>
                      (fun _j_228  ->
                         call Effect_Symbol ")"
                           (fun _result_229  -> value _j_228))))
         in
      call Effect_Decide ()
        (fun _result_230  ->
           if _result_230
           then
             (_factor_224 ()) >>
               (fun _i_231  ->
                  call Effect_Symbol "*"
                    (fun _result_232  ->
                       (_term_223 ()) >>
                         (fun _j_233  -> value (_i_231 * _j_233))))
           else _factor_224 ())
       in
    call Effect_Decide ()
      (fun _result_234  ->
         if _result_234
         then
           (fun comp  ->
              handler
                {
                  value_clause =
                    (fun _i_235  ->
                       value
                         (fun _s_236  ->
                            match _s_236 with
                            | [] ->
                                call Effect_Fail ()
                                  (fun _result_237  ->
                                     value (_absurd_1 _result_237))
                            | _x_239::_xs_238 ->
                                if "+" = _x_239
                                then
                                  ((fun comp  ->
                                      handler
                                        {
                                          value_clause =
                                            (fun _j_241  ->
                                               value
                                                 (let _y_242 =
                                                    _i_235 + _j_241  in
                                                  fun _s_243  ->
                                                    match _s_243 with
                                                    | [] -> value _y_242
                                                    | _ ->
                                                        call Effect_Fail ()
                                                          (fun _result_244 
                                                             ->
                                                             value
                                                               (_absurd_1
                                                                  _result_244))));
                                          effect_clauses = fun (type a) ->
                                            fun (type b) ->
                                            fun (x : (a,b) effect)  ->
                                              (match x with
                                               | Effect_Symbol  ->
                                                   (fun (_c_246 : string)  ->
                                                      fun
                                                        (_k_245 :
                                                          string -> _)
                                                         ->
                                                        value
                                                          (fun _s_247  ->
                                                             match _s_247
                                                             with
                                                             | [] ->
                                                                 call
                                                                   Effect_Fail
                                                                   ()
                                                                   (fun
                                                                    _result_248
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_248))
                                                             | _x_250::_xs_249
                                                                 ->
                                                                 if
                                                                   _c_246 =
                                                                    _x_250
                                                                 then
                                                                   (_k_245
                                                                    _x_250)
                                                                    >>
                                                                    ((
                                                                    fun
                                                                    _gen_bind_251
                                                                     ->
                                                                    _gen_bind_251
                                                                    _xs_249))
                                                                 else
                                                                   call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_252
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_252))))
                                               | eff' ->
                                                   (fun arg  ->
                                                      fun k  ->
                                                        Call (eff', arg, k)) : 
                                              a -> (b -> _) -> _)
                                        } comp) (_expr_73 ()))
                                    >>
                                    ((fun _gen_bind_240  ->
                                        _gen_bind_240 _xs_238))
                                else
                                  call Effect_Fail ()
                                    (fun _result_253  ->
                                       value (_absurd_1 _result_253))));
                  effect_clauses = fun (type a) -> fun (type b) ->
                    fun (x : (a,b) effect)  ->
                      (match x with
                       | Effect_Symbol  ->
                           (fun (_c_255 : string)  ->
                              fun (_k_254 : string -> _)  ->
                                value
                                  (fun _s_256  ->
                                     match _s_256 with
                                     | [] ->
                                         call Effect_Fail ()
                                           (fun _result_257  ->
                                              value (_absurd_1 _result_257))
                                     | _x_259::_xs_258 ->
                                         if _c_255 = _x_259
                                         then
                                           (_k_254 _x_259) >>
                                             ((fun _gen_bind_260  ->
                                                 _gen_bind_260 _xs_258))
                                         else
                                           call Effect_Fail ()
                                             (fun _result_261  ->
                                                value (_absurd_1 _result_261))))
                       | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                      a -> (b -> _) -> _)
                } comp) (_term_223 ())
         else
           ((fun comp  ->
               handler
                 {
                   value_clause =
                     (fun _y_262  ->
                        value
                          (fun _s_263  ->
                             match _s_263 with
                             | [] -> value _y_262
                             | _ ->
                                 call Effect_Fail ()
                                   (fun _result_264  ->
                                      value (_absurd_1 _result_264))));
                   effect_clauses = fun (type a) -> fun (type b) ->
                     fun (x : (a,b) effect)  ->
                       (match x with
                        | Effect_Symbol  ->
                            (fun (_c_266 : string)  ->
                               fun (_k_265 : string -> _)  ->
                                 value
                                   (fun _s_267  ->
                                      match _s_267 with
                                      | [] ->
                                          call Effect_Fail ()
                                            (fun _result_268  ->
                                               value (_absurd_1 _result_268))
                                      | _x_270::_xs_269 ->
                                          if _c_266 = _x_270
                                          then
                                            (_k_265 _x_270) >>
                                              ((fun _gen_bind_271  ->
                                                  _gen_bind_271 _xs_269))
                                          else
                                            call Effect_Fail ()
                                              (fun _result_272  ->
                                                 value
                                                   (_absurd_1 _result_272))))
                        | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                       a -> (b -> _) -> _)
                 } comp)) (_term_223 ()))
     in
  let rec _newvar_278 () =
    (fun comp  ->
       handler
         {
           value_clause =
             (fun _gen_bind_273  ->
                value
                  [_gen_bind_273 ["4"; "3"; "*"; "("; "3"; "+"; "3"; ")"]]);
           effect_clauses = fun (type a) -> fun (type b) ->
             fun (x : (a,b) effect)  ->
               (match x with
                | Effect_Decide  ->
                    (fun (_ : unit)  ->
                       fun (_k_274 : bool -> _)  ->
                         (_k_274 true) >>
                           (fun _gen_bind_275  ->
                              let _gen_bind_276 = _var_4 _gen_bind_275  in
                              (_k_274 false) >>
                                (fun _gen_bind_277  ->
                                   value (_gen_bind_276 _gen_bind_277))))
                | Effect_Fail  ->
                    (fun (_ : unit)  -> fun (_ : unit -> _)  -> value [])
                | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
               a -> (b -> _) -> _)
         } comp)
      (let rec _term_223 () =
         let rec _factor_224 () =
           call Effect_Decide ()
             (fun _result_225  ->
                if _result_225
                then
                  (_many1_69 ()) >> (fun _i_226  -> value (_toNum_56 _i_226))
                else
                  call Effect_Symbol "("
                    (fun _result_227  ->
                       (_expr_73 ()) >>
                         (fun _j_228  ->
                            call Effect_Symbol ")"
                              (fun _result_229  -> value _j_228))))
            in
         call Effect_Decide ()
           (fun _result_230  ->
              if _result_230
              then
                (_factor_224 ()) >>
                  (fun _i_231  ->
                     call Effect_Symbol "*"
                       (fun _result_232  ->
                          (_term_223 ()) >>
                            (fun _j_233  -> value (_i_231 * _j_233))))
              else _factor_224 ())
          in
       call Effect_Decide ()
         (fun _result_234  ->
            if _result_234
            then
              (fun comp  ->
                 handler
                   {
                     value_clause =
                       (fun _i_235  ->
                          value
                            (fun _s_236  ->
                               match _s_236 with
                               | [] ->
                                   call Effect_Fail ()
                                     (fun _result_237  ->
                                        value (_absurd_1 _result_237))
                               | _x_239::_xs_238 ->
                                   if "+" = _x_239
                                   then
                                     (let rec _newvar_279 () =
                                        let rec _term_74 () =
                                          let rec _factor_75 () =
                                            call Effect_Decide ()
                                              (fun _result_300  ->
                                                 if _result_300
                                                 then
                                                   (_many1_69 ()) >>
                                                     (fun _i_77  ->
                                                        value
                                                          (_toNum_56 _i_77))
                                                 else
                                                   call Effect_Symbol "("
                                                     (fun _result_297  ->
                                                        (_expr_73 ()) >>
                                                          (fun _j_79  ->
                                                             call
                                                               Effect_Symbol
                                                               ")"
                                                               (fun
                                                                  _result_294
                                                                   ->
                                                                  value _j_79))))
                                             in
                                          call Effect_Decide ()
                                            (fun _result_291  ->
                                               if _result_291
                                               then
                                                 (_factor_75 ()) >>
                                                   (fun _i_82  ->
                                                      call Effect_Symbol "*"
                                                        (fun _result_288  ->
                                                           (_term_74 ()) >>
                                                             (fun _j_84  ->
                                                                value
                                                                  (_i_82 *
                                                                    _j_84))))
                                               else _factor_75 ())
                                           in
                                        call Effect_Decide ()
                                          (fun _result_301  ->
                                             if _result_301
                                             then
                                               (fun comp  ->
                                                  handler
                                                    {
                                                      value_clause =
                                                        (fun _i_404  ->
                                                           value
                                                             (fun _s_405  ->
                                                                match _s_405
                                                                with
                                                                | [] ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_406
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_406))
                                                                | _x_408::_xs_407
                                                                    ->
                                                                    if
                                                                    "+" =
                                                                    _x_408
                                                                    then
                                                                    ((fun
                                                                    comp  ->
                                                                    handler
                                                                    {
                                                                    value_clause
                                                                    =
                                                                    (fun
                                                                    _j_410 
                                                                    ->
                                                                    value
                                                                    (let _y_411
                                                                    =
                                                                    _i_235 +
                                                                    (_i_404 +
                                                                    _j_410)
                                                                     in
                                                                    fun
                                                                    _s_412 
                                                                    ->
                                                                    match _s_412
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    value
                                                                    _y_411
                                                                    | 
                                                                    _ ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_413
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_413))));
                                                                    effect_clauses
                                                                    = fun
                                                                    (type a)
                                                                    -> fun
                                                                    (type b)
                                                                    ->
                                                                    fun
                                                                    (x :
                                                                    (a,
                                                                    b) effect)
                                                                     ->
                                                                    (match x
                                                                    with
                                                                    | 
                                                                    Effect_Symbol
                                                                     ->
                                                                    (fun
                                                                    (_c_415 :
                                                                    string) 
                                                                    ->
                                                                    fun
                                                                    (_k_414 :
                                                                    string ->
                                                                    _)  ->
                                                                    value
                                                                    (fun
                                                                    _s_416 
                                                                    ->
                                                                    match _s_416
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_417
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_417))
                                                                    | 
                                                                    _x_419::_xs_418
                                                                    ->
                                                                    if
                                                                    _c_415 =
                                                                    _x_419
                                                                    then
                                                                    (_k_414
                                                                    _x_419)
                                                                    >>
                                                                    ((fun
                                                                    _gen_bind_420
                                                                     ->
                                                                    _gen_bind_420
                                                                    _xs_418))
                                                                    else
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_421
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_421))))
                                                                    | 
                                                                    eff' ->
                                                                    (fun arg 
                                                                    ->
                                                                    fun k  ->
                                                                    Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                                    a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
                                                                    } comp)
                                                                    (_expr_73
                                                                    ())) >>
                                                                    ((fun
                                                                    _gen_bind_409
                                                                     ->
                                                                    _gen_bind_409
                                                                    _xs_407))
                                                                    else
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_422
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_422))));
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
                                                                  (_c_424 :
                                                                    string)
                                                                   ->
                                                                  fun
                                                                    (_k_423 :
                                                                    string ->
                                                                    _)  ->
                                                                    value
                                                                    (fun
                                                                    _s_425 
                                                                    ->
                                                                    match _s_425
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_426
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_426))
                                                                    | 
                                                                    _x_428::_xs_427
                                                                    ->
                                                                    if
                                                                    _c_424 =
                                                                    _x_428
                                                                    then
                                                                    (_k_423
                                                                    _x_428)
                                                                    >>
                                                                    ((fun
                                                                    _gen_bind_429
                                                                     ->
                                                                    _gen_bind_429
                                                                    _xs_427))
                                                                    else
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_430
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_430))))
                                                           | eff' ->
                                                               (fun arg  ->
                                                                  fun k  ->
                                                                    Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                          a -> (b -> _) -> _)
                                                    } comp) (_term_74 ())
                                             else
                                               ((fun comp  ->
                                                   handler
                                                     {
                                                       value_clause =
                                                         (fun _j_431  ->
                                                            value
                                                              (let _y_432 =
                                                                 _i_235 +
                                                                   _j_431
                                                                  in
                                                               fun _s_433  ->
                                                                 match _s_433
                                                                 with
                                                                 | [] ->
                                                                    value
                                                                    _y_432
                                                                 | _ ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_434
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_434))));
                                                       effect_clauses = fun
                                                         (type a) -> fun
                                                         (type b) ->
                                                         fun
                                                           (x : (a,b) effect)
                                                            ->
                                                           (match x with
                                                            | Effect_Symbol 
                                                                ->
                                                                (fun
                                                                   (_c_436 :
                                                                    string)
                                                                    ->
                                                                   fun
                                                                    (_k_435 :
                                                                    string ->
                                                                    _)  ->
                                                                    value
                                                                    (fun
                                                                    _s_437 
                                                                    ->
                                                                    match _s_437
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_438
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_438))
                                                                    | 
                                                                    _x_440::_xs_439
                                                                    ->
                                                                    if
                                                                    _c_436 =
                                                                    _x_440
                                                                    then
                                                                    (_k_435
                                                                    _x_440)
                                                                    >>
                                                                    ((fun
                                                                    _gen_bind_441
                                                                     ->
                                                                    _gen_bind_441
                                                                    _xs_439))
                                                                    else
                                                                    call
                                                                    Effect_Fail
                                                                    ()
                                                                    (fun
                                                                    _result_442
                                                                     ->
                                                                    value
                                                                    (_absurd_1
                                                                    _result_442))))
                                                            | eff' ->
                                                                (fun arg  ->
                                                                   fun k  ->
                                                                    Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                           a -> (b -> _) -> _)
                                                     } comp)) (_term_74 ()))
                                         in
                                      _newvar_279 ()) >>
                                       ((fun _gen_bind_240  ->
                                           _gen_bind_240 _xs_238))
                                   else
                                     call Effect_Fail ()
                                       (fun _result_253  ->
                                          value (_absurd_1 _result_253))));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_Symbol  ->
                              (fun (_c_255 : string)  ->
                                 fun (_k_254 : string -> _)  ->
                                   value
                                     (fun _s_256  ->
                                        match _s_256 with
                                        | [] ->
                                            call Effect_Fail ()
                                              (fun _result_257  ->
                                                 value
                                                   (_absurd_1 _result_257))
                                        | _x_259::_xs_258 ->
                                            if _c_255 = _x_259
                                            then
                                              (_k_254 _x_259) >>
                                                ((fun _gen_bind_260  ->
                                                    _gen_bind_260 _xs_258))
                                            else
                                              call Effect_Fail ()
                                                (fun _result_261  ->
                                                   value
                                                     (_absurd_1 _result_261))))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _) -> _)
                   } comp) (_term_223 ())
            else
              ((fun comp  ->
                  handler
                    {
                      value_clause =
                        (fun _y_262  ->
                           value
                             (fun _s_263  ->
                                match _s_263 with
                                | [] -> value _y_262
                                | _ ->
                                    call Effect_Fail ()
                                      (fun _result_264  ->
                                         value (_absurd_1 _result_264))));
                      effect_clauses = fun (type a) -> fun (type b) ->
                        fun (x : (a,b) effect)  ->
                          (match x with
                           | Effect_Symbol  ->
                               (fun (_c_266 : string)  ->
                                  fun (_k_265 : string -> _)  ->
                                    value
                                      (fun _s_267  ->
                                         match _s_267 with
                                         | [] ->
                                             call Effect_Fail ()
                                               (fun _result_268  ->
                                                  value
                                                    (_absurd_1 _result_268))
                                         | _x_270::_xs_269 ->
                                             if _c_266 = _x_270
                                             then
                                               (_k_265 _x_270) >>
                                                 ((fun _gen_bind_271  ->
                                                     _gen_bind_271 _xs_269))
                                             else
                                               call Effect_Fail ()
                                                 (fun _result_272  ->
                                                    value
                                                      (_absurd_1 _result_272))))
                           | eff' ->
                               (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                          a -> (b -> _) -> _)
                    } comp)) (_term_223 ())))
     in
  _newvar_278 () 
let _x_93 = _parseTest_91 () 
