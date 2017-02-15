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
       | _x_7::_xs_8 ->
           ((_var_4 _xs_8) >> (fun _gen_bind_10  -> _gen_bind_10 _ys_6)) >>
             ((fun _gen_bind_9  -> value (_x_7 :: _gen_bind_9))))
  
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
                    ((effect Effect_Fail) ()) >>
                      ((fun _gen_bind_28  -> _absurd_1 _gen_bind_28))));
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
                             (_k_15
                                (fun ()  ->
                                   ((effect Effect_Fail) ()) >>
                                     (fun _gen_bind_18  ->
                                        _absurd_1 _gen_bind_18)))
                               >> ((fun _gen_bind_17  -> _gen_bind_17 []))
                         | _x_19::_xs_20 ->
                             ((_var_3 _c_14) >>
                                (fun _gen_bind_22  -> _gen_bind_22 _x_19))
                               >>
                               ((fun _gen_bind_21  ->
                                   match _gen_bind_21 with
                                   | true  ->
                                       (_k_15 (fun ()  -> value _x_19)) >>
                                         ((fun _gen_bind_23  ->
                                             _gen_bind_23 _xs_20))
                                   | false  ->
                                       (_k_15
                                          (fun ()  ->
                                             ((effect Effect_Fail) ()) >>
                                               (fun _gen_bind_25  ->
                                                  _absurd_1 _gen_bind_25)))
                                         >>
                                         ((fun _gen_bind_24  ->
                                             _gen_bind_24 _s_16))))))
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
                    ((_k_30 true) >>
                       (fun _gen_bind_32  -> _var_4 _gen_bind_32))
                      >>
                      (fun _gen_bind_31  ->
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
                    (fun c  ->
                       handler
                         {
                           value_clause =
                             (fun _gen_id_par_101  -> value _gen_id_par_101);
                           effect_clauses = fun (type a) -> fun (type b) ->
                             fun (x : (a,b) effect)  ->
                               (match x with
                                | Effect_Fail  ->
                                    (fun (_ : unit)  ->
                                       fun (_ : unit -> _ computation)  ->
                                         _k_36 false)
                                | eff' ->
                                    (fun arg  ->
                                       fun k  -> Call (eff', arg, k)) : 
                               a -> (b -> _ computation) -> _ computation)
                         } c) (_k_36 true))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _createNumber_37 (_prev_38,_num_39) =
  (((_var_12 _prev_38) >> (fun _gen_bind_42  -> _gen_bind_42 10)) >>
     (fun _gen_bind_41  -> _var_11 _gen_bind_41))
    >> (fun _gen_bind_40  -> _gen_bind_40 _num_39)
  
let rec _parseNum_43 (_l_44,_v_45) =
  match _l_44 with
  | [] -> value _v_45
  | _x_46::_xs_47 ->
      (match _x_46 with
       | "0" ->
           (_createNumber_37 (_v_45, 0)) >>
             ((fun _gen_bind_48  -> _parseNum_43 (_xs_47, _gen_bind_48)))
       | "1" ->
           (_createNumber_37 (_v_45, 1)) >>
             ((fun _gen_bind_49  -> _parseNum_43 (_xs_47, _gen_bind_49)))
       | "2" ->
           (_createNumber_37 (_v_45, 2)) >>
             ((fun _gen_bind_50  -> _parseNum_43 (_xs_47, _gen_bind_50)))
       | "3" ->
           (_createNumber_37 (_v_45, 3)) >>
             ((fun _gen_bind_51  -> _parseNum_43 (_xs_47, _gen_bind_51)))
       | "4" ->
           (_createNumber_37 (_v_45, 4)) >>
             ((fun _gen_bind_52  -> _parseNum_43 (_xs_47, _gen_bind_52)))
       | "5" ->
           (_createNumber_37 (_v_45, 5)) >>
             ((fun _gen_bind_53  -> _parseNum_43 (_xs_47, _gen_bind_53)))
       | "6" ->
           (_createNumber_37 (_v_45, 6)) >>
             ((fun _gen_bind_54  -> _parseNum_43 (_xs_47, _gen_bind_54)))
       | "7" ->
           (_createNumber_37 (_v_45, 7)) >>
             ((fun _gen_bind_55  -> _parseNum_43 (_xs_47, _gen_bind_55)))
       | "8" ->
           (_createNumber_37 (_v_45, 8)) >>
             ((fun _gen_bind_56  -> _parseNum_43 (_xs_47, _gen_bind_56)))
       | "9" ->
           (_createNumber_37 (_v_45, 9)) >>
             ((fun _gen_bind_57  -> _parseNum_43 (_xs_47, _gen_bind_57))))
  
let rec _toNum_58 _l_59 = _parseNum_43 (_l_59, 0) 
let _digit_60 () =
  _backtrack_35
    (let _nums_61 = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]  in
     let rec _checkNums_62 _n_63 =
       match _n_63 with
       | [] ->
           ((effect Effect_Fail) ()) >>
             ((fun _gen_bind_64  -> _absurd_1 _gen_bind_64))
       | _x_65::_xs_66 ->
           ((effect Effect_Decide) ()) >>
             ((fun _gen_bind_67  ->
                 match _gen_bind_67 with
                 | true  ->
                     ((effect Effect_Symbol) _x_65) >>
                       ((fun _gen_bind_68  -> _gen_bind_68 ()))
                 | false  -> _checkNums_62 _xs_66))
        in
     _checkNums_62 _nums_61)
  
let rec _many_69 _m_70 =
  ((effect Effect_Decide) ()) >>
    (fun _gen_bind_71  ->
       match _gen_bind_71 with | true  -> _m_70 () | false  -> value [])
  
let rec _many1_72 () =
  (_digit_60 ()) >>
    (fun _x_73  ->
       (_many_69 _many1_72) >>
         (fun _xs_74  ->
            (_var_4 [_x_73]) >> (fun _gen_bind_75  -> _gen_bind_75 _xs_74)))
  
let rec _expr_76 () =
  let rec _term_77 () =
    let rec _factor_78 () =
      ((effect Effect_Decide) ()) >>
        (fun _gen_bind_79  ->
           match _gen_bind_79 with
           | true  -> (_many1_72 ()) >> ((fun _i_80  -> _toNum_58 _i_80))
           | false  ->
               (((effect Effect_Symbol) "(") >>
                  (fun _gen_bind_82  -> _gen_bind_82 ()))
                 >>
                 ((fun _p_81  ->
                     (_expr_76 ()) >>
                       (fun _j_83  ->
                          (((effect Effect_Symbol) ")") >>
                             (fun _gen_bind_85  -> _gen_bind_85 ()))
                            >> (fun _p_84  -> value _j_83)))))
       in
    ((effect Effect_Decide) ()) >>
      (fun _gen_bind_86  ->
         match _gen_bind_86 with
         | true  ->
             (_factor_78 ()) >>
               ((fun _i_87  ->
                   (((effect Effect_Symbol) "*") >>
                      (fun _gen_bind_89  -> _gen_bind_89 ()))
                     >>
                     (fun _p_88  ->
                        (_term_77 ()) >>
                          (fun _j_90  ->
                             (_var_12 _i_87) >>
                               (fun _gen_bind_91  -> _gen_bind_91 _j_90)))))
         | false  -> _factor_78 ())
     in
  ((effect Effect_Decide) ()) >>
    (fun _gen_bind_92  ->
       match _gen_bind_92 with
       | true  ->
           (_term_77 ()) >>
             ((fun _i_93  ->
                 (((effect Effect_Symbol) "+") >>
                    (fun _gen_bind_95  -> _gen_bind_95 ()))
                   >>
                   (fun _p_94  ->
                      (_expr_76 ()) >>
                        (fun _j_96  ->
                           (_var_11 _i_93) >>
                             (fun _gen_bind_97  -> _gen_bind_97 _j_96)))))
       | false  -> _term_77 ())
  
let _parseTest_98 () =
  _allsols_29
    ((_parse_13 (_expr_76 ())) >>
       (fun _gen_bind_99  ->
          _gen_bind_99 ["4"; "3"; "*"; "("; "3"; "+"; "3"; ")"]))
  
