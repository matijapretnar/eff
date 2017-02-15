(*
=== GENERATED FROM queens.eff ===
commit SHA: 44790e645f74dcf79df121c124dfae464c4fcfe3
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

let rec choose = function
  | [] -> (match (#Fail ()) with)
  | x::xs -> if #Decide () then x else choose xs

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

let queens_one number_of_queens =
  (with backtrack handle queens number_of_queens) (fun () -> (absurd (#Fail ())))

let queens_all number_of_queens =
  with choose_all handle queens number_of_queens

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
let _var_1 x = lift_binary (<>) x 
let _var_2 x = lift_binary (<) x 
let _var_3 x = lift_binary (>) x 
let _var_4 x = lift_binary (-) x 
let _var_5 x = lift_binary (+) x 
let _var_6 x = lift_unary (~-) x 
let _absurd_7 _void_8 = match _void_8 with | _ -> assert false 
let _abs_9 _x_10 =
  ((_var_2 _x_10) >> (fun _gen_bind_12  -> _gen_bind_12 0)) >>
    (fun _gen_bind_11  ->
       match _gen_bind_11 with
       | true  -> _var_6 _x_10
       | false  -> value _x_10)
  
let rec _var_13 _xs_14 =
  value
    (fun _ys_15  ->
       match _xs_14 with
       | [] -> value _ys_15
       | _x_16::_xs_17 ->
           ((_var_13 _xs_17) >> (fun _gen_bind_19  -> _gen_bind_19 _ys_15))
             >> ((fun _gen_bind_18  -> value (_x_16 :: _gen_bind_18))))
  
let _no_attack_20 (_x_21,_y_22) =
  value
    (fun (_x'_23,_y'_24)  ->
       ((_var_1 _x_21) >> (fun _gen_bind_26  -> _gen_bind_26 _x'_23)) >>
         (fun _gen_bind_25  ->
            match _gen_bind_25 with
            | true  ->
                ((_var_1 _y_22) >> (fun _gen_bind_28  -> _gen_bind_28 _y'_24))
                  >>
                  ((fun _gen_bind_27  ->
                      match _gen_bind_27 with
                      | true  ->
                          ((((_var_4 _x_21) >>
                               (fun _gen_bind_32  -> _gen_bind_32 _x'_23))
                              >> (fun _gen_bind_31  -> _abs_9 _gen_bind_31))
                             >> (fun _gen_bind_30  -> _var_1 _gen_bind_30))
                            >>
                            ((fun _gen_bind_29  ->
                                (((_var_4 _y_22) >>
                                    (fun _gen_bind_35  -> _gen_bind_35 _y'_24))
                                   >>
                                   (fun _gen_bind_34  -> _abs_9 _gen_bind_34))
                                  >>
                                  (fun _gen_bind_33  ->
                                     _gen_bind_29 _gen_bind_33)))
                      | false  -> value false))
            | false  -> value false))
  
let rec _not_attacked_36 _x'_37 =
  value
    (fun _gen_function_38  ->
       match _gen_function_38 with
       | [] -> value true
       | _x_39::_xs_40 ->
           ((_no_attack_20 _x'_37) >>
              (fun _gen_bind_42  -> _gen_bind_42 _x_39))
             >>
             ((fun _gen_bind_41  ->
                 match _gen_bind_41 with
                 | true  ->
                     (_not_attacked_36 _x'_37) >>
                       ((fun _gen_bind_43  -> _gen_bind_43 _xs_40))
                 | false  -> value false)))
  
let _available_44 (_number_of_queens_45,_x_46,_qs_47) =
  let rec _loop_48 (_possible_49,_y_50) =
    ((_var_2 _y_50) >> (fun _gen_bind_52  -> _gen_bind_52 1)) >>
      (fun _gen_bind_51  ->
         match _gen_bind_51 with
         | true  -> value _possible_49
         | false  ->
             ((_not_attacked_36 (_x_46, _y_50)) >>
                (fun _gen_bind_54  -> _gen_bind_54 _qs_47))
               >>
               ((fun _gen_bind_53  ->
                   match _gen_bind_53 with
                   | true  ->
                       ((_var_4 _y_50) >>
                          (fun _gen_bind_56  -> _gen_bind_56 1))
                         >>
                         ((fun _gen_bind_55  ->
                             _loop_48 ((_y_50 :: _possible_49), _gen_bind_55)))
                   | false  ->
                       ((_var_4 _y_50) >>
                          (fun _gen_bind_58  -> _gen_bind_58 1))
                         >>
                         ((fun _gen_bind_57  ->
                             _loop_48 (_possible_49, _gen_bind_57))))))
     in
  _loop_48 ([], _number_of_queens_45) 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _choose_59 _gen_let_rec_function_60 =
  match _gen_let_rec_function_60 with
  | [] ->
      ((effect Effect_Fail) ()) >>
        ((fun _gen_bind_61  -> match _gen_bind_61 with | _ -> assert false))
  | _x_62::_xs_63 ->
      ((effect Effect_Decide) ()) >>
        ((fun _gen_bind_64  ->
            match _gen_bind_64 with
            | true  -> value _x_62
            | false  -> _choose_59 _xs_63))
  
let _backtrack_65 c =
  handler
    {
      value_clause = (fun _y_71  -> value (fun _  -> value _y_71));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_67 : bool -> _ computation)  ->
                    value
                      (fun _kf_68  ->
                         (_k_67 true) >>
                           (fun _gen_bind_69  ->
                              _gen_bind_69
                                (fun ()  ->
                                   (_k_67 false) >>
                                     (fun _gen_bind_70  ->
                                        _gen_bind_70 _kf_68)))))
           | Effect_Fail  ->
               (fun (_ : unit)  ->
                  fun (_ : unit -> _ computation)  ->
                    value (fun _kf_66  -> _kf_66 ()))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _choose_all_72 c =
  handler
    {
      value_clause = (fun _x_77  -> value [_x_77]);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_73 : bool -> _ computation)  ->
                    ((_k_73 true) >>
                       (fun _gen_bind_75  -> _var_13 _gen_bind_75))
                      >>
                      (fun _gen_bind_74  ->
                         (_k_73 false) >>
                           (fun _gen_bind_76  -> _gen_bind_74 _gen_bind_76)))
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
  
let _queens_78 _number_of_queens_79 =
  let rec _place_80 (_x_81,_qs_82) =
    ((_var_3 _x_81) >>
       (fun _gen_bind_84  -> _gen_bind_84 _number_of_queens_79))
      >>
      (fun _gen_bind_83  ->
         match _gen_bind_83 with
         | true  -> value _qs_82
         | false  ->
             ((_available_44 (_number_of_queens_79, _x_81, _qs_82)) >>
                (fun _gen_bind_86  -> _choose_59 _gen_bind_86))
               >>
               ((fun _y_85  ->
                   ((_var_5 _x_81) >> (fun _gen_bind_88  -> _gen_bind_88 1))
                     >>
                     (fun _gen_bind_87  ->
                        _place_80 (_gen_bind_87, ((_x_81, _y_85) :: _qs_82))))))
     in
  _place_80 (1, []) 
let _queens_one_89 _number_of_queens_90 =
  (_backtrack_65 (_queens_78 _number_of_queens_90)) >>
    (fun _gen_bind_91  ->
       _gen_bind_91
         (fun ()  ->
            ((effect Effect_Fail) ()) >>
              (fun _gen_bind_92  -> _absurd_7 _gen_bind_92)))
  
let _queens_all_93 _number_of_queens_94 =
  _choose_all_72 (_queens_78 _number_of_queens_94) 
