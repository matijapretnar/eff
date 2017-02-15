(*
=== GENERATED FROM queens.eff ===
commit SHA: 0a8185f252df28fb2b1a33ec39799392a1190567
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
;;"End of pervasives"
let _var_1 = (<>) 
let _var_2 = (<) 
let _var_3 = (>) 
let _var_4 = (-) 
let _var_5 = (+) 
let _var_6 = (~-) 
let _absurd_7 _void_8 = match _void_8 with | _ -> assert false 
let _abs_9 _x_10 = if _x_10 < 0 then - _x_10 else _x_10 
let rec _var_13 _xs_14 _ys_15 =
  match _xs_14 with
  | [] -> _ys_15
  | _x_16::_xs_17 -> _x_16 :: (_var_13 _xs_17 _ys_15) 
let _no_attack_20 (_x_21,_y_22) (_x'_23,_y'_24) =
  if _x_21 <> _x'_23
  then
    (if _y_22 <> _y'_24
     then (_abs_9 (_x_21 - _x'_23)) <> (_abs_9 (_y_22 - _y'_24))
     else false)
  else false 
let rec _not_attacked_36 _x'_37 _gen_function_38 =
  match _gen_function_38 with
  | [] -> true
  | _x_39::_xs_40 ->
      if _no_attack_20 _x'_37 _x_39
      then _not_attacked_36 _x'_37 _xs_40
      else false
  
let _available_44 (_number_of_queens_45,_x_46,_qs_47) =
  let rec _loop_48 (_possible_49,_y_50) =
    if _y_50 < 1
    then _possible_49
    else
      if _not_attacked_36 (_x_46, _y_50) _qs_47
      then _loop_48 ((_y_50 :: _possible_49), (_y_50 - 1))
      else _loop_48 (_possible_49, (_y_50 - 1))
     in
  _loop_48 ([], _number_of_queens_45) 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _choose_59 _gen_let_rec_function_60 =
  match _gen_let_rec_function_60 with
  | [] ->
      call Effect_Fail ()
        (fun _result_3  -> value (match _result_3 with | _ -> assert false))
  | _x_62::_xs_63 ->
      call Effect_Decide ()
        (fun _result_6  ->
           if _result_6 then value _x_62 else _choose_59 _xs_63)
  
let _backtrack_65 comp =
  handler
    {
      value_clause =
        (fun _y_71  ->
           value
             (fun _lift_fun_174  -> value ((fun _  -> _y_71) _lift_fun_174)));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_67 : bool -> _)  ->
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
                  fun (_ : unit -> _)  -> value (fun _kf_66  -> _kf_66 ()))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _choose_all_72 comp =
  handler
    {
      value_clause = (fun _x_77  -> value [_x_77]);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_73 : bool -> _)  ->
                    (_k_73 true) >>
                      (fun _gen_bind_75  ->
                         let _gen_bind_74 = _var_13 _gen_bind_75  in
                         (_k_73 false) >>
                           (fun _gen_bind_76  ->
                              value (_gen_bind_74 _gen_bind_76))))
           | Effect_Fail  ->
               (fun (_ : unit)  -> fun (_ : unit -> _)  -> value [])
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b -> _)
                                                                    -> 
                                                                    _)
    } comp
  
let _queens_78 _number_of_queens_79 =
  let rec _place_80 (_x_81,_qs_82) =
    if _x_81 > _number_of_queens_79
    then value _qs_82
    else
      (_choose_59 (_available_44 (_number_of_queens_79, _x_81, _qs_82))) >>
        ((fun _y_85  -> _place_80 ((_x_81 + 1), ((_x_81, _y_85) :: _qs_82))))
     in
  _place_80 (1, []) 
let _queens_one_89 _number_of_queens_90 =
  let rec _newvar_22 (_x_19,_qs_18) =
    if _x_19 > _number_of_queens_90
    then fun _lift_fun_175  -> value ((fun _  -> _qs_18) _lift_fun_175)
    else
      (let rec _newvar_48 _gen_let_rec_function_60 =
         match _gen_let_rec_function_60 with
         | [] -> (fun _kf_68  -> _kf_68 ())
         | _x_62::_xs_63 ->
             (fun _kf_95  ->
                _newvar_22 ((_x_19 + 1), ((_x_19, _x_62) :: _qs_18))
                  (fun ()  -> _newvar_48 _xs_63 _kf_95))
          in
       _newvar_48 (_available_44 (_number_of_queens_90, _x_19, _qs_18)))
     in
  _newvar_22 (1, [])
    (fun ()  ->
       call Effect_Fail () (fun _result_9  -> value (_absurd_7 _result_9)))
  
let _queens_all_93 _number_of_queens_94 =
  let rec _newvar_109 (_x_106,_qs_105) =
    if _x_106 > _number_of_queens_94
    then [_qs_105]
    else
      (let rec _newvar_131 _gen_let_rec_function_60 =
         match _gen_let_rec_function_60 with
         | [] -> []
         | _x_62::_xs_63 ->
             _var_13
               (_newvar_109 ((_x_106 + 1), ((_x_106, _x_62) :: _qs_105)))
               (_newvar_131 _xs_63)
          in
       _newvar_131 (_available_44 (_number_of_queens_94, _x_106, _qs_105)))
     in
  _newvar_109 (1, []) 
