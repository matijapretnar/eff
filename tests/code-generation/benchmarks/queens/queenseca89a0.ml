(*
=== GENERATED FROM queens.eff ===
=== BEGIN SOURCE ===

external ( <> ) : 'a -> 'a -> bool = "<>"
external ( - ) : int -> int -> int = "-"
external ( + ) : int -> int -> int = "+"
external ( < ) : 'a -> 'a -> bool = "<"
external ( > ) : 'a -> 'a -> bool = ">"
external ( ~- ) : int -> int = "~-"

let abs x = if x < 0 then -x else x

let rec (@) xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (xs @ ys)

(******************************************************************************)

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec forall_no_attack (x, y) = function
  | [] -> true
  | (x', y') :: xs -> if no_attack (x, y) (x', y') then forall_no_attack (x, y) xs else false

let available number_of_queens x qs =
  let rec loop possible y =
    if y < 1 then
      possible
    else if forall_no_attack (x, y) qs then
      loop (y :: possible) (y - 1)
    else
      loop possible (y - 1)
  in
  loop [] number_of_queens

(******************************************************************************)

effect Decide : unit -> bool
effect Fail : unit -> empty

let rec choose = function
  | [] -> (match (#Fail ()) with)
  | x::xs -> if #Decide () then x else choose xs

(******************************************************************************)

let queens number_of_queens =
  let rec place x qs =
    if x > number_of_queens then qs else
      let y = choose (available number_of_queens x qs) in
      place (x + 1) ((x, y) :: qs)
  in
  place 1 []

let queens_one number_of_queens =
  handle queens number_of_queens with
  | #Decide _ k ->
      handle k true with
      | #Fail _ _ -> k false

let queens_all number_of_queens =
  handle queens number_of_queens with
  | val x -> [x]
  | #Decide _ k -> k true @ k false
  | #Fail _ _ -> []
=== END SOURCE ===
*)

type ('eff_arg,'eff_res) effect = ..
type 'a computation =
  | Value: 'a -> 'a computation 
  | Call: ('eff_arg,'eff_res) effect* 'eff_arg* ('eff_res -> 'a computation)
  -> 'a computation 
type ('a,'b) value_clause = 'a -> 'b computation
type ('a,'b) finally_clause = 'a -> 'b computation
type ('eff_arg,'eff_res,'b) effect_clauses =
  ('eff_arg,'eff_res) effect ->
    'eff_arg -> ('eff_res -> 'b computation) -> 'b computation
type ('a,'b,'c) handler =
  {
  value_clause: ('a,'b) value_clause ;
  finally_clause: ('b,'c) finally_clause ;
  effect_clauses: 'eff_arg 'eff_res . ('eff_arg,'eff_res,'b) effect_clauses }
let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> (k y) >> f))) 
let rec handle (h : ('a,'b,'c) handler) (c : 'a computation) =
  (let rec handler =
     function
     | Value x -> h.value_clause x
     | Call (eff,arg,k) ->
         let clause = h.effect_clauses eff  in
         clause arg (fun y  -> handler (k y))
      in
   (handler c) >> h.finally_clause : 'c computation)
  
let value (x : 'a) = (Value x : 'a computation) 
let call (eff : ('a,'b) effect) (arg : 'a) (cont : 'b -> 'c computation) =
  (Call (eff, arg, cont) : 'c computation) 
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
;;value "End of pervasives"
let _var_1 = (<>) 
let _var_2 = (-) 
let _var_3 = (+) 
let _var_4 = (<) 
let _var_5 = (>) 
let _var_6 = (~-) 
let _abs_7 _x_8 = match _x_8 < 0 with | true  -> - _x_8 | false  -> _x_8 
let rec _var_11 _xs_12 _ys_13 =
  match _xs_12 with
  | [] -> _ys_13
  | _x_14::_xs_15 -> _x_14 :: (_var_11 _xs_15 _ys_13) 
let _no_attack_18 (_x_19,_y_20) (_x'_21,_y'_22) =
  match _x_19 <> _x'_21 with
  | true  ->
      (match _y_20 <> _y'_22 with
       | true  -> (_abs_7 (_x_19 - _x'_21)) <> (_abs_7 (_y_20 - _y'_22))
       | false  -> false)
  | false  -> false 
let rec _forall_no_attack_34 (_x_35,_y_36) _gen_function_37 =
  match _gen_function_37 with
  | [] -> true
  | (_x'_38,_y'_39)::_xs_40 ->
      (match _no_attack_18 (_x_35, _y_36) (_x'_38, _y'_39) with
       | true  -> _forall_no_attack_34 (_x_35, _y_36) _xs_40
       | false  -> false)
  
let _available_44 _number_of_queens_45 _x_46 _qs_47 =
  let rec _loop_48 _possible_49 _y_50 =
    match _y_50 < 1 with
    | true  -> _possible_49
    | false  ->
        (match _forall_no_attack_34 (_x_46, _y_50) _qs_47 with
         | true  -> _loop_48 (_y_50 :: _possible_49) (_y_50 - 1)
         | false  -> _loop_48 _possible_49 (_y_50 - 1))
     in
  _loop_48 [] _number_of_queens_45 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _choose_62 _gen_let_rec_function_63 =
  match _gen_let_rec_function_63 with
  | [] ->
      call Effect_Fail ()
        (fun _result_3  -> value (match _result_3 with | _ -> assert false))
  | _x_65::_xs_66 ->
      call Effect_Decide ()
        (fun _result_6  ->
           match _result_6 with
           | true  -> value _x_65
           | false  -> _choose_62 _xs_66)
  
let _queens_68 _number_of_queens_69 =
  let rec _place_70 _x_71 _qs_72 =
    match _x_71 > _number_of_queens_69 with
    | true  -> value _qs_72
    | false  ->
        (_choose_62 (_available_44 _number_of_queens_69 _x_71 _qs_72)) >>
          ((fun _y_75  -> _place_70 (_x_71 + 1) ((_x_71, _y_75) :: _qs_72)))
     in
  _place_70 1 [] 
let _queens_one_83 _number_of_queens_84 =
  let rec _place_8 _x_9 _qs_10 =
    match _x_9 > _number_of_queens_84 with
    | true  -> value _qs_10
    | false  ->
        (_choose_62 (_available_44 _number_of_queens_84 _x_9 _qs_10)) >>
          ((fun _y_11  -> _place_8 (_x_9 + 1) ((_x_9, _y_11) :: _qs_10)))
     in
  handle
    {
      value_clause = (fun _gen_id_par_89  -> value _gen_id_par_89);
      finally_clause = (fun _gen_id_par_88  -> value _gen_id_par_88);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_85 : bool -> _ computation)  ->
                    handle
                      {
                        value_clause =
                          (fun _gen_id_par_87  -> value _gen_id_par_87);
                        finally_clause =
                          (fun _gen_id_par_86  -> value _gen_id_par_86);
                        effect_clauses = fun (type a) -> fun (type b) ->
                          fun (x : (a,b) effect)  ->
                            (match x with
                             | Effect_Fail  ->
                                 (fun (_ : unit)  ->
                                    fun (_ : unit -> _ computation)  ->
                                      _k_85 false)
                             | eff' ->
                                 (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                            a -> (b -> _ computation) -> _ computation)
                      } (_k_85 true))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } (_place_8 1 [])
  
let _queens_all_90 _number_of_queens_91 =
  let rec _place_14 _x_15 _qs_16 =
    match _x_15 > _number_of_queens_91 with
    | true  -> value _qs_16
    | false  ->
        (_choose_62 (_available_44 _number_of_queens_91 _x_15 _qs_16)) >>
          ((fun _y_17  -> _place_14 (_x_15 + 1) ((_x_15, _y_17) :: _qs_16)))
     in
  handle
    {
      value_clause = (fun _x_97  -> value [_x_97]);
      finally_clause = (fun _gen_id_par_96  -> value _gen_id_par_96);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_92 : bool -> _ computation)  ->
                    let _gen_bind_93 =
                      run
                        ((_k_92 true) >>
                           (fun _gen_bind_94  -> value (_var_11 _gen_bind_94)))
                       in
                    (_k_92 false) >>
                      (* THIS IS THE ONLY LINE THAT NEEDS TO BE CHANGED *)
                      (* (fun _gen_bind_95  -> _gen_bind_93 _gen_bind_95)) *)
                      (fun _gen_bind_95  -> value (_gen_bind_93 _gen_bind_95)))
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
    } (_place_14 1 [])
