(*
=== GENERATED FROM loop.eff ===
commit SHA: 503a5108792f58491aa1e035aa42e7cd14c90a93
=== BEGIN SOURCE ===

external ( = ) : int -> int -> bool = "="
external ( < ) : int -> int -> bool = "<"
external ( - ) : int -> int -> int = "-"
external ( + ) : int -> int -> int = "+"

(******************************************************************************)

let rec loop_pure n =
    if n = 0 then
        ()
    else
        loop_pure (n - 1)

let test_pure n =
    loop_pure n

(******************************************************************************)

effect Fail : unit -> empty

let rec loop_latent n =
    if n = 0 then
        ()
    else if n < 0 then
        (match #Fail () with)
    else
        loop_latent (n - 1)

let test_latent n =
    loop_latent n

(******************************************************************************)

effect Incr : unit -> unit

let rec loop_incr n =
    if n = 0 then
        ()
    else
        (#Incr (); loop_incr (n - 1))

let incr_handler = handler
| val y -> (fun x -> x)
| #Incr () k -> (fun x -> k () (x + 1))

let test_incr n =
    (with incr_handler handle loop_incr n) 0

(******************************************************************************)

effect Get: unit -> int
effect Put: int -> unit

let rec loop_state n =
    if n = 0 then
        ()
    else
        (#Put ((#Get ()) + 1); loop_state (n - 1))

let state_handler = handler
| val y -> (fun x -> x)
| #Get () k -> (fun s -> k s s)
| #Put s' k -> (fun _ -> k () s')

let test_state n =
    (with state_handler handle loop_state n) 0

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
let _var_1 x = lift_binary (=) x 
let _var_2 x = lift_binary (<) x 
let _var_3 x = lift_binary (-) x 
let _var_4 x = lift_binary (+) x 
let rec _loop_pure_5 _n_6 =
  ((_var_1 _n_6) >> (fun _gen_bind_8  -> _gen_bind_8 0)) >>
    (fun _gen_bind_7  ->
       match _gen_bind_7 with
       | true  -> value ()
       | false  ->
           ((_var_3 _n_6) >> (fun _gen_bind_10  -> _gen_bind_10 1)) >>
             ((fun _gen_bind_9  -> _loop_pure_5 _gen_bind_9)))
  
let _test_pure_11 _n_12 = _loop_pure_5 _n_12 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _loop_latent_13 _n_14 =
  ((_var_1 _n_14) >> (fun _gen_bind_16  -> _gen_bind_16 0)) >>
    (fun _gen_bind_15  ->
       match _gen_bind_15 with
       | true  -> value ()
       | false  ->
           ((_var_2 _n_14) >> (fun _gen_bind_18  -> _gen_bind_18 0)) >>
             ((fun _gen_bind_17  ->
                 match _gen_bind_17 with
                 | true  ->
                     ((effect Effect_Fail) ()) >>
                       ((fun _gen_bind_19  ->
                           match _gen_bind_19 with | _ -> assert false))
                 | false  ->
                     ((_var_3 _n_14) >> (fun _gen_bind_21  -> _gen_bind_21 1))
                       >>
                       ((fun _gen_bind_20  -> _loop_latent_13 _gen_bind_20)))))
  
let _test_latent_22 _n_23 = _loop_latent_13 _n_23 
type (_,_) effect +=
  | Effect_Incr: (unit,unit) effect 
let rec _loop_incr_24 _n_25 =
  ((_var_1 _n_25) >> (fun _gen_bind_27  -> _gen_bind_27 0)) >>
    (fun _gen_bind_26  ->
       match _gen_bind_26 with
       | true  -> value ()
       | false  ->
           ((effect Effect_Incr) ()) >>
             ((fun _  ->
                 ((_var_3 _n_25) >> (fun _gen_bind_29  -> _gen_bind_29 1)) >>
                   (fun _gen_bind_28  -> _loop_incr_24 _gen_bind_28))))
  
let _incr_handler_30 c =
  handler
    {
      value_clause = (fun _y_36  -> value (fun _x_37  -> value _x_37));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Incr  ->
               (fun (() : unit)  ->
                  fun (_k_31 : unit -> _ computation)  ->
                    value
                      (fun _x_32  ->
                         (_k_31 ()) >>
                           (fun _gen_bind_33  ->
                              ((_var_4 _x_32) >>
                                 (fun _gen_bind_35  -> _gen_bind_35 1))
                                >>
                                (fun _gen_bind_34  ->
                                   _gen_bind_33 _gen_bind_34))))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _test_incr_38 _n_39 =
  (_incr_handler_30 (_loop_incr_24 _n_39)) >>
    (fun _gen_bind_40  -> _gen_bind_40 0)
  
type (_,_) effect +=
  | Effect_Get: (unit,int) effect 
type (_,_) effect +=
  | Effect_Put: (int,unit) effect 
let rec _loop_state_41 _n_42 =
  ((_var_1 _n_42) >> (fun _gen_bind_44  -> _gen_bind_44 0)) >>
    (fun _gen_bind_43  ->
       match _gen_bind_43 with
       | true  -> value ()
       | false  ->
           (((((effect Effect_Get) ()) >>
                (fun _gen_bind_47  -> _var_4 _gen_bind_47))
               >> (fun _gen_bind_46  -> _gen_bind_46 1))
              >> (fun _gen_bind_45  -> (effect Effect_Put) _gen_bind_45))
             >>
             ((fun _  ->
                 ((_var_3 _n_42) >> (fun _gen_bind_49  -> _gen_bind_49 1)) >>
                   (fun _gen_bind_48  -> _loop_state_41 _gen_bind_48))))
  
let _state_handler_50 c =
  handler
    {
      value_clause = (fun _y_57  -> value (fun _x_58  -> value _x_58));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Get  ->
               (fun (() : unit)  ->
                  fun (_k_54 : int -> _ computation)  ->
                    value
                      (fun _s_55  ->
                         (_k_54 _s_55) >>
                           (fun _gen_bind_56  -> _gen_bind_56 _s_55)))
           | Effect_Put  ->
               (fun (_s'_51 : int)  ->
                  fun (_k_52 : unit -> _ computation)  ->
                    value
                      (fun _  ->
                         (_k_52 ()) >>
                           (fun _gen_bind_53  -> _gen_bind_53 _s'_51)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _test_state_59 _n_60 =
  (_state_handler_50 (_loop_state_41 _n_60)) >>
    (fun _gen_bind_61  -> _gen_bind_61 0)
  
