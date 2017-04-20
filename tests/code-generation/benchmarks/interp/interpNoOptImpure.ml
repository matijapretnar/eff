(*
=== GENERATED FROM interpSmall.eff ===
commit SHA: cdd58493d3c35dbe6ccae6de26e33c6d63c76753
=== BEGIN SOURCE ===

external ( + ) : int -> int -> int = "+"
external ( * ) : int -> int -> int = "*"
external ( - ) : int -> int -> int = "-"
external ( ~- ) : int -> int = "~-"
external ( / ) : int -> int -> int = "/"

(******************************************************************************)

type term =
    | Num of int
    | Add of term * term
    | Mul of term * term
    | Sub of term * term
    | Div of term * term

effect DivByZero : unit -> int

let rec interp = function
  | Num b -> b
  | Add (l, r) ->
    let x = interp l in
    let y = interp r in
    x + y
  | Mul (l, r) ->
    let x = interp l in
    let y = interp r in
    x * y
  | Sub (l, r) ->
    let x = interp l in
    let y = interp r in
    x - y
  | Div (l, r) ->
    let y = interp r in
    let x = interp l in
    begin match y with
    | 0 -> #DivByZero ()
    | _ -> x / y
    end

let arithmeticHandler = handler
    | #DivByZero () k ->  -1

(******************************************************************************)

let addCase =
    Add (
        Add (
            Add ((Num 20), (Num 2)),
            Mul ((Num 1), (Num 2))
        ),
        Sub (
            Add ((Num 2), (Num 2)),
            Div ((Num 1), (Num 0))
        )
    );;

let rec createCase n =
    begin match n with
    | 1 -> (Div (Num 100, Num 10))
    | _ -> Add (addCase, (createCase (n - 1)))
    end

let finalCase = createCase 200

let bigTest () =
  with arithmeticHandler handle interp (createCase 200)

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
let _var_1 x = lift_binary (+) x 
let _var_2 x = lift_binary ( * ) x 
let _var_3 x = lift_binary (-) x 
let _var_4 x = lift_unary (~-) x 
let _var_5 x = lift_binary (/) x 
type term =
  | Num of int 
  | Add of (term* term) 
  | Mul of (term* term) 
  | Sub of (term* term) 
  | Div of (term* term) 
type (_,_) effect +=
  | Effect_DivByZero: (unit,int) effect 
let rec _interp_6 _gen_let_rec_function_7 =
  match _gen_let_rec_function_7 with
  | Num _b_8 -> value _b_8
  | Add (_l_9,_r_10) ->
      (_interp_6 _l_9) >>
        ((fun _x_11  ->
            (_interp_6 _r_10) >>
              (fun _y_12  ->
                 (_var_1 _x_11) >> (fun _gen_bind_13  -> _gen_bind_13 _y_12))))
  | Mul (_l_14,_r_15) ->
      (_interp_6 _l_14) >>
        ((fun _x_16  ->
            (_interp_6 _r_15) >>
              (fun _y_17  ->
                 (_var_2 _x_16) >> (fun _gen_bind_18  -> _gen_bind_18 _y_17))))
  | Sub (_l_19,_r_20) ->
      (_interp_6 _l_19) >>
        ((fun _x_21  ->
            (_interp_6 _r_20) >>
              (fun _y_22  ->
                 (_var_3 _x_21) >> (fun _gen_bind_23  -> _gen_bind_23 _y_22))))
  | Div (_l_24,_r_25) ->
      (_interp_6 _r_25) >>
        ((fun _y_26  ->
            (_interp_6 _l_24) >>
              (fun _x_27  ->
                 match _y_26 with
                 | 0 -> (effect Effect_DivByZero) ()
                 | _ ->
                     (_var_5 _x_27) >>
                       ((fun _gen_bind_28  -> _gen_bind_28 _y_26)))))
  
let _arithmeticHandler_29 c =
  handler
    {
      value_clause = (fun _gen_id_par_40  -> value _gen_id_par_40);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_DivByZero  ->
               (fun (() : unit)  ->
                  fun (_k_30 : int -> _ computation)  -> _var_4 1)
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _addCase_31 =
  Add
    ((Add ((Add ((Num 20), (Num 2))), (Mul ((Num 1), (Num 2))))),
      (Sub ((Add ((Num 2), (Num 2))), (Div ((Num 1), (Num 0))))))
  
let rec _createCase_32 _n_33 =
  match _n_33 with
  | 1 -> value (Div ((Num 100), (Num 10)))
  | _ ->
      (((_var_3 _n_33) >> (fun _gen_bind_36  -> _gen_bind_36 1)) >>
         (fun _gen_bind_35  -> _createCase_32 _gen_bind_35))
        >> ((fun _gen_bind_34  -> value (Add (_addCase_31, _gen_bind_34))))
  
let _finalCase_37 = run (_createCase_32 200) 
let _bigTest_38 () =
  _arithmeticHandler_29
    ((_createCase_32 200) >> (fun _gen_bind_39  -> _interp_6 _gen_bind_39))
  
