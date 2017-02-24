(*
=== GENERATED FROM flat.eff ===
commit SHA: 39964fd44c01db0e6d99619f0940b04f0a17de99
=== BEGIN SOURCE ===



let absurd void = match void with;;
external ( = ) : 'a -> 'a -> bool = "="
external ( + ) : int -> int -> int = "+"
external ( * ) : int -> int -> int = "*"
external ( - ) : int -> int -> int = "-"
external ( ~-) : int -> int = "~-"
external ( / ) : int -> int -> int = "/"
let rec (@) xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (xs @ ys)

(***********************************
******* The Building Blocks ********
***********************************)

(********************************
* Types
********************************)

type num = int;;
type func = int -> int;;
type loc = int;;
type name = string;;
type env = (string * int) list;;

type term =
    | Num of int
    | Add of (term * term)
    | Mul of (term * term)
    | Sub of (term * term)
    | Div of (term * term)
    | Ref of term
    | Deref of term
    | Assign of (term * term)
    | Var of string
    | App of (termF * term)
    (* | Amb of term list *)
and
  termF =
    | LambdaV of (string * term)
    | LambdaL of (string * term)
    (* | CallCC *)
;;

(********************************
* Effects
********************************)

(* Main variable not found exception *)
effect VarNotFound : unit -> empty;;

(* Error handling *)
(* effect Err : string -> int;; *)
effect Arith_DivByZero : unit -> int;;

(* Nondeterminism *)
(* effect Merge : int list -> int;; *)

(* Environment *)
effect ReadEnv : unit -> env;;
effect InEnv : (env * int) -> int;;
effect SetEnv : env -> env;;

(* Store *)
effect AllocLoc : unit -> loc;;
effect LookupLoc : loc -> int;;
effect UpdateLoc : (loc * int) -> loc;;

(* Output *)
(* effect Write : string -> unit;; *)

(* Continuation *)
(* effect Callcc : term -> int;; *)

(********************************
* Helper methods
********************************)

(* Helper methods for the state *)
let rec lookupState (x, y) =
    match y with
    | [] -> absurd (#VarNotFound ())
    | (x', y) :: lst -> if x = x' then y else lookupState (x, lst);;

let updateState (k, v, env) =
    (k, v) :: env;;

let rec checkLoc (x, env) =
    begin match env with
    | [] -> false
    | (x', y) :: lst -> if x = x' then true else checkLoc (x, lst)
    end
;;

let rec createLoc (i, env) =
    if (checkLoc (i, env)) then
        createLoc ((i+1), env)
    else
        i
;;

let getNewLoc env = createLoc (0, env);;

(* Helper methods for the environment *)
let rec lookupEnv (x, y) =
    match y with
    | [] -> absurd (#VarNotFound ())
    | (x', y) :: lst -> if x = x' then y else lookupState (x, lst);;

let extendEnv (k, v, env) =
    (k, v) :: env;;

(********************************
* Main interpreter method
********************************)


let rec interp a =
    begin match a with
    | Num b -> b
    | Add (l, r) -> let x = (interp l) in
                    let y = (interp r) in 
                    x + y
    | Mul (l, r) -> let x = (interp l) in
                    let y = (interp r) in 
                    x * y
    | Sub (l, r) -> let x = (interp l) in
                    let y = (interp r) in 
                    x - y
    | Div (l, r) -> let r_num = (interp r) in
                    let l_num = (interp l) in 
                    l_num / r_num      
    | Ref x ->
        let x_interp = interp x in
        let x_loc = #AllocLoc () in
        #UpdateLoc (x_loc, x_interp)
    | Deref x ->
        let x_interp = interp x in
        #LookupLoc x_interp
    | Assign (lhs, rhs) ->
        let x_loc = interp lhs in
        let x_interp = interp rhs in
        let _ = #UpdateLoc (x_loc, x_interp) in
        x_interp
    | Var v -> lookupEnv (v, (#ReadEnv ()))
    | App (e1, e2) ->
            let interpFunc  =
                 begin match e1 with        
                 | LambdaV (s, t) ->
                            let envi = (#ReadEnv ()) in
                            (fun v ->
                                let ext = (extendEnv (s, v, envi)) in
                                let ext_2 = #SetEnv ext in
                                let t_res = interp t in 
                                #InEnv (ext_2, t_res)
                            )

                 | LambdaL (s, t) ->
                        let envi = (#ReadEnv ()) in
                        (fun v ->
                          let x_loc = #AllocLoc () in
                          let thunk = #UpdateLoc (x_loc, v); v in
                          let tmp = #UpdateLoc (x_loc, thunk) in
                          let ext = (extendEnv (s, (#LookupLoc x_loc), envi)) in
                          let ext_2 = #SetEnv ext in
                          let t_res = interp t in 
                         #InEnv (ext_2, t_res)
                        )
                 end 
        in
        let e1_interp = (interpFunc) in
        let envi = (#ReadEnv ()) in
        let e2_interp = (interp e2) in
        let envi2 = #SetEnv envi in
        let in_env = (#InEnv (envi2, e2_interp)) in
        e1_interp in_env 
    (* | Amb t -> #Merge (map interp t) *)
    end
;;

let rec interpTopLevel lst results =
    match lst with
    | [] -> results
    | top :: tail ->
        interpTopLevel tail (results @ [(interp top)])

;;

(********************************
* Use effect handler to mimic
* monad transformers
********************************)
(* 
let arithmeticHandler = handler
    | #Arith_DivByZero () k ->  -1 (* (absurd (#DivisionByZero ())) *)

;; *)

let storeHandler = handler
    | val y -> (fun _ -> y)
    | #LookupLoc x k -> (fun s -> k (lookupState (x, s)) s)
    | #UpdateLoc (x, y) k -> (fun s -> k x (updateState (x, y, s)))
    | #AllocLoc () k -> (fun s -> k (getNewLoc s) s)

;;

let environmentHandler = handler
    | val y -> (fun _ -> y)
    | #InEnv (env, s) k -> (fun _ -> k s env)
    | #ReadEnv () k -> (fun env -> k env env)
    | #SetEnv env k -> (fun _ -> k env env)
;;


let environment_store_Handler = handler
    | val y -> (fun _ -> y)
    | #InEnv (env, e) k -> (fun (_,s) -> k e (env,s))
    | #ReadEnv () k -> (fun (env, s) -> k env (env,s))
    | #SetEnv env k -> (fun (_,s) -> k env (env,s))
    | #LookupLoc x k -> (fun (env, s) -> k (lookupState (x, s)) (env, s))
    | #UpdateLoc (x, y) k -> (fun (env, s) -> k x (env,(updateState (x, y, s))))
    | #AllocLoc () k -> (fun (env, s) -> k (getNewLoc s) (env, s))
;;
(*
let outputHandler = handler
    | #Write s k -> k ()
;;

let errorHandler = handler
    | #Err s k -> k 0
;;

let nondeterminismHandler = handler
    | #Merge s k -> k 0
;;

let continuationHandler = handler
    | val y -> (fun _ -> y)
    | #Callcc f k -> (fun k2 -> k (f (fun a -> fun b -> k2 a)) k2)
;;
*)

(********************************
* Big Test
********************************)
 
let lambdaCase =
    LambdaV (
        "a",
        Add (
        (Var "a"),
    Num 22)
                   
    );;

let addCase =
    Add (
        Add (
            Add (
                (Num 20),
                (Num 2)
            ),
            Mul (
                (Num 1),
                (Num 2)
            )
        ),
        Sub (
            Add (
                (Num 2),
                (Num 2)
            ),
            Add (
                (Num 1),
                (Num 2)
            )
        )
    );;

let testCaseA = App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, App (lambdaCase, addCase)))))));;

let testCaseB = App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, testCaseA)))))));;

let testCaseC = App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, testCaseB)))))));;

let testCaseD = App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, App( lambdaCase, testCaseC)))))));;

let rec createCase n =
    begin match n with
    | 1 -> testCaseD
    | _ -> App( lambdaCase, (createCase (n-1)))
    end;;

let finalCase = createCase 200;;

let bigTest () =
    
        (with environment_store_Handler handle (
            interp (finalCase)
        )) ([],[])
(********************************
* Tests
********************************)

(* Simple arithmetic test *)
(* let test1 = interp (Add (Num 5, Num 3));;
assert(test1 = 8);;
*)

(* Division by zero test *)
(* let test2 = with arithmeticHandler handle (
    interp (Div(Num 2, Num 1))
);; *)
(*
assert(test2 = -1);;

(* Statehandler test *)
let test3 = (with storeHandler handle (
    let a = #UpdateLoc (1, 2) in
    #LookupLoc 1
)) [];;
assert(test3 = 2);;


(* Statehandler test *)
let test4 = (with storeHandler handle (
    let _ = interp (Assign (Num 1, Num 2)) in
    interp (Deref (Num 1))
)) [];;
assert(test4 = 2);;

(* (with storeHandler handle (
    let lst = [(Assign (Num 1, Num 2)) ; (Deref (Num 1)) ] in
    interpTopLevel lst []
)) [];; *)

(* Statehandler test *)
let test6 = (with storeHandler handle (
    with arithmeticHandler handle (
        let _ = interp (Assign (Num 1, (Div (Num 4, Num 2)))) in
        interp (Deref (Num 1))
    )
)) [];;
assert(test6 = 2);;

(* Combination of state-like handlers *)
let test7 = (with storeHandler handle (
    (with environmentHandler handle (
        interp (Deref (Var "a"))
    )) [("a", 1)]
)) [(1,7)];;
assert(test7 = 7);;

(* environmentHandler test *)
let test8 = (with environmentHandler handle (
    (* (interpFunc (LambdaV ("a", (Var "a"))) 4) *)
    (* let f = interpFunc (LambdaV ("a", (Var "a"))) interp in
    f 4 *)

    interp (App ((LambdaV ("a", (Var "a"))), (Num 8)))
)) [];;
assert(test8 = 8);;

(* Statehandler test *)
let test9 = (with storeHandler handle (
    let loc = interp (Ref (Num 100)) in
    let loc2 = interp (Ref (Num 101)) in
    interp (Deref (Num loc2))
)) [];;
assert(test9 = 101);;

(* Statehandler test *)
let test10 = (with storeHandler handle (
    let loc = interp (Ref (Num 100)) in
    let loc2 = interp (Ref (Num 101)) in
    interp (Deref (Num loc))
)) [];;
assert(test10 = 100);; *)

(* Big test *)
(* let bigTest =
(with storeHandler handle (
    (with environmentHandler handle (
        interp (
            Add (
                Add (
                    Add (
                        (Num 1),
                        (Num 2)
                    ),
                    Add (
                        (Num 1),
                        (Num 2)
                    )
                ),
                Add (
                    Add (
                        (Num 1),
                        (Num 2)
                    ),
                    Add (
                        (Num 1),
                        (Num 2)
                    )
                )
            )
        )
    )) []
)) [];; *)

(********************************
* END
********************************)

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
let _var_4 x = lift_binary (+) x 
let _var_5 x = lift_binary ( * ) x 
let _var_6 x = lift_binary (-) x 
let _var_7 x = lift_unary (~-) x 
let _var_8 x = lift_binary (/) x 
let rec _var_9 _xs_10 =
  value
    (fun _ys_11  ->
       match _xs_10 with
       | [] -> value _ys_11
       | _x_12::_xs_13 ->
           ((_var_9 _xs_13) >> (fun _gen_bind_15  -> _gen_bind_15 _ys_11)) >>
             ((fun _gen_bind_14  -> value (_x_12 :: _gen_bind_14))))
  
type num = int
type func = int -> int computation
type loc = int
type name = string
type env = (string* int) list
type term =
  | Num of int 
  | Add of (term* term) 
  | Mul of (term* term) 
  | Sub of (term* term) 
  | Div of (term* term) 
  | Ref of term 
  | Deref of term 
  | Assign of (term* term) 
  | Var of string 
  | App of (termF* term) 
and termF =
  | LambdaV of (string* term) 
  | LambdaL of (string* term) 
type (_,_) effect +=
  | Effect_VarNotFound: (unit,unit) effect 
type (_,_) effect +=
  | Effect_Arith_DivByZero: (unit,int) effect 
type (_,_) effect +=
  | Effect_ReadEnv: (unit,env) effect 
type (_,_) effect +=
  | Effect_InEnv: ((env* int),int) effect 
type (_,_) effect +=
  | Effect_SetEnv: (env,env) effect 
type (_,_) effect +=
  | Effect_AllocLoc: (unit,loc) effect 
type (_,_) effect +=
  | Effect_LookupLoc: (loc,int) effect 
type (_,_) effect +=
  | Effect_UpdateLoc: ((loc* int),loc) effect 
let rec _lookupState_16 (_x_17,_y_18) =
  match _y_18 with
  | [] ->
      ((effect Effect_VarNotFound) ()) >>
        ((fun _gen_bind_19  -> _absurd_1 _gen_bind_19))
  | (_x'_20,_y_21)::_lst_22 ->
      ((_var_3 _x_17) >> (fun _gen_bind_24  -> _gen_bind_24 _x'_20)) >>
        ((fun _gen_bind_23  ->
            match _gen_bind_23 with
            | true  -> value _y_21
            | false  -> _lookupState_16 (_x_17, _lst_22)))
  
let _updateState_25 (_k_26,_v_27,_env_28) = value ((_k_26, _v_27) :: _env_28) 
let rec _checkLoc_29 (_x_30,_env_31) =
  match _env_31 with
  | [] -> value false
  | (_x'_32,_y_33)::_lst_34 ->
      ((_var_3 _x_30) >> (fun _gen_bind_36  -> _gen_bind_36 _x'_32)) >>
        ((fun _gen_bind_35  ->
            match _gen_bind_35 with
            | true  -> value true
            | false  -> _checkLoc_29 (_x_30, _lst_34)))
  
let rec _createLoc_37 (_i_38,_env_39) =
  (_checkLoc_29 (_i_38, _env_39)) >>
    (fun _gen_bind_40  ->
       match _gen_bind_40 with
       | true  ->
           ((_var_4 _i_38) >> (fun _gen_bind_42  -> _gen_bind_42 1)) >>
             ((fun _gen_bind_41  -> _createLoc_37 (_gen_bind_41, _env_39)))
       | false  -> value _i_38)
  
let _getNewLoc_43 _env_44 = _createLoc_37 (0, _env_44) 
let rec _lookupEnv_45 (_x_46,_y_47) =
  match _y_47 with
  | [] ->
      ((effect Effect_VarNotFound) ()) >>
        ((fun _gen_bind_48  -> _absurd_1 _gen_bind_48))
  | (_x'_49,_y_50)::_lst_51 ->
      ((_var_3 _x_46) >> (fun _gen_bind_53  -> _gen_bind_53 _x'_49)) >>
        ((fun _gen_bind_52  ->
            match _gen_bind_52 with
            | true  -> value _y_50
            | false  -> _lookupState_16 (_x_46, _lst_51)))
  
let _extendEnv_54 (_k_55,_v_56,_env_57) = value ((_k_55, _v_56) :: _env_57) 
let rec _interp_58 _a_59 =
  match _a_59 with
  | Num _b_60 -> value _b_60
  | Add (_l_61,_r_62) ->
      (_interp_58 _l_61) >>
        ((fun _x_63  ->
            (_interp_58 _r_62) >>
              (fun _y_64  ->
                 (_var_4 _x_63) >> (fun _gen_bind_65  -> _gen_bind_65 _y_64))))
  | Mul (_l_66,_r_67) ->
      (_interp_58 _l_66) >>
        ((fun _x_68  ->
            (_interp_58 _r_67) >>
              (fun _y_69  ->
                 (_var_5 _x_68) >> (fun _gen_bind_70  -> _gen_bind_70 _y_69))))
  | Sub (_l_71,_r_72) ->
      (_interp_58 _l_71) >>
        ((fun _x_73  ->
            (_interp_58 _r_72) >>
              (fun _y_74  ->
                 (_var_6 _x_73) >> (fun _gen_bind_75  -> _gen_bind_75 _y_74))))
  | Div (_l_76,_r_77) ->
      (_interp_58 _r_77) >>
        ((fun _r_num_78  ->
            (_interp_58 _l_76) >>
              (fun _l_num_79  ->
                 (_var_8 _l_num_79) >>
                   (fun _gen_bind_80  -> _gen_bind_80 _r_num_78))))
  | Ref _x_81 ->
      (_interp_58 _x_81) >>
        ((fun _x_interp_82  ->
            ((effect Effect_AllocLoc) ()) >>
              (fun _x_loc_83  ->
                 (effect Effect_UpdateLoc) (_x_loc_83, _x_interp_82))))
  | Deref _x_84 ->
      (_interp_58 _x_84) >>
        ((fun _x_interp_85  -> (effect Effect_LookupLoc) _x_interp_85))
  | Assign (_lhs_86,_rhs_87) ->
      (_interp_58 _lhs_86) >>
        ((fun _x_loc_88  ->
            (_interp_58 _rhs_87) >>
              (fun _x_interp_89  ->
                 ((effect Effect_UpdateLoc) (_x_loc_88, _x_interp_89)) >>
                   (fun _  -> value _x_interp_89))))
  | Var _v_90 ->
      ((effect Effect_ReadEnv) ()) >>
        ((fun _gen_bind_91  -> _lookupEnv_45 (_v_90, _gen_bind_91)))
  | App (_e1_92,_e2_93) ->
      (match _e1_92 with
       | LambdaV (_s_95,_t_96) ->
           ((effect Effect_ReadEnv) ()) >>
             ((fun _envi_97  ->
                 value
                   (fun _v_98  ->
                      (_extendEnv_54 (_s_95, _v_98, _envi_97)) >>
                        (fun _ext_99  ->
                           ((effect Effect_SetEnv) _ext_99) >>
                             (fun _ext_2_100  ->
                                (_interp_58 _t_96) >>
                                  (fun _t_res_101  ->
                                     (effect Effect_InEnv)
                                       (_ext_2_100, _t_res_101)))))))
       | LambdaL (_s_102,_t_103) ->
           ((effect Effect_ReadEnv) ()) >>
             ((fun _envi_104  ->
                 value
                   (fun _v_105  ->
                      ((effect Effect_AllocLoc) ()) >>
                        (fun _x_loc_106  ->
                           (((effect Effect_UpdateLoc) (_x_loc_106, _v_105))
                              >> (fun _  -> value _v_105))
                             >>
                             (fun _thunk_107  ->
                                ((effect Effect_UpdateLoc)
                                   (_x_loc_106, _thunk_107))
                                  >>
                                  (fun _tmp_108  ->
                                     (((effect Effect_LookupLoc) _x_loc_106)
                                        >>
                                        (fun _gen_bind_110  ->
                                           _extendEnv_54
                                             (_s_102, _gen_bind_110,
                                               _envi_104)))
                                       >>
                                       (fun _ext_109  ->
                                          ((effect Effect_SetEnv) _ext_109)
                                            >>
                                            (fun _ext_2_111  ->
                                               (_interp_58 _t_103) >>
                                                 (fun _t_res_112  ->
                                                    (effect Effect_InEnv)
                                                      (_ext_2_111,
                                                        _t_res_112)))))))))))
        >>
        ((fun _interpFunc_94  ->
            let _e1_interp_113 = _interpFunc_94  in
            ((effect Effect_ReadEnv) ()) >>
              (fun _envi_114  ->
                 (_interp_58 _e2_93) >>
                   (fun _e2_interp_115  ->
                      ((effect Effect_SetEnv) _envi_114) >>
                        (fun _envi2_116  ->
                           ((effect Effect_InEnv)
                              (_envi2_116, _e2_interp_115))
                             >>
                             (fun _in_env_117  -> _e1_interp_113 _in_env_117))))))
  
let rec _interpTopLevel_118 _lst_119 =
  value
    (fun _results_120  ->
       match _lst_119 with
       | [] -> value _results_120
       | _top_121::_tail_122 ->
           (_interpTopLevel_118 _tail_122) >>
             ((fun _gen_bind_123  ->
                 ((_var_9 _results_120) >>
                    (fun _gen_bind_125  ->
                       (_interp_58 _top_121) >>
                         (fun _gen_bind_126  -> _gen_bind_125 [_gen_bind_126])))
                   >> (fun _gen_bind_124  -> _gen_bind_123 _gen_bind_124))))
  
let _storeHandler_127 c =
  handler
    {
      value_clause = (fun _y_143  -> value (fun _  -> value _y_143));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_LookupLoc  ->
               (fun (_x_138 : loc)  ->
                  fun (_k_139 : int -> _ computation)  ->
                    value
                      (fun _s_140  ->
                         ((_lookupState_16 (_x_138, _s_140)) >>
                            (fun _gen_bind_142  -> _k_139 _gen_bind_142))
                           >> (fun _gen_bind_141  -> _gen_bind_141 _s_140)))
           | Effect_UpdateLoc  ->
               (fun ((_x_132,_y_133) : (loc* int))  ->
                  fun (_k_134 : loc -> _ computation)  ->
                    value
                      (fun _s_135  ->
                         (_k_134 _x_132) >>
                           (fun _gen_bind_136  ->
                              (_updateState_25 (_x_132, _y_133, _s_135)) >>
                                (fun _gen_bind_137  ->
                                   _gen_bind_136 _gen_bind_137))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_128 : loc -> _ computation)  ->
                    value
                      (fun _s_129  ->
                         ((_getNewLoc_43 _s_129) >>
                            (fun _gen_bind_131  -> _k_128 _gen_bind_131))
                           >> (fun _gen_bind_130  -> _gen_bind_130 _s_129)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _environmentHandler_144 c =
  handler
    {
      value_clause = (fun _y_155  -> value (fun _  -> value _y_155));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_InEnv  ->
               (fun ((_env_151,_s_152) : (env* int))  ->
                  fun (_k_153 : int -> _ computation)  ->
                    value
                      (fun _  ->
                         (_k_153 _s_152) >>
                           (fun _gen_bind_154  -> _gen_bind_154 _env_151)))
           | Effect_ReadEnv  ->
               (fun (() : unit)  ->
                  fun (_k_148 : env -> _ computation)  ->
                    value
                      (fun _env_149  ->
                         (_k_148 _env_149) >>
                           (fun _gen_bind_150  -> _gen_bind_150 _env_149)))
           | Effect_SetEnv  ->
               (fun (_env_145 : env)  ->
                  fun (_k_146 : env -> _ computation)  ->
                    value
                      (fun _  ->
                         (_k_146 _env_145) >>
                           (fun _gen_bind_147  -> _gen_bind_147 _env_145)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _environment_store_Handler_156 c =
  handler
    {
      value_clause = (fun _y_188  -> value (fun _  -> value _y_188));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_InEnv  ->
               (fun ((_env_183,_e_184) : (env* int))  ->
                  fun (_k_185 : int -> _ computation)  ->
                    value
                      (fun (_,_s_186)  ->
                         (_k_185 _e_184) >>
                           (fun _gen_bind_187  ->
                              _gen_bind_187 (_env_183, _s_186))))
           | Effect_ReadEnv  ->
               (fun (() : unit)  ->
                  fun (_k_179 : env -> _ computation)  ->
                    value
                      (fun (_env_180,_s_181)  ->
                         (_k_179 _env_180) >>
                           (fun _gen_bind_182  ->
                              _gen_bind_182 (_env_180, _s_181))))
           | Effect_SetEnv  ->
               (fun (_env_175 : env)  ->
                  fun (_k_176 : env -> _ computation)  ->
                    value
                      (fun (_,_s_177)  ->
                         (_k_176 _env_175) >>
                           (fun _gen_bind_178  ->
                              _gen_bind_178 (_env_175, _s_177))))
           | Effect_LookupLoc  ->
               (fun (_x_169 : loc)  ->
                  fun (_k_170 : int -> _ computation)  ->
                    value
                      (fun (_env_171,_s_172)  ->
                         ((_lookupState_16 (_x_169, _s_172)) >>
                            (fun _gen_bind_174  -> _k_170 _gen_bind_174))
                           >>
                           (fun _gen_bind_173  ->
                              _gen_bind_173 (_env_171, _s_172))))
           | Effect_UpdateLoc  ->
               (fun ((_x_162,_y_163) : (loc* int))  ->
                  fun (_k_164 : loc -> _ computation)  ->
                    value
                      (fun (_env_165,_s_166)  ->
                         (_k_164 _x_162) >>
                           (fun _gen_bind_167  ->
                              (_updateState_25 (_x_162, _y_163, _s_166)) >>
                                (fun _gen_bind_168  ->
                                   _gen_bind_167 (_env_165, _gen_bind_168)))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_157 : loc -> _ computation)  ->
                    value
                      (fun (_env_158,_s_159)  ->
                         ((_getNewLoc_43 _s_159) >>
                            (fun _gen_bind_161  -> _k_157 _gen_bind_161))
                           >>
                           (fun _gen_bind_160  ->
                              _gen_bind_160 (_env_158, _s_159))))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _lambdaCase_189 = LambdaV ("a", (Add ((Var "a"), (Num 22)))) 
let _addCase_190 =
  Add
    ((Add ((Add ((Num 20), (Num 2))), (Mul ((Num 1), (Num 2))))),
      (Sub ((Add ((Num 2), (Num 2))), (Add ((Num 1), (Num 2))))))
  
let _testCaseA_191 =
  App
    (_lambdaCase_189,
      (App
         (_lambdaCase_189,
           (App
              (_lambdaCase_189,
                (App
                   (_lambdaCase_189,
                     (App
                        (_lambdaCase_189,
                          (App
                             (_lambdaCase_189,
                               (App (_lambdaCase_189, _addCase_190)))))))))))))
  
let _testCaseB_192 =
  App
    (_lambdaCase_189,
      (App
         (_lambdaCase_189,
           (App
              (_lambdaCase_189,
                (App
                   (_lambdaCase_189,
                     (App
                        (_lambdaCase_189,
                          (App
                             (_lambdaCase_189,
                               (App (_lambdaCase_189, _testCaseA_191)))))))))))))
  
let _testCaseC_193 =
  App
    (_lambdaCase_189,
      (App
         (_lambdaCase_189,
           (App
              (_lambdaCase_189,
                (App
                   (_lambdaCase_189,
                     (App
                        (_lambdaCase_189,
                          (App
                             (_lambdaCase_189,
                               (App (_lambdaCase_189, _testCaseB_192)))))))))))))
  
let _testCaseD_194 =
  App
    (_lambdaCase_189,
      (App
         (_lambdaCase_189,
           (App
              (_lambdaCase_189,
                (App
                   (_lambdaCase_189,
                     (App
                        (_lambdaCase_189,
                          (App
                             (_lambdaCase_189,
                               (App (_lambdaCase_189, _testCaseC_193)))))))))))))
  
let rec _createCase_195 _n_196 =
  match _n_196 with
  | 1 -> value _testCaseD_194
  | _ ->
      (((_var_6 _n_196) >> (fun _gen_bind_199  -> _gen_bind_199 1)) >>
         (fun _gen_bind_198  -> _createCase_195 _gen_bind_198))
        >>
        ((fun _gen_bind_197  -> value (App (_lambdaCase_189, _gen_bind_197))))
  
let _finalCase_200 = run (_createCase_195 200) 
let _bigTest_201 () =
  (_environment_store_Handler_156 (_interp_58 _finalCase_200)) >>
    (fun _gen_bind_202  -> _gen_bind_202 ([], []))
  
