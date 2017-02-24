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
           value (_x_12 :: (run ((run (_var_9 _xs_13)) _ys_11))))
  
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
  | [] -> call Effect_VarNotFound () (fun _result_3  -> _absurd_1 _result_3)
  | (_x'_20,_y_21)::_lst_22 ->
      (match run ((run (lift_binary (=) _x_17)) _x'_20) with
       | true  -> value _y_21
       | false  -> _lookupState_16 (_x_17, _lst_22))
  
let _updateState_25 (_k_26,_v_27,_env_28) = value ((_k_26, _v_27) :: _env_28) 
let rec _checkLoc_29 (_x_30,_env_31) =
  match _env_31 with
  | [] -> value false
  | (_x'_32,_y_33)::_lst_34 ->
      (match run ((run (lift_binary (=) _x_30)) _x'_32) with
       | true  -> value true
       | false  -> _checkLoc_29 (_x_30, _lst_34))
  
let rec _createLoc_37 (_i_38,_env_39) =
  match run (_checkLoc_29 (_i_38, _env_39)) with
  | true  -> _createLoc_37 ((run ((run (lift_binary (+) _i_38)) 1)), _env_39)
  | false  -> value _i_38 
let _getNewLoc_43 _env_44 = _createLoc_37 (0, _env_44) 
let rec _lookupEnv_45 (_x_46,_y_47) =
  match _y_47 with
  | [] -> call Effect_VarNotFound () (fun _result_6  -> _absurd_1 _result_6)
  | (_x'_49,_y_50)::_lst_51 ->
      (match run ((run (lift_binary (=) _x_46)) _x'_49) with
       | true  -> value _y_50
       | false  -> _lookupState_16 (_x_46, _lst_51))
  
let _extendEnv_54 (_k_55,_v_56,_env_57) = value ((_k_55, _v_56) :: _env_57) 
let rec _interp_58 _a_59 =
  match _a_59 with
  | Num _b_60 -> value _b_60
  | Add (_l_61,_r_62) ->
      (_interp_58 _l_61) >>
        ((fun _x_63  ->
            (_interp_58 _r_62) >>
              (fun _y_64  -> (run (lift_binary (+) _x_63)) _y_64)))
  | Mul (_l_66,_r_67) ->
      (_interp_58 _l_66) >>
        ((fun _x_68  ->
            (_interp_58 _r_67) >>
              (fun _y_69  -> (run (lift_binary ( * ) _x_68)) _y_69)))
  | Sub (_l_71,_r_72) ->
      (_interp_58 _l_71) >>
        ((fun _x_73  ->
            (_interp_58 _r_72) >>
              (fun _y_74  -> (run (lift_binary (-) _x_73)) _y_74)))
  | Div (_l_76,_r_77) ->
      (_interp_58 _r_77) >>
        ((fun _r_num_78  ->
            (_interp_58 _l_76) >>
              (fun _l_num_79  -> (run (lift_binary (/) _l_num_79)) _r_num_78)))
  | Ref _x_81 ->
      (_interp_58 _x_81) >>
        ((fun _x_interp_82  ->
            call Effect_AllocLoc ()
              (fun _result_11  ->
                 call Effect_UpdateLoc (_result_11, _x_interp_82)
                   (fun _result_8  -> value _result_8))))
  | Deref _x_84 ->
      (_interp_58 _x_84) >>
        ((fun _x_interp_85  ->
            call Effect_LookupLoc _x_interp_85
              (fun _result_13  -> value _result_13)))
  | Assign (_lhs_86,_rhs_87) ->
      (_interp_58 _lhs_86) >>
        ((fun _x_loc_88  ->
            (_interp_58 _rhs_87) >>
              (fun _x_interp_89  ->
                 call Effect_UpdateLoc (_x_loc_88, _x_interp_89)
                   (fun _result_16  -> value _x_interp_89))))
  | Var _v_90 ->
      call Effect_ReadEnv ()
        (fun _result_19  -> _lookupEnv_45 (_v_90, _result_19))
  | App (_e1_92,_e2_93) ->
      (match _e1_92 with
       | LambdaV (_s_95,_t_96) ->
           call Effect_ReadEnv ()
             (fun _result_36  ->
                value
                  (fun _v_98  ->
                     call Effect_SetEnv
                       (run (_extendEnv_54 (_s_95, _v_98, _result_36)))
                       (fun _result_33  ->
                          (_interp_58 _t_96) >>
                            (fun _t_res_101  ->
                               call Effect_InEnv (_result_33, _t_res_101)
                                 (fun _result_30  -> value _result_30)))))
       | LambdaL (_s_102,_t_103) ->
           call Effect_ReadEnv ()
             (fun _result_58  ->
                value
                  (fun _v_105  ->
                     call Effect_AllocLoc ()
                       (fun _result_55  ->
                          call Effect_UpdateLoc (_result_55, _v_105)
                            (fun _result_52  ->
                               call Effect_UpdateLoc (_result_55, _v_105)
                                 (fun _result_48  ->
                                    call Effect_LookupLoc _result_55
                                      (fun _result_45  ->
                                         call Effect_SetEnv
                                           (run
                                              (_extendEnv_54
                                                 (_s_102, _result_45,
                                                   _result_58)))
                                           (fun _result_41  ->
                                              (_interp_58 _t_103) >>
                                                (fun _t_res_112  ->
                                                   call Effect_InEnv
                                                     (_result_41, _t_res_112)
                                                     (fun _result_38  ->
                                                        value _result_38))))))))))
        >>
        ((fun _interpFunc_94  ->
            call Effect_ReadEnv ()
              (fun _result_28  ->
                 (_interp_58 _e2_93) >>
                   (fun _e2_interp_115  ->
                      call Effect_SetEnv _result_28
                        (fun _result_25  ->
                           call Effect_InEnv (_result_25, _e2_interp_115)
                             (fun _result_22  -> _interpFunc_94 _result_22))))))
  
let rec _interpTopLevel_118 _lst_119 =
  value
    (fun _results_120  ->
       match _lst_119 with
       | [] -> value _results_120
       | _top_121::_tail_122 ->
           let _gen_bind_123 = run (_interpTopLevel_118 _tail_122)  in
           let _gen_bind_125 = run (_var_9 _results_120)  in
           (_interp_58 _top_121) >>
             ((fun _gen_bind_126  ->
                 (_gen_bind_125 [_gen_bind_126]) >>
                   (fun _gen_bind_124  -> _gen_bind_123 _gen_bind_124))))
  
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
                         (_lookupState_16 (_x_138, _s_140)) >>
                           (fun _gen_bind_142  ->
                              (_k_139 _gen_bind_142) >>
                                (fun _gen_bind_141  -> _gen_bind_141 _s_140))))
           | Effect_UpdateLoc  ->
               (fun ((_x_132,_y_133) : (loc* int))  ->
                  fun (_k_134 : loc -> _ computation)  ->
                    value
                      (fun _s_135  ->
                         (_k_134 _x_132) >>
                           (fun _gen_bind_136  ->
                              _gen_bind_136
                                (run
                                   (_updateState_25 (_x_132, _y_133, _s_135))))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_128 : loc -> _ computation)  ->
                    value
                      (fun _s_129  ->
                         (_k_128 (run (_getNewLoc_43 _s_129))) >>
                           (fun _gen_bind_130  -> _gen_bind_130 _s_129)))
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
                         (_lookupState_16 (_x_169, _s_172)) >>
                           (fun _gen_bind_174  ->
                              (_k_170 _gen_bind_174) >>
                                (fun _gen_bind_173  ->
                                   _gen_bind_173 (_env_171, _s_172)))))
           | Effect_UpdateLoc  ->
               (fun ((_x_162,_y_163) : (loc* int))  ->
                  fun (_k_164 : loc -> _ computation)  ->
                    value
                      (fun (_env_165,_s_166)  ->
                         (_k_164 _x_162) >>
                           (fun _gen_bind_167  ->
                              _gen_bind_167
                                (_env_165,
                                  (run
                                     (_updateState_25
                                        (_x_162, _y_163, _s_166)))))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_157 : loc -> _ computation)  ->
                    value
                      (fun (_env_158,_s_159)  ->
                         (_k_157 (run (_getNewLoc_43 _s_159))) >>
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
      value
        (App
           (_lambdaCase_189,
             (run (_createCase_195 (run ((run (lift_binary (-) _n_196)) 1))))))
  
let _finalCase_200 = run (_createCase_195 200) 
let _bigTest_201 () =
  (let rec _interp_89 _a_59 =
     match _a_59 with
     | Num _b_60 -> value (fun _  -> value _b_60)
     | Add (_l_61,_r_62) ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _x_1327  ->
                      let rec _new_special_var_1328 (_a_1330,_k_val_1329) =
                        match _a_1330 with
                        | Num _b_1331 -> _k_val_1329 _b_1331
                        | Add (_l_1333,_r_1332) ->
                            _new_special_var_1328
                              (_l_1333,
                                (fun _x_1334  ->
                                   _new_special_var_1328
                                     (_r_1332,
                                       (fun _y_1335  ->
                                          _k_val_1329
                                            (run
                                               ((run
                                                   (lift_binary (+) _x_1334))
                                                  _y_1335))))))
                        | Mul (_l_1337,_r_1336) ->
                            _new_special_var_1328
                              (_l_1337,
                                (fun _x_1338  ->
                                   _new_special_var_1328
                                     (_r_1336,
                                       (fun _y_1339  ->
                                          _k_val_1329
                                            (run
                                               ((run
                                                   (lift_binary ( * ) _x_1338))
                                                  _y_1339))))))
                        | Sub (_l_1341,_r_1340) ->
                            _new_special_var_1328
                              (_l_1341,
                                (fun _x_1342  ->
                                   _new_special_var_1328
                                     (_r_1340,
                                       (fun _y_1343  ->
                                          _k_val_1329
                                            (run
                                               ((run
                                                   (lift_binary (-) _x_1342))
                                                  _y_1343))))))
                        | Div (_l_1345,_r_1344) ->
                            _new_special_var_1328
                              (_r_1344,
                                (fun _r_num_1346  ->
                                   _new_special_var_1328
                                     (_l_1345,
                                       (fun _l_num_1347  ->
                                          _k_val_1329
                                            (run
                                               ((run
                                                   (lift_binary (/)
                                                      _l_num_1347))
                                                  _r_num_1346))))))
                        | Ref _x_1348 ->
                            ((fun c  ->
                                handler
                                  {
                                    value_clause =
                                      (fun _x_interp_1349  ->
                                         value
                                           (fun (_env_1351,_s_1350)  ->
                                              ((fun _result_1353  ->
                                                  value
                                                    (fun (_env_1355,_s_1354) 
                                                       ->
                                                       (_k_val_1329
                                                          _result_1353)
                                                         >>
                                                         (fun _gen_bind_1356 
                                                            ->
                                                            _gen_bind_1356
                                                              (_env_1355,
                                                                (run
                                                                   (_updateState_25
                                                                    (_result_1353,
                                                                    _x_interp_1349,
                                                                    _s_1354)))))))
                                                 (run (_getNewLoc_43 _s_1350)))
                                                >>
                                                (fun _gen_bind_1352  ->
                                                   _gen_bind_1352
                                                     (_env_1351, _s_1350))));
                                    effect_clauses = fun (type a) -> fun
                                      (type b) ->
                                      fun (x : (a,b) effect)  ->
                                        (match x with
                                         | Effect_InEnv  ->
                                             (fun
                                                ((_env_1359,_e_1358) :
                                                  (env* int))
                                                 ->
                                                fun
                                                  (_k_1357 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1360)  ->
                                                       (_k_1357 _e_1358) >>
                                                         (fun _gen_bind_1361 
                                                            ->
                                                            _gen_bind_1361
                                                              (_env_1359,
                                                                _s_1360))))
                                         | Effect_ReadEnv  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1362 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1364,_s_1363) 
                                                       ->
                                                       (_k_1362 _env_1364) >>
                                                         (fun _gen_bind_1365 
                                                            ->
                                                            _gen_bind_1365
                                                              (_env_1364,
                                                                _s_1363))))
                                         | Effect_SetEnv  ->
                                             (fun (_env_1367 : env)  ->
                                                fun
                                                  (_k_1366 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1368)  ->
                                                       (_k_1366 _env_1367) >>
                                                         (fun _gen_bind_1369 
                                                            ->
                                                            _gen_bind_1369
                                                              (_env_1367,
                                                                _s_1368))))
                                         | Effect_LookupLoc  ->
                                             (fun (_x_1371 : loc)  ->
                                                fun
                                                  (_k_1370 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1373,_s_1372) 
                                                       ->
                                                       (_lookupState_16
                                                          (_x_1371, _s_1372))
                                                         >>
                                                         (fun _gen_bind_1374 
                                                            ->
                                                            (_k_1370
                                                               _gen_bind_1374)
                                                              >>
                                                              (fun
                                                                 _gen_bind_1375
                                                                  ->
                                                                 _gen_bind_1375
                                                                   (_env_1373,
                                                                    _s_1372)))))
                                         | Effect_UpdateLoc  ->
                                             (fun
                                                ((_x_1378,_y_1377) :
                                                  (loc* int))
                                                 ->
                                                fun
                                                  (_k_1376 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1380,_s_1379) 
                                                       ->
                                                       (_k_1376 _x_1378) >>
                                                         (fun _gen_bind_1381 
                                                            ->
                                                            _gen_bind_1381
                                                              (_env_1380,
                                                                (run
                                                                   (_updateState_25
                                                                    (_x_1378,
                                                                    _y_1377,
                                                                    _s_1379)))))))
                                         | Effect_AllocLoc  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1382 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1384,_s_1383) 
                                                       ->
                                                       (_k_1382
                                                          (run
                                                             (_getNewLoc_43
                                                                _s_1383)))
                                                         >>
                                                         (fun _gen_bind_1385 
                                                            ->
                                                            _gen_bind_1385
                                                              (_env_1384,
                                                                _s_1383))))
                                         | eff' ->
                                             (fun arg  ->
                                                fun k  -> Call (eff', arg, k)) : 
                                        a ->
                                          (b -> _ computation) ->
                                            _ computation)
                                  } c)) (_interp_58 _x_1348)
                        | Deref _x_1386 ->
                            ((fun c  ->
                                handler
                                  {
                                    value_clause =
                                      (fun _vcvar_1388  ->
                                         _k_val_1329 _vcvar_1388);
                                    effect_clauses = fun (type a) -> fun
                                      (type b) ->
                                      fun (x : (a,b) effect)  ->
                                        (match x with
                                         | Effect_InEnv  ->
                                             (fun
                                                ((_env_1391,_e_1390) :
                                                  (env* int))
                                                 ->
                                                fun
                                                  (_k_1389 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1392)  ->
                                                       (_k_1389 _e_1390) >>
                                                         (fun _gen_bind_1393 
                                                            ->
                                                            _gen_bind_1393
                                                              (_env_1391,
                                                                _s_1392))))
                                         | Effect_ReadEnv  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1394 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1396,_s_1395) 
                                                       ->
                                                       (_k_1394 _env_1396) >>
                                                         (fun _gen_bind_1397 
                                                            ->
                                                            _gen_bind_1397
                                                              (_env_1396,
                                                                _s_1395))))
                                         | Effect_SetEnv  ->
                                             (fun (_env_1399 : env)  ->
                                                fun
                                                  (_k_1398 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1400)  ->
                                                       (_k_1398 _env_1399) >>
                                                         (fun _gen_bind_1401 
                                                            ->
                                                            _gen_bind_1401
                                                              (_env_1399,
                                                                _s_1400))))
                                         | Effect_LookupLoc  ->
                                             (fun (_x_1403 : loc)  ->
                                                fun
                                                  (_k_1402 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1405,_s_1404) 
                                                       ->
                                                       (_lookupState_16
                                                          (_x_1403, _s_1404))
                                                         >>
                                                         (fun _gen_bind_1406 
                                                            ->
                                                            (_k_1402
                                                               _gen_bind_1406)
                                                              >>
                                                              (fun
                                                                 _gen_bind_1407
                                                                  ->
                                                                 _gen_bind_1407
                                                                   (_env_1405,
                                                                    _s_1404)))))
                                         | Effect_UpdateLoc  ->
                                             (fun
                                                ((_x_1410,_y_1409) :
                                                  (loc* int))
                                                 ->
                                                fun
                                                  (_k_1408 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1412,_s_1411) 
                                                       ->
                                                       (_k_1408 _x_1410) >>
                                                         (fun _gen_bind_1413 
                                                            ->
                                                            _gen_bind_1413
                                                              (_env_1412,
                                                                (run
                                                                   (_updateState_25
                                                                    (_x_1410,
                                                                    _y_1409,
                                                                    _s_1411)))))))
                                         | Effect_AllocLoc  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1414 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1416,_s_1415) 
                                                       ->
                                                       (_k_1414
                                                          (run
                                                             (_getNewLoc_43
                                                                _s_1415)))
                                                         >>
                                                         (fun _gen_bind_1417 
                                                            ->
                                                            _gen_bind_1417
                                                              (_env_1416,
                                                                _s_1415))))
                                         | eff' ->
                                             (fun arg  ->
                                                fun k  -> Call (eff', arg, k)) : 
                                        a ->
                                          (b -> _ computation) ->
                                            _ computation)
                                  } c))
                              ((_interp_58 _x_1386) >>
                                 (fun _x_interp_1387  ->
                                    (effect Effect_LookupLoc) _x_interp_1387))
                        | Assign (_lhs_1419,_rhs_1418) ->
                            ((fun c  ->
                                handler
                                  {
                                    value_clause =
                                      (fun _vcvar_1422  ->
                                         _k_val_1329 _vcvar_1422);
                                    effect_clauses = fun (type a) -> fun
                                      (type b) ->
                                      fun (x : (a,b) effect)  ->
                                        (match x with
                                         | Effect_InEnv  ->
                                             (fun
                                                ((_env_1425,_e_1424) :
                                                  (env* int))
                                                 ->
                                                fun
                                                  (_k_1423 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1426)  ->
                                                       (_k_1423 _e_1424) >>
                                                         (fun _gen_bind_1427 
                                                            ->
                                                            _gen_bind_1427
                                                              (_env_1425,
                                                                _s_1426))))
                                         | Effect_ReadEnv  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1428 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1430,_s_1429) 
                                                       ->
                                                       (_k_1428 _env_1430) >>
                                                         (fun _gen_bind_1431 
                                                            ->
                                                            _gen_bind_1431
                                                              (_env_1430,
                                                                _s_1429))))
                                         | Effect_SetEnv  ->
                                             (fun (_env_1433 : env)  ->
                                                fun
                                                  (_k_1432 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1434)  ->
                                                       (_k_1432 _env_1433) >>
                                                         (fun _gen_bind_1435 
                                                            ->
                                                            _gen_bind_1435
                                                              (_env_1433,
                                                                _s_1434))))
                                         | Effect_LookupLoc  ->
                                             (fun (_x_1437 : loc)  ->
                                                fun
                                                  (_k_1436 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1439,_s_1438) 
                                                       ->
                                                       (_lookupState_16
                                                          (_x_1437, _s_1438))
                                                         >>
                                                         (fun _gen_bind_1440 
                                                            ->
                                                            (_k_1436
                                                               _gen_bind_1440)
                                                              >>
                                                              (fun
                                                                 _gen_bind_1441
                                                                  ->
                                                                 _gen_bind_1441
                                                                   (_env_1439,
                                                                    _s_1438)))))
                                         | Effect_UpdateLoc  ->
                                             (fun
                                                ((_x_1444,_y_1443) :
                                                  (loc* int))
                                                 ->
                                                fun
                                                  (_k_1442 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1446,_s_1445) 
                                                       ->
                                                       (_k_1442 _x_1444) >>
                                                         (fun _gen_bind_1447 
                                                            ->
                                                            _gen_bind_1447
                                                              (_env_1446,
                                                                (run
                                                                   (_updateState_25
                                                                    (_x_1444,
                                                                    _y_1443,
                                                                    _s_1445)))))))
                                         | Effect_AllocLoc  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1448 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1450,_s_1449) 
                                                       ->
                                                       (_k_1448
                                                          (run
                                                             (_getNewLoc_43
                                                                _s_1449)))
                                                         >>
                                                         (fun _gen_bind_1451 
                                                            ->
                                                            _gen_bind_1451
                                                              (_env_1450,
                                                                _s_1449))))
                                         | eff' ->
                                             (fun arg  ->
                                                fun k  -> Call (eff', arg, k)) : 
                                        a ->
                                          (b -> _ computation) ->
                                            _ computation)
                                  } c))
                              ((_interp_58 _lhs_1419) >>
                                 (fun _x_loc_1420  ->
                                    (_interp_58 _rhs_1418) >>
                                      (fun _x_interp_1421  ->
                                         ((effect Effect_UpdateLoc)
                                            (_x_loc_1420, _x_interp_1421))
                                           >>
                                           (fun _  -> value _x_interp_1421))))
                        | Var _v_1452 ->
                            ((fun c  ->
                                handler
                                  {
                                    value_clause =
                                      (fun _vcvar_1454  ->
                                         _k_val_1329 _vcvar_1454);
                                    effect_clauses = fun (type a) -> fun
                                      (type b) ->
                                      fun (x : (a,b) effect)  ->
                                        (match x with
                                         | Effect_InEnv  ->
                                             (fun
                                                ((_env_1457,_e_1456) :
                                                  (env* int))
                                                 ->
                                                fun
                                                  (_k_1455 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1458)  ->
                                                       (_k_1455 _e_1456) >>
                                                         (fun _gen_bind_1459 
                                                            ->
                                                            _gen_bind_1459
                                                              (_env_1457,
                                                                _s_1458))))
                                         | Effect_ReadEnv  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1460 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1462,_s_1461) 
                                                       ->
                                                       (_k_1460 _env_1462) >>
                                                         (fun _gen_bind_1463 
                                                            ->
                                                            _gen_bind_1463
                                                              (_env_1462,
                                                                _s_1461))))
                                         | Effect_SetEnv  ->
                                             (fun (_env_1465 : env)  ->
                                                fun
                                                  (_k_1464 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1466)  ->
                                                       (_k_1464 _env_1465) >>
                                                         (fun _gen_bind_1467 
                                                            ->
                                                            _gen_bind_1467
                                                              (_env_1465,
                                                                _s_1466))))
                                         | Effect_LookupLoc  ->
                                             (fun (_x_1469 : loc)  ->
                                                fun
                                                  (_k_1468 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1471,_s_1470) 
                                                       ->
                                                       (_lookupState_16
                                                          (_x_1469, _s_1470))
                                                         >>
                                                         (fun _gen_bind_1472 
                                                            ->
                                                            (_k_1468
                                                               _gen_bind_1472)
                                                              >>
                                                              (fun
                                                                 _gen_bind_1473
                                                                  ->
                                                                 _gen_bind_1473
                                                                   (_env_1471,
                                                                    _s_1470)))))
                                         | Effect_UpdateLoc  ->
                                             (fun
                                                ((_x_1476,_y_1475) :
                                                  (loc* int))
                                                 ->
                                                fun
                                                  (_k_1474 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1478,_s_1477) 
                                                       ->
                                                       (_k_1474 _x_1476) >>
                                                         (fun _gen_bind_1479 
                                                            ->
                                                            _gen_bind_1479
                                                              (_env_1478,
                                                                (run
                                                                   (_updateState_25
                                                                    (_x_1476,
                                                                    _y_1475,
                                                                    _s_1477)))))))
                                         | Effect_AllocLoc  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1480 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1482,_s_1481) 
                                                       ->
                                                       (_k_1480
                                                          (run
                                                             (_getNewLoc_43
                                                                _s_1481)))
                                                         >>
                                                         (fun _gen_bind_1483 
                                                            ->
                                                            _gen_bind_1483
                                                              (_env_1482,
                                                                _s_1481))))
                                         | eff' ->
                                             (fun arg  ->
                                                fun k  -> Call (eff', arg, k)) : 
                                        a ->
                                          (b -> _ computation) ->
                                            _ computation)
                                  } c))
                              (((effect Effect_ReadEnv) ()) >>
                                 (fun _gen_bind_1453  ->
                                    _lookupEnv_45 (_v_1452, _gen_bind_1453)))
                        | App (_e1_1485,_e2_1484) ->
                            ((fun c  ->
                                handler
                                  {
                                    value_clause =
                                      (fun _vcvar_1510  ->
                                         _k_val_1329 _vcvar_1510);
                                    effect_clauses = fun (type a) -> fun
                                      (type b) ->
                                      fun (x : (a,b) effect)  ->
                                        (match x with
                                         | Effect_InEnv  ->
                                             (fun
                                                ((_env_1513,_e_1512) :
                                                  (env* int))
                                                 ->
                                                fun
                                                  (_k_1511 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1514)  ->
                                                       (_k_1511 _e_1512) >>
                                                         (fun _gen_bind_1515 
                                                            ->
                                                            _gen_bind_1515
                                                              (_env_1513,
                                                                _s_1514))))
                                         | Effect_ReadEnv  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1516 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1518,_s_1517) 
                                                       ->
                                                       (_k_1516 _env_1518) >>
                                                         (fun _gen_bind_1519 
                                                            ->
                                                            _gen_bind_1519
                                                              (_env_1518,
                                                                _s_1517))))
                                         | Effect_SetEnv  ->
                                             (fun (_env_1521 : env)  ->
                                                fun
                                                  (_k_1520 :
                                                    env -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_,_s_1522)  ->
                                                       (_k_1520 _env_1521) >>
                                                         (fun _gen_bind_1523 
                                                            ->
                                                            _gen_bind_1523
                                                              (_env_1521,
                                                                _s_1522))))
                                         | Effect_LookupLoc  ->
                                             (fun (_x_1525 : loc)  ->
                                                fun
                                                  (_k_1524 :
                                                    int -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1527,_s_1526) 
                                                       ->
                                                       (_lookupState_16
                                                          (_x_1525, _s_1526))
                                                         >>
                                                         (fun _gen_bind_1528 
                                                            ->
                                                            (_k_1524
                                                               _gen_bind_1528)
                                                              >>
                                                              (fun
                                                                 _gen_bind_1529
                                                                  ->
                                                                 _gen_bind_1529
                                                                   (_env_1527,
                                                                    _s_1526)))))
                                         | Effect_UpdateLoc  ->
                                             (fun
                                                ((_x_1532,_y_1531) :
                                                  (loc* int))
                                                 ->
                                                fun
                                                  (_k_1530 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1534,_s_1533) 
                                                       ->
                                                       (_k_1530 _x_1532) >>
                                                         (fun _gen_bind_1535 
                                                            ->
                                                            _gen_bind_1535
                                                              (_env_1534,
                                                                (run
                                                                   (_updateState_25
                                                                    (_x_1532,
                                                                    _y_1531,
                                                                    _s_1533)))))))
                                         | Effect_AllocLoc  ->
                                             (fun (() : unit)  ->
                                                fun
                                                  (_k_1536 :
                                                    loc -> _ computation)
                                                   ->
                                                  value
                                                    (fun (_env_1538,_s_1537) 
                                                       ->
                                                       (_k_1536
                                                          (run
                                                             (_getNewLoc_43
                                                                _s_1537)))
                                                         >>
                                                         (fun _gen_bind_1539 
                                                            ->
                                                            _gen_bind_1539
                                                              (_env_1538,
                                                                _s_1537))))
                                         | eff' ->
                                             (fun arg  ->
                                                fun k  -> Call (eff', arg, k)) : 
                                        a ->
                                          (b -> _ computation) ->
                                            _ computation)
                                  } c))
                              ((match _e1_1485 with
                                | LambdaV (_s_1493,_t_1492) ->
                                    ((effect Effect_ReadEnv) ()) >>
                                      ((fun _envi_1494  ->
                                          value
                                            (fun _v_1495  ->
                                               (_extendEnv_54
                                                  (_s_1493, _v_1495,
                                                    _envi_1494))
                                                 >>
                                                 (fun _ext_1496  ->
                                                    ((effect Effect_SetEnv)
                                                       _ext_1496)
                                                      >>
                                                      (fun _ext_2_1497  ->
                                                         (_interp_58 _t_1492)
                                                           >>
                                                           (fun _t_res_1498 
                                                              ->
                                                              (effect
                                                                 Effect_InEnv)
                                                                (_ext_2_1497,
                                                                  _t_res_1498)))))))
                                | LambdaL (_s_1500,_t_1499) ->
                                    ((effect Effect_ReadEnv) ()) >>
                                      ((fun _envi_1501  ->
                                          value
                                            (fun _v_1502  ->
                                               ((effect Effect_AllocLoc) ())
                                                 >>
                                                 (fun _x_loc_1503  ->
                                                    (((effect
                                                         Effect_UpdateLoc)
                                                        (_x_loc_1503,
                                                          _v_1502))
                                                       >>
                                                       (fun _  ->
                                                          value _v_1502))
                                                      >>
                                                      (fun _thunk_1504  ->
                                                         ((effect
                                                             Effect_UpdateLoc)
                                                            (_x_loc_1503,
                                                              _thunk_1504))
                                                           >>
                                                           (fun _tmp_1505  ->
                                                              (((effect
                                                                   Effect_LookupLoc)
                                                                  _x_loc_1503)
                                                                 >>
                                                                 (fun
                                                                    _gen_bind_1509
                                                                     ->
                                                                    _extendEnv_54
                                                                    (_s_1500,
                                                                    _gen_bind_1509,
                                                                    _envi_1501)))
                                                                >>
                                                                (fun
                                                                   _ext_1506 
                                                                   ->
                                                                   ((effect
                                                                    Effect_SetEnv)
                                                                    _ext_1506)
                                                                    >>
                                                                    (fun
                                                                    _ext_2_1507
                                                                     ->
                                                                    (_interp_58
                                                                    _t_1499)
                                                                    >>
                                                                    (fun
                                                                    _t_res_1508
                                                                     ->
                                                                    (effect
                                                                    Effect_InEnv)
                                                                    (_ext_2_1507,
                                                                    _t_res_1508)))))))))))
                                 >>
                                 (fun _interpFunc_1486  ->
                                    let _e1_interp_1487 = _interpFunc_1486
                                       in
                                    ((effect Effect_ReadEnv) ()) >>
                                      (fun _envi_1488  ->
                                         (_interp_58 _e2_1484) >>
                                           (fun _e2_interp_1489  ->
                                              ((effect Effect_SetEnv)
                                                 _envi_1488)
                                                >>
                                                (fun _envi2_1490  ->
                                                   ((effect Effect_InEnv)
                                                      (_envi2_1490,
                                                        _e2_interp_1489))
                                                     >>
                                                     (fun _in_env_1491  ->
                                                        _e1_interp_1487
                                                          _in_env_1491))))))
                         in
                      _new_special_var_1328
                        (_r_62,
                          (fun _y_1540  ->
                             let _y_1541 =
                               run ((run (lift_binary (+) _x_1327)) _y_1540)
                                in
                             value (fun _  -> value _y_1541))));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1544,_e_1543) : (env* int))  ->
                             fun (_k_1542 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1545)  ->
                                    (_k_1542 _e_1543) >>
                                      (fun _gen_bind_1546  ->
                                         _gen_bind_1546 (_env_1544, _s_1545))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1547 : env -> _ computation)  ->
                               value
                                 (fun (_env_1549,_s_1548)  ->
                                    (_k_1547 _env_1549) >>
                                      (fun _gen_bind_1550  ->
                                         _gen_bind_1550 (_env_1549, _s_1548))))
                      | Effect_SetEnv  ->
                          (fun (_env_1552 : env)  ->
                             fun (_k_1551 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1553)  ->
                                    (_k_1551 _env_1552) >>
                                      (fun _gen_bind_1554  ->
                                         _gen_bind_1554 (_env_1552, _s_1553))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1556 : loc)  ->
                             fun (_k_1555 : int -> _ computation)  ->
                               value
                                 (fun (_env_1558,_s_1557)  ->
                                    (_lookupState_16 (_x_1556, _s_1557)) >>
                                      (fun _gen_bind_1559  ->
                                         (_k_1555 _gen_bind_1559) >>
                                           (fun _gen_bind_1560  ->
                                              _gen_bind_1560
                                                (_env_1558, _s_1557)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1563,_y_1562) : (loc* int))  ->
                             fun (_k_1561 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1565,_s_1564)  ->
                                    (_k_1561 _x_1563) >>
                                      (fun _gen_bind_1566  ->
                                         _gen_bind_1566
                                           (_env_1565,
                                             (run
                                                (_updateState_25
                                                   (_x_1563, _y_1562,
                                                     _s_1564)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1567 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1569,_s_1568)  ->
                                    (_k_1567 (run (_getNewLoc_43 _s_1568)))
                                      >>
                                      (fun _gen_bind_1570  ->
                                         _gen_bind_1570 (_env_1569, _s_1568))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c)) (_interp_58 _l_61)
     | Mul (_l_66,_r_67) ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1571  -> value (fun _  -> value _y_1571));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1574,_e_1573) : (env* int))  ->
                             fun (_k_1572 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1575)  ->
                                    (_k_1572 _e_1573) >>
                                      (fun _gen_bind_1576  ->
                                         _gen_bind_1576 (_env_1574, _s_1575))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1577 : env -> _ computation)  ->
                               value
                                 (fun (_env_1579,_s_1578)  ->
                                    (_k_1577 _env_1579) >>
                                      (fun _gen_bind_1580  ->
                                         _gen_bind_1580 (_env_1579, _s_1578))))
                      | Effect_SetEnv  ->
                          (fun (_env_1582 : env)  ->
                             fun (_k_1581 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1583)  ->
                                    (_k_1581 _env_1582) >>
                                      (fun _gen_bind_1584  ->
                                         _gen_bind_1584 (_env_1582, _s_1583))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1586 : loc)  ->
                             fun (_k_1585 : int -> _ computation)  ->
                               value
                                 (fun (_env_1588,_s_1587)  ->
                                    (_lookupState_16 (_x_1586, _s_1587)) >>
                                      (fun _gen_bind_1589  ->
                                         (_k_1585 _gen_bind_1589) >>
                                           (fun _gen_bind_1590  ->
                                              _gen_bind_1590
                                                (_env_1588, _s_1587)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1593,_y_1592) : (loc* int))  ->
                             fun (_k_1591 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1595,_s_1594)  ->
                                    (_k_1591 _x_1593) >>
                                      (fun _gen_bind_1596  ->
                                         _gen_bind_1596
                                           (_env_1595,
                                             (run
                                                (_updateState_25
                                                   (_x_1593, _y_1592,
                                                     _s_1594)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1597 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1599,_s_1598)  ->
                                    (_k_1597 (run (_getNewLoc_43 _s_1598)))
                                      >>
                                      (fun _gen_bind_1600  ->
                                         _gen_bind_1600 (_env_1599, _s_1598))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((_interp_58 _l_66) >>
              (fun _x_68  ->
                 (_interp_58 _r_67) >>
                   (fun _y_69  -> (run (lift_binary ( * ) _x_68)) _y_69)))
     | Sub (_l_71,_r_72) ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1601  -> value (fun _  -> value _y_1601));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1604,_e_1603) : (env* int))  ->
                             fun (_k_1602 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1605)  ->
                                    (_k_1602 _e_1603) >>
                                      (fun _gen_bind_1606  ->
                                         _gen_bind_1606 (_env_1604, _s_1605))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1607 : env -> _ computation)  ->
                               value
                                 (fun (_env_1609,_s_1608)  ->
                                    (_k_1607 _env_1609) >>
                                      (fun _gen_bind_1610  ->
                                         _gen_bind_1610 (_env_1609, _s_1608))))
                      | Effect_SetEnv  ->
                          (fun (_env_1612 : env)  ->
                             fun (_k_1611 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1613)  ->
                                    (_k_1611 _env_1612) >>
                                      (fun _gen_bind_1614  ->
                                         _gen_bind_1614 (_env_1612, _s_1613))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1616 : loc)  ->
                             fun (_k_1615 : int -> _ computation)  ->
                               value
                                 (fun (_env_1618,_s_1617)  ->
                                    (_lookupState_16 (_x_1616, _s_1617)) >>
                                      (fun _gen_bind_1619  ->
                                         (_k_1615 _gen_bind_1619) >>
                                           (fun _gen_bind_1620  ->
                                              _gen_bind_1620
                                                (_env_1618, _s_1617)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1623,_y_1622) : (loc* int))  ->
                             fun (_k_1621 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1625,_s_1624)  ->
                                    (_k_1621 _x_1623) >>
                                      (fun _gen_bind_1626  ->
                                         _gen_bind_1626
                                           (_env_1625,
                                             (run
                                                (_updateState_25
                                                   (_x_1623, _y_1622,
                                                     _s_1624)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1627 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1629,_s_1628)  ->
                                    (_k_1627 (run (_getNewLoc_43 _s_1628)))
                                      >>
                                      (fun _gen_bind_1630  ->
                                         _gen_bind_1630 (_env_1629, _s_1628))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((_interp_58 _l_71) >>
              (fun _x_73  ->
                 (_interp_58 _r_72) >>
                   (fun _y_74  -> (run (lift_binary (-) _x_73)) _y_74)))
     | Div (_l_76,_r_77) ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1631  -> value (fun _  -> value _y_1631));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1634,_e_1633) : (env* int))  ->
                             fun (_k_1632 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1635)  ->
                                    (_k_1632 _e_1633) >>
                                      (fun _gen_bind_1636  ->
                                         _gen_bind_1636 (_env_1634, _s_1635))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1637 : env -> _ computation)  ->
                               value
                                 (fun (_env_1639,_s_1638)  ->
                                    (_k_1637 _env_1639) >>
                                      (fun _gen_bind_1640  ->
                                         _gen_bind_1640 (_env_1639, _s_1638))))
                      | Effect_SetEnv  ->
                          (fun (_env_1642 : env)  ->
                             fun (_k_1641 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1643)  ->
                                    (_k_1641 _env_1642) >>
                                      (fun _gen_bind_1644  ->
                                         _gen_bind_1644 (_env_1642, _s_1643))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1646 : loc)  ->
                             fun (_k_1645 : int -> _ computation)  ->
                               value
                                 (fun (_env_1648,_s_1647)  ->
                                    (_lookupState_16 (_x_1646, _s_1647)) >>
                                      (fun _gen_bind_1649  ->
                                         (_k_1645 _gen_bind_1649) >>
                                           (fun _gen_bind_1650  ->
                                              _gen_bind_1650
                                                (_env_1648, _s_1647)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1653,_y_1652) : (loc* int))  ->
                             fun (_k_1651 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1655,_s_1654)  ->
                                    (_k_1651 _x_1653) >>
                                      (fun _gen_bind_1656  ->
                                         _gen_bind_1656
                                           (_env_1655,
                                             (run
                                                (_updateState_25
                                                   (_x_1653, _y_1652,
                                                     _s_1654)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1657 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1659,_s_1658)  ->
                                    (_k_1657 (run (_getNewLoc_43 _s_1658)))
                                      >>
                                      (fun _gen_bind_1660  ->
                                         _gen_bind_1660 (_env_1659, _s_1658))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((_interp_58 _r_77) >>
              (fun _r_num_78  ->
                 (_interp_58 _l_76) >>
                   (fun _l_num_79  ->
                      (run (lift_binary (/) _l_num_79)) _r_num_78)))
     | Ref _x_81 ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1661  -> value (fun _  -> value _y_1661));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1664,_e_1663) : (env* int))  ->
                             fun (_k_1662 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1665)  ->
                                    (_k_1662 _e_1663) >>
                                      (fun _gen_bind_1666  ->
                                         _gen_bind_1666 (_env_1664, _s_1665))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1667 : env -> _ computation)  ->
                               value
                                 (fun (_env_1669,_s_1668)  ->
                                    (_k_1667 _env_1669) >>
                                      (fun _gen_bind_1670  ->
                                         _gen_bind_1670 (_env_1669, _s_1668))))
                      | Effect_SetEnv  ->
                          (fun (_env_1672 : env)  ->
                             fun (_k_1671 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1673)  ->
                                    (_k_1671 _env_1672) >>
                                      (fun _gen_bind_1674  ->
                                         _gen_bind_1674 (_env_1672, _s_1673))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1676 : loc)  ->
                             fun (_k_1675 : int -> _ computation)  ->
                               value
                                 (fun (_env_1678,_s_1677)  ->
                                    (_lookupState_16 (_x_1676, _s_1677)) >>
                                      (fun _gen_bind_1679  ->
                                         (_k_1675 _gen_bind_1679) >>
                                           (fun _gen_bind_1680  ->
                                              _gen_bind_1680
                                                (_env_1678, _s_1677)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1683,_y_1682) : (loc* int))  ->
                             fun (_k_1681 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1685,_s_1684)  ->
                                    (_k_1681 _x_1683) >>
                                      (fun _gen_bind_1686  ->
                                         _gen_bind_1686
                                           (_env_1685,
                                             (run
                                                (_updateState_25
                                                   (_x_1683, _y_1682,
                                                     _s_1684)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1687 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1689,_s_1688)  ->
                                    (_k_1687 (run (_getNewLoc_43 _s_1688)))
                                      >>
                                      (fun _gen_bind_1690  ->
                                         _gen_bind_1690 (_env_1689, _s_1688))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((_interp_58 _x_81) >>
              (fun _x_interp_82  ->
                 call Effect_AllocLoc ()
                   (fun _result_94  ->
                      call Effect_UpdateLoc (_result_94, _x_interp_82)
                        (fun _result_91  -> value _result_91))))
     | Deref _x_84 ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1691  -> value (fun _  -> value _y_1691));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1694,_e_1693) : (env* int))  ->
                             fun (_k_1692 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1695)  ->
                                    (_k_1692 _e_1693) >>
                                      (fun _gen_bind_1696  ->
                                         _gen_bind_1696 (_env_1694, _s_1695))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1697 : env -> _ computation)  ->
                               value
                                 (fun (_env_1699,_s_1698)  ->
                                    (_k_1697 _env_1699) >>
                                      (fun _gen_bind_1700  ->
                                         _gen_bind_1700 (_env_1699, _s_1698))))
                      | Effect_SetEnv  ->
                          (fun (_env_1702 : env)  ->
                             fun (_k_1701 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1703)  ->
                                    (_k_1701 _env_1702) >>
                                      (fun _gen_bind_1704  ->
                                         _gen_bind_1704 (_env_1702, _s_1703))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1706 : loc)  ->
                             fun (_k_1705 : int -> _ computation)  ->
                               value
                                 (fun (_env_1708,_s_1707)  ->
                                    (_lookupState_16 (_x_1706, _s_1707)) >>
                                      (fun _gen_bind_1709  ->
                                         (_k_1705 _gen_bind_1709) >>
                                           (fun _gen_bind_1710  ->
                                              _gen_bind_1710
                                                (_env_1708, _s_1707)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1713,_y_1712) : (loc* int))  ->
                             fun (_k_1711 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1715,_s_1714)  ->
                                    (_k_1711 _x_1713) >>
                                      (fun _gen_bind_1716  ->
                                         _gen_bind_1716
                                           (_env_1715,
                                             (run
                                                (_updateState_25
                                                   (_x_1713, _y_1712,
                                                     _s_1714)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1717 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1719,_s_1718)  ->
                                    (_k_1717 (run (_getNewLoc_43 _s_1718)))
                                      >>
                                      (fun _gen_bind_1720  ->
                                         _gen_bind_1720 (_env_1719, _s_1718))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((_interp_58 _x_84) >>
              (fun _x_interp_85  ->
                 call Effect_LookupLoc _x_interp_85
                   (fun _result_96  -> value _result_96)))
     | Assign (_lhs_86,_rhs_87) ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1721  -> value (fun _  -> value _y_1721));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1724,_e_1723) : (env* int))  ->
                             fun (_k_1722 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1725)  ->
                                    (_k_1722 _e_1723) >>
                                      (fun _gen_bind_1726  ->
                                         _gen_bind_1726 (_env_1724, _s_1725))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1727 : env -> _ computation)  ->
                               value
                                 (fun (_env_1729,_s_1728)  ->
                                    (_k_1727 _env_1729) >>
                                      (fun _gen_bind_1730  ->
                                         _gen_bind_1730 (_env_1729, _s_1728))))
                      | Effect_SetEnv  ->
                          (fun (_env_1732 : env)  ->
                             fun (_k_1731 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1733)  ->
                                    (_k_1731 _env_1732) >>
                                      (fun _gen_bind_1734  ->
                                         _gen_bind_1734 (_env_1732, _s_1733))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1736 : loc)  ->
                             fun (_k_1735 : int -> _ computation)  ->
                               value
                                 (fun (_env_1738,_s_1737)  ->
                                    (_lookupState_16 (_x_1736, _s_1737)) >>
                                      (fun _gen_bind_1739  ->
                                         (_k_1735 _gen_bind_1739) >>
                                           (fun _gen_bind_1740  ->
                                              _gen_bind_1740
                                                (_env_1738, _s_1737)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1743,_y_1742) : (loc* int))  ->
                             fun (_k_1741 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1745,_s_1744)  ->
                                    (_k_1741 _x_1743) >>
                                      (fun _gen_bind_1746  ->
                                         _gen_bind_1746
                                           (_env_1745,
                                             (run
                                                (_updateState_25
                                                   (_x_1743, _y_1742,
                                                     _s_1744)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1747 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1749,_s_1748)  ->
                                    (_k_1747 (run (_getNewLoc_43 _s_1748)))
                                      >>
                                      (fun _gen_bind_1750  ->
                                         _gen_bind_1750 (_env_1749, _s_1748))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((_interp_58 _lhs_86) >>
              (fun _x_loc_88  ->
                 (_interp_58 _rhs_87) >>
                   (fun _x_interp_89  ->
                      call Effect_UpdateLoc (_x_loc_88, _x_interp_89)
                        (fun _result_99  -> value _x_interp_89))))
     | Var _v_90 ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1751  -> value (fun _  -> value _y_1751));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1754,_e_1753) : (env* int))  ->
                             fun (_k_1752 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1755)  ->
                                    (_k_1752 _e_1753) >>
                                      (fun _gen_bind_1756  ->
                                         _gen_bind_1756 (_env_1754, _s_1755))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1757 : env -> _ computation)  ->
                               value
                                 (fun (_env_1759,_s_1758)  ->
                                    (_k_1757 _env_1759) >>
                                      (fun _gen_bind_1760  ->
                                         _gen_bind_1760 (_env_1759, _s_1758))))
                      | Effect_SetEnv  ->
                          (fun (_env_1762 : env)  ->
                             fun (_k_1761 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1763)  ->
                                    (_k_1761 _env_1762) >>
                                      (fun _gen_bind_1764  ->
                                         _gen_bind_1764 (_env_1762, _s_1763))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1766 : loc)  ->
                             fun (_k_1765 : int -> _ computation)  ->
                               value
                                 (fun (_env_1768,_s_1767)  ->
                                    (_lookupState_16 (_x_1766, _s_1767)) >>
                                      (fun _gen_bind_1769  ->
                                         (_k_1765 _gen_bind_1769) >>
                                           (fun _gen_bind_1770  ->
                                              _gen_bind_1770
                                                (_env_1768, _s_1767)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1773,_y_1772) : (loc* int))  ->
                             fun (_k_1771 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1775,_s_1774)  ->
                                    (_k_1771 _x_1773) >>
                                      (fun _gen_bind_1776  ->
                                         _gen_bind_1776
                                           (_env_1775,
                                             (run
                                                (_updateState_25
                                                   (_x_1773, _y_1772,
                                                     _s_1774)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1777 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1779,_s_1778)  ->
                                    (_k_1777 (run (_getNewLoc_43 _s_1778)))
                                      >>
                                      (fun _gen_bind_1780  ->
                                         _gen_bind_1780 (_env_1779, _s_1778))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           (call Effect_ReadEnv ()
              (fun _result_102  -> _lookupEnv_45 (_v_90, _result_102)))
     | App (_e1_92,_e2_93) ->
         ((fun c  ->
             handler
               {
                 value_clause =
                   (fun _y_1781  -> value (fun _  -> value _y_1781));
                 effect_clauses = fun (type a) -> fun (type b) ->
                   fun (x : (a,b) effect)  ->
                     (match x with
                      | Effect_InEnv  ->
                          (fun ((_env_1784,_e_1783) : (env* int))  ->
                             fun (_k_1782 : int -> _ computation)  ->
                               value
                                 (fun (_,_s_1785)  ->
                                    (_k_1782 _e_1783) >>
                                      (fun _gen_bind_1786  ->
                                         _gen_bind_1786 (_env_1784, _s_1785))))
                      | Effect_ReadEnv  ->
                          (fun (() : unit)  ->
                             fun (_k_1787 : env -> _ computation)  ->
                               value
                                 (fun (_env_1789,_s_1788)  ->
                                    (_k_1787 _env_1789) >>
                                      (fun _gen_bind_1790  ->
                                         _gen_bind_1790 (_env_1789, _s_1788))))
                      | Effect_SetEnv  ->
                          (fun (_env_1792 : env)  ->
                             fun (_k_1791 : env -> _ computation)  ->
                               value
                                 (fun (_,_s_1793)  ->
                                    (_k_1791 _env_1792) >>
                                      (fun _gen_bind_1794  ->
                                         _gen_bind_1794 (_env_1792, _s_1793))))
                      | Effect_LookupLoc  ->
                          (fun (_x_1796 : loc)  ->
                             fun (_k_1795 : int -> _ computation)  ->
                               value
                                 (fun (_env_1798,_s_1797)  ->
                                    (_lookupState_16 (_x_1796, _s_1797)) >>
                                      (fun _gen_bind_1799  ->
                                         (_k_1795 _gen_bind_1799) >>
                                           (fun _gen_bind_1800  ->
                                              _gen_bind_1800
                                                (_env_1798, _s_1797)))))
                      | Effect_UpdateLoc  ->
                          (fun ((_x_1803,_y_1802) : (loc* int))  ->
                             fun (_k_1801 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1805,_s_1804)  ->
                                    (_k_1801 _x_1803) >>
                                      (fun _gen_bind_1806  ->
                                         _gen_bind_1806
                                           (_env_1805,
                                             (run
                                                (_updateState_25
                                                   (_x_1803, _y_1802,
                                                     _s_1804)))))))
                      | Effect_AllocLoc  ->
                          (fun (() : unit)  ->
                             fun (_k_1807 : loc -> _ computation)  ->
                               value
                                 (fun (_env_1809,_s_1808)  ->
                                    (_k_1807 (run (_getNewLoc_43 _s_1808)))
                                      >>
                                      (fun _gen_bind_1810  ->
                                         _gen_bind_1810 (_env_1809, _s_1808))))
                      | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                     a -> (b -> _ computation) -> _ computation)
               } c))
           ((match _e1_92 with
             | LambdaV (_s_95,_t_96) ->
                 call Effect_ReadEnv ()
                   (fun _result_119  ->
                      value
                        (fun _v_98  ->
                           call Effect_SetEnv
                             (run (_extendEnv_54 (_s_95, _v_98, _result_119)))
                             (fun _result_116  ->
                                (_interp_58 _t_96) >>
                                  (fun _t_res_101  ->
                                     call Effect_InEnv
                                       (_result_116, _t_res_101)
                                       (fun _result_113  -> value _result_113)))))
             | LambdaL (_s_102,_t_103) ->
                 call Effect_ReadEnv ()
                   (fun _result_141  ->
                      value
                        (fun _v_105  ->
                           call Effect_AllocLoc ()
                             (fun _result_138  ->
                                call Effect_UpdateLoc (_result_138, _v_105)
                                  (fun _result_135  ->
                                     call Effect_UpdateLoc
                                       (_result_138, _v_105)
                                       (fun _result_131  ->
                                          call Effect_LookupLoc _result_138
                                            (fun _result_128  ->
                                               call Effect_SetEnv
                                                 (run
                                                    (_extendEnv_54
                                                       (_s_102, _result_128,
                                                         _result_141)))
                                                 (fun _result_124  ->
                                                    (_interp_58 _t_103) >>
                                                      (fun _t_res_112  ->
                                                         call Effect_InEnv
                                                           (_result_124,
                                                             _t_res_112)
                                                           (fun _result_121 
                                                              ->
                                                              value
                                                                _result_121))))))))))
              >>
              (fun _interpFunc_94  ->
                 call Effect_ReadEnv ()
                   (fun _result_111  ->
                      (_interp_58 _e2_93) >>
                        (fun _e2_interp_115  ->
                           call Effect_SetEnv _result_111
                             (fun _result_108  ->
                                call Effect_InEnv
                                  (_result_108, _e2_interp_115)
                                  (fun _result_105  ->
                                     _interpFunc_94 _result_105))))))
      in
   _interp_89 _finalCase_200) >>
    (fun _gen_bind_202  -> _gen_bind_202 ([], []))
  
