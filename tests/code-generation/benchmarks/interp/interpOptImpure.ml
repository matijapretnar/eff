(*
=== GENERATED FROM interp.eff ===
commit SHA: 03cdc167bd82ae792396973571e61b43009cf73a
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
    | LambdaN of (string * term)
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

let rec interpFunc (a, interpT) =
    begin match a with
    | LambdaN (s, t) ->
        let envi = (#ReadEnv ()) in
        (fun v ->
            let ext = (extendEnv (s, v, envi) ) in
            let ext = #SetEnv ext in
            #InEnv (ext, interpT t)
        )
    | LambdaV (s, t) ->
        let envi = (#ReadEnv ()) in
        (fun v ->
            let ext = (extendEnv (s, v, envi)) in
            let ext = #SetEnv ext in
            #InEnv (ext, interpT t)
        )
    | LambdaL (s, t) ->
        let envi = (#ReadEnv ()) in
        (fun v ->
            let x_loc = #AllocLoc () in
            let thunk = #UpdateLoc (x_loc, v); v in
            let tmp = #UpdateLoc (x_loc, thunk) in
            let ext = (extendEnv (s, (#LookupLoc x_loc), envi)) in
            let ext = #SetEnv ext in
            #InEnv (ext, interpT t)
        )
    (* | CallCC ->
        (fun f ->
            let f' = f in
            #Callcc (fun k -> f' (fun a -> k))
        ) *)
    end
;;

let rec interp a =
    begin match a with
    | Num b -> b
    | Add (l, r) -> (interp l) + (interp r)
    | Mul (l, r) -> (interp l) * (interp r)
    | Sub (l, r) -> (interp l) - (interp r)
    | Div (l, r) ->
        let r_num = (interp r) in
        begin match r_num with
        | 0 -> #Arith_DivByZero ()
        | _ -> (interp l) / r_num
        end
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
        let e1_interp = (interpFunc (e1, interp)) in
        let envi = (#ReadEnv ()) in
        let e2_interp = (interp e2) in
        let envi = #SetEnv envi in
        let in_env = (#InEnv (envi, e2_interp)) in
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

let arithmeticHandler = handler
    | #Arith_DivByZero () k ->  -1 (* (absurd (#DivisionByZero ())) *)

;;

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
            Add (
                Add (
                    (Var "a"),
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
    );;

let addCase =
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
    (with storeHandler handle (
        (with environmentHandler handle (
            interp (finalCase)
        )) []
    )) [];;

(********************************
* Tests
********************************)

(* Simple arithmetic test *)
(* let test1 = interp (Add (Num 5, Num 3));;
assert(test1 = 8);;


(* Division by zero test *)
let test2 = with arithmeticHandler handle (
    interp (Div (Num 5, Num 0))
);;
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
  | LambdaN of (string* term) 
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
let rec _interpFunc_58 (_a_59,_interpT_60) =
  match _a_59 with
  | LambdaN (_s_61,_t_62) ->
      call Effect_ReadEnv ()
        (fun _result_14  ->
           value
             (fun _v_64  ->
                call Effect_SetEnv
                  (run (_extendEnv_54 (_s_61, _v_64, _result_14)))
                  (fun _result_11  ->
                     (_interpT_60 _t_62) >>
                       (fun _gen_bind_67  ->
                          call Effect_InEnv (_result_11, _gen_bind_67)
                            (fun _result_8  -> value _result_8)))))
  | LambdaV (_s_68,_t_69) ->
      call Effect_ReadEnv ()
        (fun _result_22  ->
           value
             (fun _v_71  ->
                call Effect_SetEnv
                  (run (_extendEnv_54 (_s_68, _v_71, _result_22)))
                  (fun _result_19  ->
                     (_interpT_60 _t_69) >>
                       (fun _gen_bind_74  ->
                          call Effect_InEnv (_result_19, _gen_bind_74)
                            (fun _result_16  -> value _result_16)))))
  | LambdaL (_s_75,_t_76) ->
      call Effect_ReadEnv ()
        (fun _result_44  ->
           value
             (fun _v_78  ->
                call Effect_AllocLoc ()
                  (fun _result_41  ->
                     call Effect_UpdateLoc (_result_41, _v_78)
                       (fun _result_38  ->
                          call Effect_UpdateLoc (_result_41, _v_78)
                            (fun _result_34  ->
                               call Effect_LookupLoc _result_41
                                 (fun _result_31  ->
                                    call Effect_SetEnv
                                      (run
                                         (_extendEnv_54
                                            (_s_75, _result_31, _result_44)))
                                      (fun _result_27  ->
                                         (_interpT_60 _t_76) >>
                                           (fun _gen_bind_85  ->
                                              call Effect_InEnv
                                                (_result_27, _gen_bind_85)
                                                (fun _result_24  ->
                                                   value _result_24)))))))))
  
let rec _interp_86 _a_87 =
  match _a_87 with
  | Num _b_88 -> value _b_88
  | Add (_l_89,_r_90) ->
      (_interp_86 _l_89) >>
        ((fun _gen_bind_92  ->
            let _gen_bind_91 = run (lift_binary (+) _gen_bind_92)  in
            (_interp_86 _r_90) >>
              (fun _gen_bind_93  -> _gen_bind_91 _gen_bind_93)))
  | Mul (_l_94,_r_95) ->
      (_interp_86 _l_94) >>
        ((fun _gen_bind_97  ->
            let _gen_bind_96 = run (lift_binary ( * ) _gen_bind_97)  in
            (_interp_86 _r_95) >>
              (fun _gen_bind_98  -> _gen_bind_96 _gen_bind_98)))
  | Sub (_l_99,_r_100) ->
      (_interp_86 _l_99) >>
        ((fun _gen_bind_102  ->
            let _gen_bind_101 = run (lift_binary (-) _gen_bind_102)  in
            (_interp_86 _r_100) >>
              (fun _gen_bind_103  -> _gen_bind_101 _gen_bind_103)))
  | Div (_l_104,_r_105) ->
      (_interp_86 _r_105) >>
        ((fun _r_num_106  ->
            match _r_num_106 with
            | 0 ->
                call Effect_Arith_DivByZero ()
                  (fun _result_46  -> value _result_46)
            | _ ->
                (_interp_86 _l_104) >>
                  ((fun _gen_bind_108  ->
                      (run (lift_binary (/) _gen_bind_108)) _r_num_106))))
  | Ref _x_109 ->
      (_interp_86 _x_109) >>
        ((fun _x_interp_110  ->
            call Effect_AllocLoc ()
              (fun _result_51  ->
                 call Effect_UpdateLoc (_result_51, _x_interp_110)
                   (fun _result_48  -> value _result_48))))
  | Deref _x_112 ->
      (_interp_86 _x_112) >>
        ((fun _x_interp_113  ->
            call Effect_LookupLoc _x_interp_113
              (fun _result_53  -> value _result_53)))
  | Assign (_lhs_114,_rhs_115) ->
      (_interp_86 _lhs_114) >>
        ((fun _x_loc_116  ->
            (_interp_86 _rhs_115) >>
              (fun _x_interp_117  ->
                 call Effect_UpdateLoc (_x_loc_116, _x_interp_117)
                   (fun _result_56  -> value _x_interp_117))))
  | Var _v_118 ->
      call Effect_ReadEnv ()
        (fun _result_59  -> _lookupEnv_45 (_v_118, _result_59))
  | App (_e1_120,_e2_121) ->
      (_interpFunc_58 (_e1_120, _interp_86)) >>
        ((fun _e1_interp_122  ->
            call Effect_ReadEnv ()
              (fun _result_68  ->
                 (_interp_86 _e2_121) >>
                   (fun _e2_interp_124  ->
                      call Effect_SetEnv _result_68
                        (fun _result_65  ->
                           call Effect_InEnv (_result_65, _e2_interp_124)
                             (fun _result_62  -> _e1_interp_122 _result_62))))))
  
let rec _interpTopLevel_127 _lst_128 =
  value
    (fun _results_129  ->
       match _lst_128 with
       | [] -> value _results_129
       | _top_130::_tail_131 ->
           let _gen_bind_132 = run (_interpTopLevel_127 _tail_131)  in
           let _gen_bind_134 = run (_var_9 _results_129)  in
           (_interp_86 _top_130) >>
             ((fun _gen_bind_135  ->
                 (_gen_bind_134 [_gen_bind_135]) >>
                   (fun _gen_bind_133  -> _gen_bind_132 _gen_bind_133))))
  
let _arithmeticHandler_136 c =
  handler
    {
      value_clause = (fun _gen_id_par_182  -> value _gen_id_par_182);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Arith_DivByZero  ->
               (fun (() : unit)  ->
                  fun (_k_137 : int -> _ computation)  -> lift_unary (~-) 1)
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _storeHandler_138 c =
  handler
    {
      value_clause = (fun _y_154  -> value (fun _  -> value _y_154));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_LookupLoc  ->
               (fun (_x_149 : loc)  ->
                  fun (_k_150 : int -> _ computation)  ->
                    value
                      (fun _s_151  ->
                         (_lookupState_16 (_x_149, _s_151)) >>
                           (fun _gen_bind_153  ->
                              (_k_150 _gen_bind_153) >>
                                (fun _gen_bind_152  -> _gen_bind_152 _s_151))))
           | Effect_UpdateLoc  ->
               (fun ((_x_143,_y_144) : (loc* int))  ->
                  fun (_k_145 : loc -> _ computation)  ->
                    value
                      (fun _s_146  ->
                         (_k_145 _x_143) >>
                           (fun _gen_bind_147  ->
                              _gen_bind_147
                                (run
                                   (_updateState_25 (_x_143, _y_144, _s_146))))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_139 : loc -> _ computation)  ->
                    value
                      (fun _s_140  ->
                         (_k_139 (run (_getNewLoc_43 _s_140))) >>
                           (fun _gen_bind_141  -> _gen_bind_141 _s_140)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _environmentHandler_155 c =
  handler
    {
      value_clause = (fun _y_166  -> value (fun _  -> value _y_166));
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_InEnv  ->
               (fun ((_env_162,_s_163) : (env* int))  ->
                  fun (_k_164 : int -> _ computation)  ->
                    value
                      (fun _  ->
                         (_k_164 _s_163) >>
                           (fun _gen_bind_165  -> _gen_bind_165 _env_162)))
           | Effect_ReadEnv  ->
               (fun (() : unit)  ->
                  fun (_k_159 : env -> _ computation)  ->
                    value
                      (fun _env_160  ->
                         (_k_159 _env_160) >>
                           (fun _gen_bind_161  -> _gen_bind_161 _env_160)))
           | Effect_SetEnv  ->
               (fun (_env_156 : env)  ->
                  fun (_k_157 : env -> _ computation)  ->
                    value
                      (fun _  ->
                         (_k_157 _env_156) >>
                           (fun _gen_bind_158  -> _gen_bind_158 _env_156)))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    } c
  
let _lambdaCase_167 =
  LambdaV
    ("a",
      (Add
         ((Add ((Add ((Var "a"), (Num 2))), (Add ((Num 1), (Num 2))))),
           (Add ((Add ((Num 1), (Num 2))), (Add ((Num 1), (Num 2))))))))
  
let _addCase_168 =
  Add
    ((Add ((Add ((Num 1), (Num 2))), (Add ((Num 1), (Num 2))))),
      (Add ((Add ((Num 1), (Num 2))), (Add ((Num 1), (Num 2))))))
  
let _testCaseA_169 =
  App
    (_lambdaCase_167,
      (App
         (_lambdaCase_167,
           (App
              (_lambdaCase_167,
                (App
                   (_lambdaCase_167,
                     (App
                        (_lambdaCase_167,
                          (App
                             (_lambdaCase_167,
                               (App (_lambdaCase_167, _addCase_168)))))))))))))
  
let _testCaseB_170 =
  App
    (_lambdaCase_167,
      (App
         (_lambdaCase_167,
           (App
              (_lambdaCase_167,
                (App
                   (_lambdaCase_167,
                     (App
                        (_lambdaCase_167,
                          (App
                             (_lambdaCase_167,
                               (App (_lambdaCase_167, _testCaseA_169)))))))))))))
  
let _testCaseC_171 =
  App
    (_lambdaCase_167,
      (App
         (_lambdaCase_167,
           (App
              (_lambdaCase_167,
                (App
                   (_lambdaCase_167,
                     (App
                        (_lambdaCase_167,
                          (App
                             (_lambdaCase_167,
                               (App (_lambdaCase_167, _testCaseB_170)))))))))))))
  
let _testCaseD_172 =
  App
    (_lambdaCase_167,
      (App
         (_lambdaCase_167,
           (App
              (_lambdaCase_167,
                (App
                   (_lambdaCase_167,
                     (App
                        (_lambdaCase_167,
                          (App
                             (_lambdaCase_167,
                               (App (_lambdaCase_167, _testCaseC_171)))))))))))))
  
let rec _createCase_173 _n_174 =
  match _n_174 with
  | 1 -> value _testCaseD_172
  | _ ->
      value
        (App
           (_lambdaCase_167,
             (run (_createCase_173 (run ((run (lift_binary (-) _n_174)) 1))))))
  
let _finalCase_178 = run (_createCase_173 200) 
let _bigTest_179 () =
  (_storeHandler_138
     ((let rec _interp_80 _a_87 =
         match _a_87 with
         | Num _b_88 -> value (fun _  -> value _b_88)
         | Add (_l_89,_r_90) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _gen_bind_1075  ->
                          let _gen_bind_1076 =
                            run (lift_binary (+) _gen_bind_1075)  in
                          let rec _new_special_var_1077 (_a_1079,_k_val_1078)
                            =
                            match _a_1079 with
                            | Num _b_1080 -> _k_val_1078 _b_1080
                            | Add (_l_1082,_r_1081) ->
                                _new_special_var_1077
                                  (_l_1082,
                                    (fun _gen_bind_1083  ->
                                       let _gen_bind_1084 =
                                         run (lift_binary (+) _gen_bind_1083)
                                          in
                                       _new_special_var_1077
                                         (_r_1081,
                                           (fun _gen_bind_1085  ->
                                              (fun c  ->
                                                 handler
                                                   {
                                                     value_clause =
                                                       (fun _vcvar_1086  ->
                                                          _k_val_1078
                                                            _vcvar_1086);
                                                     effect_clauses = fun
                                                       (type a) -> fun (type
                                                       b) ->
                                                       fun (x : (a,b) effect)
                                                          ->
                                                         (match x with
                                                          | Effect_InEnv  ->
                                                              (fun
                                                                 ((_env_1089,_s_1088)
                                                                   :
                                                                   (env* int))
                                                                  ->
                                                                 fun
                                                                   (_k_1087 :
                                                                    int ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun _ 
                                                                    ->
                                                                    (_k_1087
                                                                    _s_1088)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1090
                                                                     ->
                                                                    _gen_bind_1090
                                                                    _env_1089)))
                                                          | Effect_ReadEnv 
                                                              ->
                                                              (fun
                                                                 (() : unit) 
                                                                 ->
                                                                 fun
                                                                   (_k_1091 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun
                                                                    _env_1092
                                                                     ->
                                                                    (_k_1091
                                                                    _env_1092)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1093
                                                                     ->
                                                                    _gen_bind_1093
                                                                    _env_1092)))
                                                          | Effect_SetEnv  ->
                                                              (fun
                                                                 (_env_1095 :
                                                                   env)
                                                                  ->
                                                                 fun
                                                                   (_k_1094 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun _ 
                                                                    ->
                                                                    (_k_1094
                                                                    _env_1095)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1096
                                                                     ->
                                                                    _gen_bind_1096
                                                                    _env_1095)))
                                                          | eff' ->
                                                              (fun arg  ->
                                                                 fun k  ->
                                                                   Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                         a ->
                                                           (b ->
                                                              _ computation)
                                                             -> _ computation)
                                                   } c)
                                                (_gen_bind_1084
                                                   _gen_bind_1085)))))
                            | Mul (_l_1098,_r_1097) ->
                                _new_special_var_1077
                                  (_l_1098,
                                    (fun _gen_bind_1099  ->
                                       let _gen_bind_1100 =
                                         run
                                           (lift_binary ( * ) _gen_bind_1099)
                                          in
                                       _new_special_var_1077
                                         (_r_1097,
                                           (fun _gen_bind_1101  ->
                                              (fun c  ->
                                                 handler
                                                   {
                                                     value_clause =
                                                       (fun _vcvar_1102  ->
                                                          _k_val_1078
                                                            _vcvar_1102);
                                                     effect_clauses = fun
                                                       (type a) -> fun (type
                                                       b) ->
                                                       fun (x : (a,b) effect)
                                                          ->
                                                         (match x with
                                                          | Effect_InEnv  ->
                                                              (fun
                                                                 ((_env_1105,_s_1104)
                                                                   :
                                                                   (env* int))
                                                                  ->
                                                                 fun
                                                                   (_k_1103 :
                                                                    int ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun _ 
                                                                    ->
                                                                    (_k_1103
                                                                    _s_1104)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1106
                                                                     ->
                                                                    _gen_bind_1106
                                                                    _env_1105)))
                                                          | Effect_ReadEnv 
                                                              ->
                                                              (fun
                                                                 (() : unit) 
                                                                 ->
                                                                 fun
                                                                   (_k_1107 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun
                                                                    _env_1108
                                                                     ->
                                                                    (_k_1107
                                                                    _env_1108)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1109
                                                                     ->
                                                                    _gen_bind_1109
                                                                    _env_1108)))
                                                          | Effect_SetEnv  ->
                                                              (fun
                                                                 (_env_1111 :
                                                                   env)
                                                                  ->
                                                                 fun
                                                                   (_k_1110 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun _ 
                                                                    ->
                                                                    (_k_1110
                                                                    _env_1111)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1112
                                                                     ->
                                                                    _gen_bind_1112
                                                                    _env_1111)))
                                                          | eff' ->
                                                              (fun arg  ->
                                                                 fun k  ->
                                                                   Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                         a ->
                                                           (b ->
                                                              _ computation)
                                                             -> _ computation)
                                                   } c)
                                                (_gen_bind_1100
                                                   _gen_bind_1101)))))
                            | Sub (_l_1114,_r_1113) ->
                                _new_special_var_1077
                                  (_l_1114,
                                    (fun _gen_bind_1115  ->
                                       let _gen_bind_1116 =
                                         run (lift_binary (-) _gen_bind_1115)
                                          in
                                       _new_special_var_1077
                                         (_r_1113,
                                           (fun _gen_bind_1117  ->
                                              (fun c  ->
                                                 handler
                                                   {
                                                     value_clause =
                                                       (fun _vcvar_1118  ->
                                                          _k_val_1078
                                                            _vcvar_1118);
                                                     effect_clauses = fun
                                                       (type a) -> fun (type
                                                       b) ->
                                                       fun (x : (a,b) effect)
                                                          ->
                                                         (match x with
                                                          | Effect_InEnv  ->
                                                              (fun
                                                                 ((_env_1121,_s_1120)
                                                                   :
                                                                   (env* int))
                                                                  ->
                                                                 fun
                                                                   (_k_1119 :
                                                                    int ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun _ 
                                                                    ->
                                                                    (_k_1119
                                                                    _s_1120)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1122
                                                                     ->
                                                                    _gen_bind_1122
                                                                    _env_1121)))
                                                          | Effect_ReadEnv 
                                                              ->
                                                              (fun
                                                                 (() : unit) 
                                                                 ->
                                                                 fun
                                                                   (_k_1123 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun
                                                                    _env_1124
                                                                     ->
                                                                    (_k_1123
                                                                    _env_1124)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1125
                                                                     ->
                                                                    _gen_bind_1125
                                                                    _env_1124)))
                                                          | Effect_SetEnv  ->
                                                              (fun
                                                                 (_env_1127 :
                                                                   env)
                                                                  ->
                                                                 fun
                                                                   (_k_1126 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                   value
                                                                    (fun _ 
                                                                    ->
                                                                    (_k_1126
                                                                    _env_1127)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1128
                                                                     ->
                                                                    _gen_bind_1128
                                                                    _env_1127)))
                                                          | eff' ->
                                                              (fun arg  ->
                                                                 fun k  ->
                                                                   Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                         a ->
                                                           (b ->
                                                              _ computation)
                                                             -> _ computation)
                                                   } c)
                                                (_gen_bind_1116
                                                   _gen_bind_1117)))))
                            | Div (_l_1130,_r_1129) ->
                                _new_special_var_1077
                                  (_r_1129,
                                    (fun _r_num_1131  ->
                                       match _r_num_1131 with
                                       | 0 ->
                                           call Effect_Arith_DivByZero ()
                                             (fun _result_1132  ->
                                                _k_val_1078 _result_1132)
                                       | _ ->
                                           _new_special_var_1077
                                             (_l_1130,
                                               (fun _gen_bind_1133  ->
                                                  _k_val_1078
                                                    (run
                                                       ((run
                                                           (lift_binary (/)
                                                              _gen_bind_1133))
                                                          _r_num_1131))))))
                            | Ref _x_1134 ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _x_interp_1135  ->
                                             (fun c  ->
                                                handler
                                                  {
                                                    value_clause =
                                                      (fun _vcvar_1139  ->
                                                         _k_val_1078
                                                           _vcvar_1139);
                                                    effect_clauses = fun
                                                      (type a) -> fun (type
                                                      b) ->
                                                      fun (x : (a,b) effect) 
                                                        ->
                                                        (match x with
                                                         | Effect_InEnv  ->
                                                             (fun
                                                                ((_env_1142,_s_1141)
                                                                  :
                                                                  (env* int))
                                                                 ->
                                                                fun
                                                                  (_k_1140 :
                                                                    int ->
                                                                    _
                                                                    computation)
                                                                   ->
                                                                  value
                                                                    (
                                                                    fun _  ->
                                                                    (_k_1140
                                                                    _s_1141)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1143
                                                                     ->
                                                                    _gen_bind_1143
                                                                    _env_1142)))
                                                         | Effect_ReadEnv  ->
                                                             (fun (() : unit)
                                                                 ->
                                                                fun
                                                                  (_k_1144 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                   ->
                                                                  value
                                                                    (
                                                                    fun
                                                                    _env_1145
                                                                     ->
                                                                    (_k_1144
                                                                    _env_1145)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1146
                                                                     ->
                                                                    _gen_bind_1146
                                                                    _env_1145)))
                                                         | Effect_SetEnv  ->
                                                             (fun
                                                                (_env_1148 :
                                                                  env)
                                                                 ->
                                                                fun
                                                                  (_k_1147 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                   ->
                                                                  value
                                                                    (
                                                                    fun _  ->
                                                                    (_k_1147
                                                                    _env_1148)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_1149
                                                                     ->
                                                                    _gen_bind_1149
                                                                    _env_1148)))
                                                         | eff' ->
                                                             (fun arg  ->
                                                                fun k  ->
                                                                  Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                        a ->
                                                          (b -> _ computation)
                                                            -> _ computation)
                                                  } c)
                                               (call Effect_AllocLoc ()
                                                  (fun _result_1136  ->
                                                     let _x_loc_1137 =
                                                       _result_1136  in
                                                     call Effect_UpdateLoc
                                                       (_x_loc_1137,
                                                         _x_interp_1135)
                                                       (fun _result_1138  ->
                                                          value _result_1138))));
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_1152,_s_1151) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_1150 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1150 _s_1151)
                                                             >>
                                                             (fun
                                                                _gen_bind_1153
                                                                 ->
                                                                _gen_bind_1153
                                                                  _env_1152)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_1154 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_1155  ->
                                                           (_k_1154 _env_1155)
                                                             >>
                                                             (fun
                                                                _gen_bind_1156
                                                                 ->
                                                                _gen_bind_1156
                                                                  _env_1155)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_1158 : env)  ->
                                                    fun
                                                      (_k_1157 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1157 _env_1158)
                                                             >>
                                                             (fun
                                                                _gen_bind_1159
                                                                 ->
                                                                _gen_bind_1159
                                                                  _env_1158)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c)) (_interp_86 _x_1134)
                            | Deref _x_1160 ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _vcvar_1162  ->
                                             _k_val_1078 _vcvar_1162);
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_1165,_s_1164) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_1163 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1163 _s_1164)
                                                             >>
                                                             (fun
                                                                _gen_bind_1166
                                                                 ->
                                                                _gen_bind_1166
                                                                  _env_1165)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_1167 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_1168  ->
                                                           (_k_1167 _env_1168)
                                                             >>
                                                             (fun
                                                                _gen_bind_1169
                                                                 ->
                                                                _gen_bind_1169
                                                                  _env_1168)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_1171 : env)  ->
                                                    fun
                                                      (_k_1170 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1170 _env_1171)
                                                             >>
                                                             (fun
                                                                _gen_bind_1172
                                                                 ->
                                                                _gen_bind_1172
                                                                  _env_1171)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c))
                                  ((_interp_86 _x_1160) >>
                                     (fun _x_interp_1161  ->
                                        (effect Effect_LookupLoc)
                                          _x_interp_1161))
                            | Assign (_lhs_1174,_rhs_1173) ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _vcvar_1177  ->
                                             _k_val_1078 _vcvar_1177);
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_1180,_s_1179) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_1178 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1178 _s_1179)
                                                             >>
                                                             (fun
                                                                _gen_bind_1181
                                                                 ->
                                                                _gen_bind_1181
                                                                  _env_1180)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_1182 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_1183  ->
                                                           (_k_1182 _env_1183)
                                                             >>
                                                             (fun
                                                                _gen_bind_1184
                                                                 ->
                                                                _gen_bind_1184
                                                                  _env_1183)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_1186 : env)  ->
                                                    fun
                                                      (_k_1185 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1185 _env_1186)
                                                             >>
                                                             (fun
                                                                _gen_bind_1187
                                                                 ->
                                                                _gen_bind_1187
                                                                  _env_1186)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c))
                                  ((_interp_86 _lhs_1174) >>
                                     (fun _x_loc_1175  ->
                                        (_interp_86 _rhs_1173) >>
                                          (fun _x_interp_1176  ->
                                             ((effect Effect_UpdateLoc)
                                                (_x_loc_1175, _x_interp_1176))
                                               >>
                                               (fun _  ->
                                                  value _x_interp_1176))))
                            | Var _v_1188 ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _vcvar_1190  ->
                                             _k_val_1078 _vcvar_1190);
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_1193,_s_1192) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_1191 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1191 _s_1192)
                                                             >>
                                                             (fun
                                                                _gen_bind_1194
                                                                 ->
                                                                _gen_bind_1194
                                                                  _env_1193)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_1195 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_1196  ->
                                                           (_k_1195 _env_1196)
                                                             >>
                                                             (fun
                                                                _gen_bind_1197
                                                                 ->
                                                                _gen_bind_1197
                                                                  _env_1196)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_1199 : env)  ->
                                                    fun
                                                      (_k_1198 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1198 _env_1199)
                                                             >>
                                                             (fun
                                                                _gen_bind_1200
                                                                 ->
                                                                _gen_bind_1200
                                                                  _env_1199)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c))
                                  (((effect Effect_ReadEnv) ()) >>
                                     (fun _gen_bind_1189  ->
                                        _lookupEnv_45
                                          (_v_1188, _gen_bind_1189)))
                            | App (_e1_1202,_e2_1201) ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _vcvar_1208  ->
                                             _k_val_1078 _vcvar_1208);
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_1211,_s_1210) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_1209 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1209 _s_1210)
                                                             >>
                                                             (fun
                                                                _gen_bind_1212
                                                                 ->
                                                                _gen_bind_1212
                                                                  _env_1211)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_1213 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_1214  ->
                                                           (_k_1213 _env_1214)
                                                             >>
                                                             (fun
                                                                _gen_bind_1215
                                                                 ->
                                                                _gen_bind_1215
                                                                  _env_1214)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_1217 : env)  ->
                                                    fun
                                                      (_k_1216 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1216 _env_1217)
                                                             >>
                                                             (fun
                                                                _gen_bind_1218
                                                                 ->
                                                                _gen_bind_1218
                                                                  _env_1217)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c))
                                  ((_interpFunc_58 (_e1_1202, _interp_86)) >>
                                     (fun _e1_interp_1203  ->
                                        ((effect Effect_ReadEnv) ()) >>
                                          (fun _envi_1204  ->
                                             (_interp_86 _e2_1201) >>
                                               (fun _e2_interp_1205  ->
                                                  ((effect Effect_SetEnv)
                                                     _envi_1204)
                                                    >>
                                                    (fun _envi_1206  ->
                                                       ((effect Effect_InEnv)
                                                          (_envi_1206,
                                                            _e2_interp_1205))
                                                         >>
                                                         (fun _in_env_1207 
                                                            ->
                                                            _e1_interp_1203
                                                              _in_env_1207))))))
                             in
                          _new_special_var_1077
                            (_r_90,
                              (fun _gen_bind_1219  ->
                                 (fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _y_1220  ->
                                             value (fun _  -> value _y_1220));
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_1223,_s_1222) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_1221 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1221 _s_1222)
                                                             >>
                                                             (fun
                                                                _gen_bind_1224
                                                                 ->
                                                                _gen_bind_1224
                                                                  _env_1223)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_1225 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_1226  ->
                                                           (_k_1225 _env_1226)
                                                             >>
                                                             (fun
                                                                _gen_bind_1227
                                                                 ->
                                                                _gen_bind_1227
                                                                  _env_1226)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_1229 : env)  ->
                                                    fun
                                                      (_k_1228 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_1228 _env_1229)
                                                             >>
                                                             (fun
                                                                _gen_bind_1230
                                                                 ->
                                                                _gen_bind_1230
                                                                  _env_1229)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c) (_gen_bind_1076 _gen_bind_1219))));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1233,_s_1232) : (env* int))  ->
                                 fun (_k_1231 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1231 _s_1232) >>
                                          (fun _gen_bind_1234  ->
                                             _gen_bind_1234 _env_1233)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1235 : env -> _ computation)  ->
                                   value
                                     (fun _env_1236  ->
                                        (_k_1235 _env_1236) >>
                                          (fun _gen_bind_1237  ->
                                             _gen_bind_1237 _env_1236)))
                          | Effect_SetEnv  ->
                              (fun (_env_1239 : env)  ->
                                 fun (_k_1238 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1238 _env_1239) >>
                                          (fun _gen_bind_1240  ->
                                             _gen_bind_1240 _env_1239)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _l_89)
         | Mul (_l_94,_r_95) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1241  -> value (fun _  -> value _y_1241));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1244,_s_1243) : (env* int))  ->
                                 fun (_k_1242 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1242 _s_1243) >>
                                          (fun _gen_bind_1245  ->
                                             _gen_bind_1245 _env_1244)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1246 : env -> _ computation)  ->
                                   value
                                     (fun _env_1247  ->
                                        (_k_1246 _env_1247) >>
                                          (fun _gen_bind_1248  ->
                                             _gen_bind_1248 _env_1247)))
                          | Effect_SetEnv  ->
                              (fun (_env_1250 : env)  ->
                                 fun (_k_1249 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1249 _env_1250) >>
                                          (fun _gen_bind_1251  ->
                                             _gen_bind_1251 _env_1250)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interp_86 _l_94) >>
                  (fun _gen_bind_97  ->
                     let _gen_bind_96 = run (lift_binary ( * ) _gen_bind_97)
                        in
                     (_interp_86 _r_95) >>
                       (fun _gen_bind_98  -> _gen_bind_96 _gen_bind_98)))
         | Sub (_l_99,_r_100) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1252  -> value (fun _  -> value _y_1252));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1255,_s_1254) : (env* int))  ->
                                 fun (_k_1253 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1253 _s_1254) >>
                                          (fun _gen_bind_1256  ->
                                             _gen_bind_1256 _env_1255)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1257 : env -> _ computation)  ->
                                   value
                                     (fun _env_1258  ->
                                        (_k_1257 _env_1258) >>
                                          (fun _gen_bind_1259  ->
                                             _gen_bind_1259 _env_1258)))
                          | Effect_SetEnv  ->
                              (fun (_env_1261 : env)  ->
                                 fun (_k_1260 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1260 _env_1261) >>
                                          (fun _gen_bind_1262  ->
                                             _gen_bind_1262 _env_1261)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interp_86 _l_99) >>
                  (fun _gen_bind_102  ->
                     let _gen_bind_101 = run (lift_binary (-) _gen_bind_102)
                        in
                     (_interp_86 _r_100) >>
                       (fun _gen_bind_103  -> _gen_bind_101 _gen_bind_103)))
         | Div (_l_104,_r_105) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1263  -> value (fun _  -> value _y_1263));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1266,_s_1265) : (env* int))  ->
                                 fun (_k_1264 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1264 _s_1265) >>
                                          (fun _gen_bind_1267  ->
                                             _gen_bind_1267 _env_1266)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1268 : env -> _ computation)  ->
                                   value
                                     (fun _env_1269  ->
                                        (_k_1268 _env_1269) >>
                                          (fun _gen_bind_1270  ->
                                             _gen_bind_1270 _env_1269)))
                          | Effect_SetEnv  ->
                              (fun (_env_1272 : env)  ->
                                 fun (_k_1271 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1271 _env_1272) >>
                                          (fun _gen_bind_1273  ->
                                             _gen_bind_1273 _env_1272)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interp_86 _r_105) >>
                  (fun _r_num_106  ->
                     match _r_num_106 with
                     | 0 ->
                         call Effect_Arith_DivByZero ()
                           (fun _result_82  -> value _result_82)
                     | _ ->
                         (_interp_86 _l_104) >>
                           ((fun _gen_bind_108  ->
                               (run (lift_binary (/) _gen_bind_108))
                                 _r_num_106))))
         | Ref _x_109 ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1274  -> value (fun _  -> value _y_1274));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1277,_s_1276) : (env* int))  ->
                                 fun (_k_1275 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1275 _s_1276) >>
                                          (fun _gen_bind_1278  ->
                                             _gen_bind_1278 _env_1277)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1279 : env -> _ computation)  ->
                                   value
                                     (fun _env_1280  ->
                                        (_k_1279 _env_1280) >>
                                          (fun _gen_bind_1281  ->
                                             _gen_bind_1281 _env_1280)))
                          | Effect_SetEnv  ->
                              (fun (_env_1283 : env)  ->
                                 fun (_k_1282 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1282 _env_1283) >>
                                          (fun _gen_bind_1284  ->
                                             _gen_bind_1284 _env_1283)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interp_86 _x_109) >>
                  (fun _x_interp_110  ->
                     call Effect_AllocLoc ()
                       (fun _result_87  ->
                          call Effect_UpdateLoc (_result_87, _x_interp_110)
                            (fun _result_84  -> value _result_84))))
         | Deref _x_112 ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1285  -> value (fun _  -> value _y_1285));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1288,_s_1287) : (env* int))  ->
                                 fun (_k_1286 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1286 _s_1287) >>
                                          (fun _gen_bind_1289  ->
                                             _gen_bind_1289 _env_1288)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1290 : env -> _ computation)  ->
                                   value
                                     (fun _env_1291  ->
                                        (_k_1290 _env_1291) >>
                                          (fun _gen_bind_1292  ->
                                             _gen_bind_1292 _env_1291)))
                          | Effect_SetEnv  ->
                              (fun (_env_1294 : env)  ->
                                 fun (_k_1293 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1293 _env_1294) >>
                                          (fun _gen_bind_1295  ->
                                             _gen_bind_1295 _env_1294)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interp_86 _x_112) >>
                  (fun _x_interp_113  ->
                     call Effect_LookupLoc _x_interp_113
                       (fun _result_89  -> value _result_89)))
         | Assign (_lhs_114,_rhs_115) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1296  -> value (fun _  -> value _y_1296));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1299,_s_1298) : (env* int))  ->
                                 fun (_k_1297 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1297 _s_1298) >>
                                          (fun _gen_bind_1300  ->
                                             _gen_bind_1300 _env_1299)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1301 : env -> _ computation)  ->
                                   value
                                     (fun _env_1302  ->
                                        (_k_1301 _env_1302) >>
                                          (fun _gen_bind_1303  ->
                                             _gen_bind_1303 _env_1302)))
                          | Effect_SetEnv  ->
                              (fun (_env_1305 : env)  ->
                                 fun (_k_1304 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1304 _env_1305) >>
                                          (fun _gen_bind_1306  ->
                                             _gen_bind_1306 _env_1305)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interp_86 _lhs_114) >>
                  (fun _x_loc_116  ->
                     (_interp_86 _rhs_115) >>
                       (fun _x_interp_117  ->
                          call Effect_UpdateLoc (_x_loc_116, _x_interp_117)
                            (fun _result_92  -> value _x_interp_117))))
         | Var _v_118 ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1307  -> value (fun _  -> value _y_1307));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1310,_s_1309) : (env* int))  ->
                                 fun (_k_1308 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1308 _s_1309) >>
                                          (fun _gen_bind_1311  ->
                                             _gen_bind_1311 _env_1310)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1312 : env -> _ computation)  ->
                                   value
                                     (fun _env_1313  ->
                                        (_k_1312 _env_1313) >>
                                          (fun _gen_bind_1314  ->
                                             _gen_bind_1314 _env_1313)))
                          | Effect_SetEnv  ->
                              (fun (_env_1316 : env)  ->
                                 fun (_k_1315 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1315 _env_1316) >>
                                          (fun _gen_bind_1317  ->
                                             _gen_bind_1317 _env_1316)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               (call Effect_ReadEnv ()
                  (fun _result_95  -> _lookupEnv_45 (_v_118, _result_95)))
         | App (_e1_120,_e2_121) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_1318  -> value (fun _  -> value _y_1318));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1321,_s_1320) : (env* int))  ->
                                 fun (_k_1319 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1319 _s_1320) >>
                                          (fun _gen_bind_1322  ->
                                             _gen_bind_1322 _env_1321)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1323 : env -> _ computation)  ->
                                   value
                                     (fun _env_1324  ->
                                        (_k_1323 _env_1324) >>
                                          (fun _gen_bind_1325  ->
                                             _gen_bind_1325 _env_1324)))
                          | Effect_SetEnv  ->
                              (fun (_env_1327 : env)  ->
                                 fun (_k_1326 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1326 _env_1327) >>
                                          (fun _gen_bind_1328  ->
                                             _gen_bind_1328 _env_1327)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c))
               ((_interpFunc_58 (_e1_120, _interp_86)) >>
                  (fun _e1_interp_122  ->
                     call Effect_ReadEnv ()
                       (fun _result_104  ->
                          (_interp_86 _e2_121) >>
                            (fun _e2_interp_124  ->
                               call Effect_SetEnv _result_104
                                 (fun _result_101  ->
                                    call Effect_InEnv
                                      (_result_101, _e2_interp_124)
                                      (fun _result_98  ->
                                         _e1_interp_122 _result_98))))))
          in
       _interp_80 _finalCase_178) >> (fun _gen_bind_181  -> _gen_bind_181 [])))
    >> (fun _gen_bind_180  -> _gen_bind_180 [])
  
