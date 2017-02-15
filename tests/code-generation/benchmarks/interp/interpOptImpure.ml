(*
=== GENERATED FROM interp.eff ===
commit SHA: 0a8185f252df28fb2b1a33ec39799392a1190567
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
                     call Effect_InEnv
                       (_result_11, (run (_interpT_60 _t_62)))
                       (fun _result_8  -> value _result_8))))
  | LambdaV (_s_68,_t_69) ->
      call Effect_ReadEnv ()
        (fun _result_22  ->
           value
             (fun _v_71  ->
                call Effect_SetEnv
                  (run (_extendEnv_54 (_s_68, _v_71, _result_22)))
                  (fun _result_19  ->
                     call Effect_InEnv
                       (_result_19, (run (_interpT_60 _t_69)))
                       (fun _result_16  -> value _result_16))))
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
                                         call Effect_InEnv
                                           (_result_27,
                                             (run (_interpT_60 _t_76)))
                                           (fun _result_24  ->
                                              value _result_24))))))))
  
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
                 _gen_bind_132 (run (_gen_bind_134 [_gen_bind_135])))))
  
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
                              (run (_k_150 _gen_bind_153)) _s_151)))
           | Effect_UpdateLoc  ->
               (fun ((_x_143,_y_144) : (loc* int))  ->
                  fun (_k_145 : loc -> _ computation)  ->
                    value
                      (fun _s_146  ->
                         (run (_k_145 _x_143))
                           (run (_updateState_25 (_x_143, _y_144, _s_146)))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_139 : loc -> _ computation)  ->
                    value
                      (fun _s_140  ->
                         (run (_k_139 (run (_getNewLoc_43 _s_140)))) _s_140))
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
     ((let rec _newvar_80 _a_87 =
         match _a_87 with
         | Num _b_88 -> value (fun _  -> value _b_88)
         | Add (_l_89,_r_90) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _gen_bind_161  ->
                          let _gen_bind_162 =
                            run (lift_binary (+) _gen_bind_161)  in
                          (fun c  ->
                             handler
                               {
                                 value_clause =
                                   (fun _gen_bind_163  ->
                                      let _y_164 =
                                        run (_gen_bind_162 _gen_bind_163)  in
                                      value (fun _  -> value _y_164));
                                 effect_clauses = fun (type a) -> fun (type
                                   b) ->
                                   fun (x : (a,b) effect)  ->
                                     (match x with
                                      | Effect_InEnv  ->
                                          (fun
                                             ((_env_167,_s_166) : (env* int))
                                              ->
                                             fun
                                               (_k_165 :
                                                 int -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_165 _s_166))
                                                      _env_167))
                                      | Effect_ReadEnv  ->
                                          (fun (() : unit)  ->
                                             fun
                                               (_k_168 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _env_169  ->
                                                    (run (_k_168 _env_169))
                                                      _env_169))
                                      | Effect_SetEnv  ->
                                          (fun (_env_171 : env)  ->
                                             fun
                                               (_k_170 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_170 _env_171))
                                                      _env_171))
                                      | eff' ->
                                          (fun arg  ->
                                             fun k  -> Call (eff', arg, k)) : 
                                     a ->
                                       (b -> _ computation) -> _ computation)
                               } c) (_interp_86 _r_90));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_174,_s_173) : (env* int))  ->
                                 fun (_k_172 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_172 _s_173)) _env_174))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_175 : env -> _ computation)  ->
                                   value
                                     (fun _env_176  ->
                                        (run (_k_175 _env_176)) _env_176))
                          | Effect_SetEnv  ->
                              (fun (_env_178 : env)  ->
                                 fun (_k_177 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_177 _env_178)) _env_178))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _l_89)
         | Mul (_l_94,_r_95) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _gen_bind_227  ->
                          let _gen_bind_228 =
                            run (lift_binary ( * ) _gen_bind_227)  in
                          (fun c  ->
                             handler
                               {
                                 value_clause =
                                   (fun _gen_bind_229  ->
                                      let _y_230 =
                                        run (_gen_bind_228 _gen_bind_229)  in
                                      value (fun _  -> value _y_230));
                                 effect_clauses = fun (type a) -> fun (type
                                   b) ->
                                   fun (x : (a,b) effect)  ->
                                     (match x with
                                      | Effect_InEnv  ->
                                          (fun
                                             ((_env_233,_s_232) : (env* int))
                                              ->
                                             fun
                                               (_k_231 :
                                                 int -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_231 _s_232))
                                                      _env_233))
                                      | Effect_ReadEnv  ->
                                          (fun (() : unit)  ->
                                             fun
                                               (_k_234 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _env_235  ->
                                                    (run (_k_234 _env_235))
                                                      _env_235))
                                      | Effect_SetEnv  ->
                                          (fun (_env_237 : env)  ->
                                             fun
                                               (_k_236 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_236 _env_237))
                                                      _env_237))
                                      | eff' ->
                                          (fun arg  ->
                                             fun k  -> Call (eff', arg, k)) : 
                                     a ->
                                       (b -> _ computation) -> _ computation)
                               } c) (_interp_86 _r_95));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_240,_s_239) : (env* int))  ->
                                 fun (_k_238 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_238 _s_239)) _env_240))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_241 : env -> _ computation)  ->
                                   value
                                     (fun _env_242  ->
                                        (run (_k_241 _env_242)) _env_242))
                          | Effect_SetEnv  ->
                              (fun (_env_244 : env)  ->
                                 fun (_k_243 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_243 _env_244)) _env_244))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _l_94)
         | Sub (_l_99,_r_100) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _gen_bind_293  ->
                          let _gen_bind_294 =
                            run (lift_binary (-) _gen_bind_293)  in
                          (fun c  ->
                             handler
                               {
                                 value_clause =
                                   (fun _gen_bind_295  ->
                                      let _y_296 =
                                        run (_gen_bind_294 _gen_bind_295)  in
                                      value (fun _  -> value _y_296));
                                 effect_clauses = fun (type a) -> fun (type
                                   b) ->
                                   fun (x : (a,b) effect)  ->
                                     (match x with
                                      | Effect_InEnv  ->
                                          (fun
                                             ((_env_299,_s_298) : (env* int))
                                              ->
                                             fun
                                               (_k_297 :
                                                 int -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_297 _s_298))
                                                      _env_299))
                                      | Effect_ReadEnv  ->
                                          (fun (() : unit)  ->
                                             fun
                                               (_k_300 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _env_301  ->
                                                    (run (_k_300 _env_301))
                                                      _env_301))
                                      | Effect_SetEnv  ->
                                          (fun (_env_303 : env)  ->
                                             fun
                                               (_k_302 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_302 _env_303))
                                                      _env_303))
                                      | eff' ->
                                          (fun arg  ->
                                             fun k  -> Call (eff', arg, k)) : 
                                     a ->
                                       (b -> _ computation) -> _ computation)
                               } c) (_interp_86 _r_100));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_306,_s_305) : (env* int))  ->
                                 fun (_k_304 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_304 _s_305)) _env_306))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_307 : env -> _ computation)  ->
                                   value
                                     (fun _env_308  ->
                                        (run (_k_307 _env_308)) _env_308))
                          | Effect_SetEnv  ->
                              (fun (_env_310 : env)  ->
                                 fun (_k_309 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_309 _env_310)) _env_310))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _l_99)
         | Div (_l_104,_r_105) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _r_num_369  ->
                          match _r_num_369 with
                          | 0 ->
                              call Effect_Arith_DivByZero ()
                                (fun _result_370  ->
                                   value (fun _  -> value _result_370))
                          | _ ->
                              ((fun c  ->
                                  handler
                                    {
                                      value_clause =
                                        (fun _gen_bind_371  ->
                                           let _y_372 =
                                             run
                                               ((run
                                                   (lift_binary (/)
                                                      _gen_bind_371))
                                                  _r_num_369)
                                              in
                                           value (fun _  -> value _y_372));
                                      effect_clauses = fun (type a) -> fun
                                        (type b) ->
                                        fun (x : (a,b) effect)  ->
                                          (match x with
                                           | Effect_InEnv  ->
                                               (fun
                                                  ((_env_375,_s_374) :
                                                    (env* int))
                                                   ->
                                                  fun
                                                    (_k_373 :
                                                      int -> _ computation)
                                                     ->
                                                    value
                                                      (fun _  ->
                                                         (run (_k_373 _s_374))
                                                           _env_375))
                                           | Effect_ReadEnv  ->
                                               (fun (() : unit)  ->
                                                  fun
                                                    (_k_376 :
                                                      env -> _ computation)
                                                     ->
                                                    value
                                                      (fun _env_377  ->
                                                         (run
                                                            (_k_376 _env_377))
                                                           _env_377))
                                           | Effect_SetEnv  ->
                                               (fun (_env_379 : env)  ->
                                                  fun
                                                    (_k_378 :
                                                      env -> _ computation)
                                                     ->
                                                    value
                                                      (fun _  ->
                                                         (run
                                                            (_k_378 _env_379))
                                                           _env_379))
                                           | eff' ->
                                               (fun arg  ->
                                                  fun k  ->
                                                    Call (eff', arg, k)) : 
                                          a ->
                                            (b -> _ computation) ->
                                              _ computation)
                                    } c)) (_interp_86 _l_104));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_382,_s_381) : (env* int))  ->
                                 fun (_k_380 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_380 _s_381)) _env_382))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_383 : env -> _ computation)  ->
                                   value
                                     (fun _env_384  ->
                                        (run (_k_383 _env_384)) _env_384))
                          | Effect_SetEnv  ->
                              (fun (_env_386 : env)  ->
                                 fun (_k_385 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_385 _env_386)) _env_386))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _r_105)
         | Ref _x_109 ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _x_interp_402  ->
                          call Effect_AllocLoc ()
                            (fun _result_403  ->
                               call Effect_UpdateLoc
                                 (_result_403, _x_interp_402)
                                 (fun _result_404  ->
                                    value (fun _  -> value _result_404))));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_407,_s_406) : (env* int))  ->
                                 fun (_k_405 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_405 _s_406)) _env_407))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_408 : env -> _ computation)  ->
                                   value
                                     (fun _env_409  ->
                                        (run (_k_408 _env_409)) _env_409))
                          | Effect_SetEnv  ->
                              (fun (_env_411 : env)  ->
                                 fun (_k_410 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_410 _env_411)) _env_411))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _x_109)
         | Deref _x_112 ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _x_interp_424  ->
                          call Effect_LookupLoc _x_interp_424
                            (fun _result_425  ->
                               value (fun _  -> value _result_425)));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_428,_s_427) : (env* int))  ->
                                 fun (_k_426 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_426 _s_427)) _env_428))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_429 : env -> _ computation)  ->
                                   value
                                     (fun _env_430  ->
                                        (run (_k_429 _env_430)) _env_430))
                          | Effect_SetEnv  ->
                              (fun (_env_432 : env)  ->
                                 fun (_k_431 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_431 _env_432)) _env_432))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _x_112)
         | Assign (_lhs_114,_rhs_115) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _x_loc_474  ->
                          (fun c  ->
                             handler
                               {
                                 value_clause =
                                   (fun _x_interp_475  ->
                                      call Effect_UpdateLoc
                                        (_x_loc_474, _x_interp_475)
                                        (fun _result_476  ->
                                           value
                                             (fun _  -> value _x_interp_475)));
                                 effect_clauses = fun (type a) -> fun (type
                                   b) ->
                                   fun (x : (a,b) effect)  ->
                                     (match x with
                                      | Effect_InEnv  ->
                                          (fun
                                             ((_env_479,_s_478) : (env* int))
                                              ->
                                             fun
                                               (_k_477 :
                                                 int -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_477 _s_478))
                                                      _env_479))
                                      | Effect_ReadEnv  ->
                                          (fun (() : unit)  ->
                                             fun
                                               (_k_480 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _env_481  ->
                                                    (run (_k_480 _env_481))
                                                      _env_481))
                                      | Effect_SetEnv  ->
                                          (fun (_env_483 : env)  ->
                                             fun
                                               (_k_482 :
                                                 env -> _ computation)
                                                ->
                                               value
                                                 (fun _  ->
                                                    (run (_k_482 _env_483))
                                                      _env_483))
                                      | eff' ->
                                          (fun arg  ->
                                             fun k  -> Call (eff', arg, k)) : 
                                     a ->
                                       (b -> _ computation) -> _ computation)
                               } c) (_interp_86 _rhs_115));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_486,_s_485) : (env* int))  ->
                                 fun (_k_484 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_484 _s_485)) _env_486))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_487 : env -> _ computation)  ->
                                   value
                                     (fun _env_488  ->
                                        (run (_k_487 _env_488)) _env_488))
                          | Effect_SetEnv  ->
                              (fun (_env_490 : env)  ->
                                 fun (_k_489 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_489 _env_490)) _env_490))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _lhs_114)
         | Var _v_118 ->
             value
               (fun _env_509  ->
                  (run
                     ((_lookupEnv_45 (_v_118, _env_509)) >>
                        (fun _y_500  -> value (fun _  -> value _y_500))))
                    _env_509)
         | App (_e1_120,_e2_121) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _e1_interp_616  ->
                          value
                            (fun _env_617  ->
                               (run
                                  ((fun _result_618  ->
                                      (fun c  ->
                                         handler
                                           {
                                             value_clause =
                                               (fun _e2_interp_619  ->
                                                  value
                                                    (fun _  ->
                                                       (run
                                                          ((fun _result_620 
                                                              ->
                                                              (fun c  ->
                                                                 handler
                                                                   {
                                                                    value_clause
                                                                    =
                                                                    (fun
                                                                    _y_622 
                                                                    ->
                                                                    value
                                                                    (fun _ 
                                                                    ->
                                                                    value
                                                                    _y_622));
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
                                                                    Effect_InEnv
                                                                     ->
                                                                    (fun
                                                                    ((_env_625,_s_624)
                                                                    :
                                                                    (env*
                                                                    int))  ->
                                                                    fun
                                                                    (_k_623 :
                                                                    int ->
                                                                    _
                                                                    computation)
                                                                     ->
                                                                    value
                                                                    (fun _ 
                                                                    ->
                                                                    (run
                                                                    (_k_623
                                                                    _s_624))
                                                                    _env_625))
                                                                    | 
                                                                    Effect_ReadEnv
                                                                     ->
                                                                    (fun
                                                                    (() :
                                                                    unit)  ->
                                                                    fun
                                                                    (_k_626 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                     ->
                                                                    value
                                                                    (fun
                                                                    _env_627 
                                                                    ->
                                                                    (run
                                                                    (_k_626
                                                                    _env_627))
                                                                    _env_627))
                                                                    | 
                                                                    Effect_SetEnv
                                                                     ->
                                                                    (fun
                                                                    (_env_629
                                                                    : env) 
                                                                    ->
                                                                    fun
                                                                    (_k_628 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                     ->
                                                                    value
                                                                    (fun _ 
                                                                    ->
                                                                    (run
                                                                    (_k_628
                                                                    _env_629))
                                                                    _env_629))
                                                                    | 
                                                                    eff' ->
                                                                    (fun arg 
                                                                    ->
                                                                    fun k  ->
                                                                    Call
                                                                    (eff',
                                                                    arg, k)) : 
                                                                    a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
                                                                   } c)
                                                                (call
                                                                   Effect_InEnv
                                                                   (_result_620,
                                                                    _e2_interp_619)
                                                                   (fun
                                                                    _result_621
                                                                     ->
                                                                    _e1_interp_616
                                                                    _result_621)))
                                                             _result_618))
                                                         _result_618));
                                             effect_clauses = fun (type a) ->
                                               fun (type b) ->
                                               fun (x : (a,b) effect)  ->
                                                 (match x with
                                                  | Effect_InEnv  ->
                                                      (fun
                                                         ((_env_632,_s_631) :
                                                           (env* int))
                                                          ->
                                                         fun
                                                           (_k_630 :
                                                             int ->
                                                               _ computation)
                                                            ->
                                                           value
                                                             (fun _  ->
                                                                (run
                                                                   (_k_630
                                                                    _s_631))
                                                                  _env_632))
                                                  | Effect_ReadEnv  ->
                                                      (fun (() : unit)  ->
                                                         fun
                                                           (_k_633 :
                                                             env ->
                                                               _ computation)
                                                            ->
                                                           value
                                                             (fun _env_634 
                                                                ->
                                                                (run
                                                                   (_k_633
                                                                    _env_634))
                                                                  _env_634))
                                                  | Effect_SetEnv  ->
                                                      (fun (_env_636 : env) 
                                                         ->
                                                         fun
                                                           (_k_635 :
                                                             env ->
                                                               _ computation)
                                                            ->
                                                           value
                                                             (fun _  ->
                                                                (run
                                                                   (_k_635
                                                                    _env_636))
                                                                  _env_636))
                                                  | eff' ->
                                                      (fun arg  ->
                                                         fun k  ->
                                                           Call
                                                             (eff', arg, k)) : 
                                                 a ->
                                                   (b -> _ computation) ->
                                                     _ computation)
                                           } c) (_interp_86 _e2_121))
                                     _env_617)) _env_617));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_639,_s_638) : (env* int))  ->
                                 fun (_k_637 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_637 _s_638)) _env_639))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_640 : env -> _ computation)  ->
                                   value
                                     (fun _env_641  ->
                                        (run (_k_640 _env_641)) _env_641))
                          | Effect_SetEnv  ->
                              (fun (_env_643 : env)  ->
                                 fun (_k_642 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (run (_k_642 _env_643)) _env_643))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interpFunc_58 (_e1_120, _interp_86))
          in
       _newvar_80 _finalCase_178) >> (fun _gen_bind_181  -> _gen_bind_181 [])))
    >> (fun _gen_bind_180  -> _gen_bind_180 [])
  
