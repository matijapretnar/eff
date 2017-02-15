(*
=== GENERATED FROM interp.eff ===
commit SHA: ec8d6d094577edb51f0603c9a7d9f74d8bd5c47a
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
     ((let rec _newvar_80 _a_87 =
         match _a_87 with
         | Num _b_88 -> value (fun _  -> value _b_88)
         | Add (_l_89,_r_90) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _gen_bind_842  ->
                          let _gen_bind_843 =
                            run (lift_binary (+) _gen_bind_842)  in
                          let rec _new_special_var_844 (_a_846,_k_val_845) =
                            match _a_846 with
                            | Num _b_847 -> _k_val_845 _b_847
                            | Add (_l_849,_r_848) ->
                                _new_special_var_844
                                  (_l_849,
                                    (fun _gen_bind_850  ->
                                       let _gen_bind_851 =
                                         run (lift_binary (+) _gen_bind_850)
                                          in
                                       _new_special_var_844
                                         (_r_848,
                                           (fun _gen_bind_852  ->
                                              _k_val_845
                                                (run
                                                   (_gen_bind_851
                                                      _gen_bind_852))))))
                            | Mul (_l_854,_r_853) ->
                                _new_special_var_844
                                  (_l_854,
                                    (fun _gen_bind_855  ->
                                       let _gen_bind_856 =
                                         run
                                           (lift_binary ( * ) _gen_bind_855)
                                          in
                                       _new_special_var_844
                                         (_r_853,
                                           (fun _gen_bind_857  ->
                                              _k_val_845
                                                (run
                                                   (_gen_bind_856
                                                      _gen_bind_857))))))
                            | Sub (_l_859,_r_858) ->
                                _new_special_var_844
                                  (_l_859,
                                    (fun _gen_bind_860  ->
                                       let _gen_bind_861 =
                                         run (lift_binary (-) _gen_bind_860)
                                          in
                                       _new_special_var_844
                                         (_r_858,
                                           (fun _gen_bind_862  ->
                                              _k_val_845
                                                (run
                                                   (_gen_bind_861
                                                      _gen_bind_862))))))
                            | Div (_l_864,_r_863) ->
                                _new_special_var_844
                                  (_r_863,
                                    (fun _r_num_865  ->
                                       match _r_num_865 with
                                       | 0 ->
                                           call Effect_Arith_DivByZero ()
                                             (fun _result_866  ->
                                                _k_val_845 _result_866)
                                       | _ ->
                                           _new_special_var_844
                                             (_l_864,
                                               (fun _gen_bind_867  ->
                                                  _k_val_845
                                                    (run
                                                       ((run
                                                           (lift_binary (/)
                                                              _gen_bind_867))
                                                          _r_num_865))))))
                            | Ref _x_868 ->
                                _new_special_var_844
                                  (_x_868,
                                    (fun _x_interp_869  ->
                                       call Effect_AllocLoc ()
                                         (fun _result_870  ->
                                            call Effect_UpdateLoc
                                              (_result_870, _x_interp_869)
                                              (fun _result_871  ->
                                                 _k_val_845 _result_871))))
                            | Deref _x_872 ->
                                _new_special_var_844
                                  (_x_872,
                                    (fun _x_interp_873  ->
                                       call Effect_LookupLoc _x_interp_873
                                         (fun _result_874  ->
                                            _k_val_845 _result_874)))
                            | Assign (_lhs_876,_rhs_875) ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _x_loc_877  ->
                                             (fun c  ->
                                                handler
                                                  {
                                                    value_clause =
                                                      (fun _vcvar_880  ->
                                                         _k_val_845
                                                           _vcvar_880);
                                                    effect_clauses = fun
                                                      (type a) -> fun (type
                                                      b) ->
                                                      fun (x : (a,b) effect) 
                                                        ->
                                                        (match x with
                                                         | Effect_InEnv  ->
                                                             (fun
                                                                ((_env_883,_s_882)
                                                                  :
                                                                  (env* int))
                                                                 ->
                                                                fun
                                                                  (_k_881 :
                                                                    int ->
                                                                    _
                                                                    computation)
                                                                   ->
                                                                  value
                                                                    (
                                                                    fun _  ->
                                                                    (_k_881
                                                                    _s_882)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_884
                                                                     ->
                                                                    _gen_bind_884
                                                                    _env_883)))
                                                         | Effect_ReadEnv  ->
                                                             (fun (() : unit)
                                                                 ->
                                                                fun
                                                                  (_k_885 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                   ->
                                                                  value
                                                                    (
                                                                    fun
                                                                    _env_886 
                                                                    ->
                                                                    (_k_885
                                                                    _env_886)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_887
                                                                     ->
                                                                    _gen_bind_887
                                                                    _env_886)))
                                                         | Effect_SetEnv  ->
                                                             (fun
                                                                (_env_889 :
                                                                  env)
                                                                 ->
                                                                fun
                                                                  (_k_888 :
                                                                    env ->
                                                                    _
                                                                    computation)
                                                                   ->
                                                                  value
                                                                    (
                                                                    fun _  ->
                                                                    (_k_888
                                                                    _env_889)
                                                                    >>
                                                                    (fun
                                                                    _gen_bind_890
                                                                     ->
                                                                    _gen_bind_890
                                                                    _env_889)))
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
                                               ((_interp_86 _rhs_875) >>
                                                  (fun _x_interp_878  ->
                                                     call Effect_UpdateLoc
                                                       (_x_loc_877,
                                                         _x_interp_878)
                                                       (fun _result_879  ->
                                                          (value _result_879)
                                                            >>
                                                            (fun _  ->
                                                               value
                                                                 _x_interp_878)))));
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_893,_s_892) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_891 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_891 _s_892) >>
                                                             (fun
                                                                _gen_bind_894
                                                                 ->
                                                                _gen_bind_894
                                                                  _env_893)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_895 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_896  ->
                                                           (_k_895 _env_896)
                                                             >>
                                                             (fun
                                                                _gen_bind_897
                                                                 ->
                                                                _gen_bind_897
                                                                  _env_896)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_899 : env)  ->
                                                    fun
                                                      (_k_898 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_898 _env_899)
                                                             >>
                                                             (fun
                                                                _gen_bind_900
                                                                 ->
                                                                _gen_bind_900
                                                                  _env_899)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c)) (_interp_86 _lhs_876)
                            | Var _v_901 ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _vcvar_903  ->
                                             _k_val_845 _vcvar_903);
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_906,_s_905) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_904 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_904 _s_905) >>
                                                             (fun
                                                                _gen_bind_907
                                                                 ->
                                                                _gen_bind_907
                                                                  _env_906)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_908 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_909  ->
                                                           (_k_908 _env_909)
                                                             >>
                                                             (fun
                                                                _gen_bind_910
                                                                 ->
                                                                _gen_bind_910
                                                                  _env_909)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_912 : env)  ->
                                                    fun
                                                      (_k_911 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_911 _env_912)
                                                             >>
                                                             (fun
                                                                _gen_bind_913
                                                                 ->
                                                                _gen_bind_913
                                                                  _env_912)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c))
                                  (((effect Effect_ReadEnv) ()) >>
                                     (fun _gen_bind_902  ->
                                        _lookupEnv_45 (_v_901, _gen_bind_902)))
                            | App (_e1_915,_e2_914) ->
                                ((fun c  ->
                                    handler
                                      {
                                        value_clause =
                                          (fun _vcvar_921  ->
                                             _k_val_845 _vcvar_921);
                                        effect_clauses = fun (type a) -> fun
                                          (type b) ->
                                          fun (x : (a,b) effect)  ->
                                            (match x with
                                             | Effect_InEnv  ->
                                                 (fun
                                                    ((_env_924,_s_923) :
                                                      (env* int))
                                                     ->
                                                    fun
                                                      (_k_922 :
                                                        int -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_922 _s_923) >>
                                                             (fun
                                                                _gen_bind_925
                                                                 ->
                                                                _gen_bind_925
                                                                  _env_924)))
                                             | Effect_ReadEnv  ->
                                                 (fun (() : unit)  ->
                                                    fun
                                                      (_k_926 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _env_927  ->
                                                           (_k_926 _env_927)
                                                             >>
                                                             (fun
                                                                _gen_bind_928
                                                                 ->
                                                                _gen_bind_928
                                                                  _env_927)))
                                             | Effect_SetEnv  ->
                                                 (fun (_env_930 : env)  ->
                                                    fun
                                                      (_k_929 :
                                                        env -> _ computation)
                                                       ->
                                                      value
                                                        (fun _  ->
                                                           (_k_929 _env_930)
                                                             >>
                                                             (fun
                                                                _gen_bind_931
                                                                 ->
                                                                _gen_bind_931
                                                                  _env_930)))
                                             | eff' ->
                                                 (fun arg  ->
                                                    fun k  ->
                                                      Call (eff', arg, k)) : 
                                            a ->
                                              (b -> _ computation) ->
                                                _ computation)
                                      } c))
                                  ((_interpFunc_58 (_e1_915, _interp_86)) >>
                                     (fun _e1_interp_916  ->
                                        ((effect Effect_ReadEnv) ()) >>
                                          (fun _envi_917  ->
                                             (_interp_86 _e2_914) >>
                                               (fun _e2_interp_918  ->
                                                  ((effect Effect_SetEnv)
                                                     _envi_917)
                                                    >>
                                                    (fun _envi_919  ->
                                                       ((effect Effect_InEnv)
                                                          (_envi_919,
                                                            _e2_interp_918))
                                                         >>
                                                         (fun _in_env_920  ->
                                                            _e1_interp_916
                                                              _in_env_920))))))
                             in
                          _new_special_var_844
                            (_r_90,
                              (fun _gen_bind_932  ->
                                 let _y_933 =
                                   run (_gen_bind_843 _gen_bind_932)  in
                                 value (fun _  -> value _y_933))));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_936,_s_935) : (env* int))  ->
                                 fun (_k_934 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_934 _s_935) >>
                                          (fun _gen_bind_937  ->
                                             _gen_bind_937 _env_936)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_938 : env -> _ computation)  ->
                                   value
                                     (fun _env_939  ->
                                        (_k_938 _env_939) >>
                                          (fun _gen_bind_940  ->
                                             _gen_bind_940 _env_939)))
                          | Effect_SetEnv  ->
                              (fun (_env_942 : env)  ->
                                 fun (_k_941 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_941 _env_942) >>
                                          (fun _gen_bind_943  ->
                                             _gen_bind_943 _env_942)))
                          | eff' ->
                              (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                         a -> (b -> _ computation) -> _ computation)
                   } c)) (_interp_86 _l_89)
         | Mul (_l_94,_r_95) ->
             ((fun c  ->
                 handler
                   {
                     value_clause =
                       (fun _y_944  -> value (fun _  -> value _y_944));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_947,_s_946) : (env* int))  ->
                                 fun (_k_945 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_945 _s_946) >>
                                          (fun _gen_bind_948  ->
                                             _gen_bind_948 _env_947)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_949 : env -> _ computation)  ->
                                   value
                                     (fun _env_950  ->
                                        (_k_949 _env_950) >>
                                          (fun _gen_bind_951  ->
                                             _gen_bind_951 _env_950)))
                          | Effect_SetEnv  ->
                              (fun (_env_953 : env)  ->
                                 fun (_k_952 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_952 _env_953) >>
                                          (fun _gen_bind_954  ->
                                             _gen_bind_954 _env_953)))
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
                       (fun _y_955  -> value (fun _  -> value _y_955));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_958,_s_957) : (env* int))  ->
                                 fun (_k_956 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_956 _s_957) >>
                                          (fun _gen_bind_959  ->
                                             _gen_bind_959 _env_958)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_960 : env -> _ computation)  ->
                                   value
                                     (fun _env_961  ->
                                        (_k_960 _env_961) >>
                                          (fun _gen_bind_962  ->
                                             _gen_bind_962 _env_961)))
                          | Effect_SetEnv  ->
                              (fun (_env_964 : env)  ->
                                 fun (_k_963 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_963 _env_964) >>
                                          (fun _gen_bind_965  ->
                                             _gen_bind_965 _env_964)))
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
                       (fun _y_966  -> value (fun _  -> value _y_966));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_969,_s_968) : (env* int))  ->
                                 fun (_k_967 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_967 _s_968) >>
                                          (fun _gen_bind_970  ->
                                             _gen_bind_970 _env_969)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_971 : env -> _ computation)  ->
                                   value
                                     (fun _env_972  ->
                                        (_k_971 _env_972) >>
                                          (fun _gen_bind_973  ->
                                             _gen_bind_973 _env_972)))
                          | Effect_SetEnv  ->
                              (fun (_env_975 : env)  ->
                                 fun (_k_974 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_974 _env_975) >>
                                          (fun _gen_bind_976  ->
                                             _gen_bind_976 _env_975)))
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
                       (fun _y_977  -> value (fun _  -> value _y_977));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_980,_s_979) : (env* int))  ->
                                 fun (_k_978 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_978 _s_979) >>
                                          (fun _gen_bind_981  ->
                                             _gen_bind_981 _env_980)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_982 : env -> _ computation)  ->
                                   value
                                     (fun _env_983  ->
                                        (_k_982 _env_983) >>
                                          (fun _gen_bind_984  ->
                                             _gen_bind_984 _env_983)))
                          | Effect_SetEnv  ->
                              (fun (_env_986 : env)  ->
                                 fun (_k_985 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_985 _env_986) >>
                                          (fun _gen_bind_987  ->
                                             _gen_bind_987 _env_986)))
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
                       (fun _y_988  -> value (fun _  -> value _y_988));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_991,_s_990) : (env* int))  ->
                                 fun (_k_989 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_989 _s_990) >>
                                          (fun _gen_bind_992  ->
                                             _gen_bind_992 _env_991)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_993 : env -> _ computation)  ->
                                   value
                                     (fun _env_994  ->
                                        (_k_993 _env_994) >>
                                          (fun _gen_bind_995  ->
                                             _gen_bind_995 _env_994)))
                          | Effect_SetEnv  ->
                              (fun (_env_997 : env)  ->
                                 fun (_k_996 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_996 _env_997) >>
                                          (fun _gen_bind_998  ->
                                             _gen_bind_998 _env_997)))
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
                       (fun _y_999  -> value (fun _  -> value _y_999));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1002,_s_1001) : (env* int))  ->
                                 fun (_k_1000 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1000 _s_1001) >>
                                          (fun _gen_bind_1003  ->
                                             _gen_bind_1003 _env_1002)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1004 : env -> _ computation)  ->
                                   value
                                     (fun _env_1005  ->
                                        (_k_1004 _env_1005) >>
                                          (fun _gen_bind_1006  ->
                                             _gen_bind_1006 _env_1005)))
                          | Effect_SetEnv  ->
                              (fun (_env_1008 : env)  ->
                                 fun (_k_1007 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1007 _env_1008) >>
                                          (fun _gen_bind_1009  ->
                                             _gen_bind_1009 _env_1008)))
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
                       (fun _y_1010  -> value (fun _  -> value _y_1010));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1013,_s_1012) : (env* int))  ->
                                 fun (_k_1011 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1011 _s_1012) >>
                                          (fun _gen_bind_1014  ->
                                             _gen_bind_1014 _env_1013)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1015 : env -> _ computation)  ->
                                   value
                                     (fun _env_1016  ->
                                        (_k_1015 _env_1016) >>
                                          (fun _gen_bind_1017  ->
                                             _gen_bind_1017 _env_1016)))
                          | Effect_SetEnv  ->
                              (fun (_env_1019 : env)  ->
                                 fun (_k_1018 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1018 _env_1019) >>
                                          (fun _gen_bind_1020  ->
                                             _gen_bind_1020 _env_1019)))
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
                       (fun _y_1021  -> value (fun _  -> value _y_1021));
                     effect_clauses = fun (type a) -> fun (type b) ->
                       fun (x : (a,b) effect)  ->
                         (match x with
                          | Effect_InEnv  ->
                              (fun ((_env_1024,_s_1023) : (env* int))  ->
                                 fun (_k_1022 : int -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1022 _s_1023) >>
                                          (fun _gen_bind_1025  ->
                                             _gen_bind_1025 _env_1024)))
                          | Effect_ReadEnv  ->
                              (fun (() : unit)  ->
                                 fun (_k_1026 : env -> _ computation)  ->
                                   value
                                     (fun _env_1027  ->
                                        (_k_1026 _env_1027) >>
                                          (fun _gen_bind_1028  ->
                                             _gen_bind_1028 _env_1027)))
                          | Effect_SetEnv  ->
                              (fun (_env_1030 : env)  ->
                                 fun (_k_1029 : env -> _ computation)  ->
                                   value
                                     (fun _  ->
                                        (_k_1029 _env_1030) >>
                                          (fun _gen_bind_1031  ->
                                             _gen_bind_1031 _env_1030)))
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
       _newvar_80 _finalCase_178) >> (fun _gen_bind_181  -> _gen_bind_181 [])))
    >> (fun _gen_bind_180  -> _gen_bind_180 [])
  
