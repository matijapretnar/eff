(*
=== GENERATED FROM interp.eff ===
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
let rec _interpFunc_58 (_a_59,_interpT_60) =
  match _a_59 with
  | LambdaN (_s_61,_t_62) ->
      ((effect Effect_ReadEnv) ()) >>
        ((fun _envi_63  ->
            value
              (fun _v_64  ->
                 (_extendEnv_54 (_s_61, _v_64, _envi_63)) >>
                   (fun _ext_65  ->
                      ((effect Effect_SetEnv) _ext_65) >>
                        (fun _ext_66  ->
                           (_interpT_60 _t_62) >>
                             (fun _gen_bind_67  ->
                                (effect Effect_InEnv) (_ext_66, _gen_bind_67)))))))
  | LambdaV (_s_68,_t_69) ->
      ((effect Effect_ReadEnv) ()) >>
        ((fun _envi_70  ->
            value
              (fun _v_71  ->
                 (_extendEnv_54 (_s_68, _v_71, _envi_70)) >>
                   (fun _ext_72  ->
                      ((effect Effect_SetEnv) _ext_72) >>
                        (fun _ext_73  ->
                           (_interpT_60 _t_69) >>
                             (fun _gen_bind_74  ->
                                (effect Effect_InEnv) (_ext_73, _gen_bind_74)))))))
  | LambdaL (_s_75,_t_76) ->
      ((effect Effect_ReadEnv) ()) >>
        ((fun _envi_77  ->
            value
              (fun _v_78  ->
                 ((effect Effect_AllocLoc) ()) >>
                   (fun _x_loc_79  ->
                      (((effect Effect_UpdateLoc) (_x_loc_79, _v_78)) >>
                         (fun _  -> value _v_78))
                        >>
                        (fun _thunk_80  ->
                           ((effect Effect_UpdateLoc) (_x_loc_79, _thunk_80))
                             >>
                             (fun _tmp_81  ->
                                (((effect Effect_LookupLoc) _x_loc_79) >>
                                   (fun _gen_bind_83  ->
                                      _extendEnv_54
                                        (_s_75, _gen_bind_83, _envi_77)))
                                  >>
                                  (fun _ext_82  ->
                                     ((effect Effect_SetEnv) _ext_82) >>
                                       (fun _ext_84  ->
                                          (_interpT_60 _t_76) >>
                                            (fun _gen_bind_85  ->
                                               (effect Effect_InEnv)
                                                 (_ext_84, _gen_bind_85))))))))))
  
let rec _interp_86 _a_87 =
  match _a_87 with
  | Num _b_88 -> value _b_88
  | Add (_l_89,_r_90) ->
      ((_interp_86 _l_89) >> (fun _gen_bind_92  -> _var_4 _gen_bind_92)) >>
        ((fun _gen_bind_91  ->
            (_interp_86 _r_90) >>
              (fun _gen_bind_93  -> _gen_bind_91 _gen_bind_93)))
  | Mul (_l_94,_r_95) ->
      ((_interp_86 _l_94) >> (fun _gen_bind_97  -> _var_5 _gen_bind_97)) >>
        ((fun _gen_bind_96  ->
            (_interp_86 _r_95) >>
              (fun _gen_bind_98  -> _gen_bind_96 _gen_bind_98)))
  | Sub (_l_99,_r_100) ->
      ((_interp_86 _l_99) >> (fun _gen_bind_102  -> _var_6 _gen_bind_102)) >>
        ((fun _gen_bind_101  ->
            (_interp_86 _r_100) >>
              (fun _gen_bind_103  -> _gen_bind_101 _gen_bind_103)))
  | Div (_l_104,_r_105) ->
      (_interp_86 _r_105) >>
        ((fun _r_num_106  ->
            match _r_num_106 with
            | 0 -> (effect Effect_Arith_DivByZero) ()
            | _ ->
                ((_interp_86 _l_104) >>
                   (fun _gen_bind_108  -> _var_8 _gen_bind_108))
                  >> ((fun _gen_bind_107  -> _gen_bind_107 _r_num_106))))
  | Ref _x_109 ->
      (_interp_86 _x_109) >>
        ((fun _x_interp_110  ->
            ((effect Effect_AllocLoc) ()) >>
              (fun _x_loc_111  ->
                 (effect Effect_UpdateLoc) (_x_loc_111, _x_interp_110))))
  | Deref _x_112 ->
      (_interp_86 _x_112) >>
        ((fun _x_interp_113  -> (effect Effect_LookupLoc) _x_interp_113))
  | Assign (_lhs_114,_rhs_115) ->
      (_interp_86 _lhs_114) >>
        ((fun _x_loc_116  ->
            (_interp_86 _rhs_115) >>
              (fun _x_interp_117  ->
                 ((effect Effect_UpdateLoc) (_x_loc_116, _x_interp_117)) >>
                   (fun _  -> value _x_interp_117))))
  | Var _v_118 ->
      ((effect Effect_ReadEnv) ()) >>
        ((fun _gen_bind_119  -> _lookupEnv_45 (_v_118, _gen_bind_119)))
  | App (_e1_120,_e2_121) ->
      (_interpFunc_58 (_e1_120, _interp_86)) >>
        ((fun _e1_interp_122  ->
            ((effect Effect_ReadEnv) ()) >>
              (fun _envi_123  ->
                 (_interp_86 _e2_121) >>
                   (fun _e2_interp_124  ->
                      ((effect Effect_SetEnv) _envi_123) >>
                        (fun _envi_125  ->
                           ((effect Effect_InEnv) (_envi_125, _e2_interp_124))
                             >>
                             (fun _in_env_126  -> _e1_interp_122 _in_env_126))))))
  
let rec _interpTopLevel_127 _lst_128 =
  value
    (fun _results_129  ->
       match _lst_128 with
       | [] -> value _results_129
       | _top_130::_tail_131 ->
           (_interpTopLevel_127 _tail_131) >>
             ((fun _gen_bind_132  ->
                 ((_var_9 _results_129) >>
                    (fun _gen_bind_134  ->
                       (_interp_86 _top_130) >>
                         (fun _gen_bind_135  -> _gen_bind_134 [_gen_bind_135])))
                   >> (fun _gen_bind_133  -> _gen_bind_132 _gen_bind_133))))
  
let _arithmeticHandler_136 c =
  handler
    {
      value_clause = (fun _gen_id_par_182  -> value _gen_id_par_182);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Arith_DivByZero  ->
               (fun (() : unit)  ->
                  fun (_k_137 : int -> _ computation)  -> _var_7 1)
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
                         ((_lookupState_16 (_x_149, _s_151)) >>
                            (fun _gen_bind_153  -> _k_150 _gen_bind_153))
                           >> (fun _gen_bind_152  -> _gen_bind_152 _s_151)))
           | Effect_UpdateLoc  ->
               (fun ((_x_143,_y_144) : (loc* int))  ->
                  fun (_k_145 : loc -> _ computation)  ->
                    value
                      (fun _s_146  ->
                         (_k_145 _x_143) >>
                           (fun _gen_bind_147  ->
                              (_updateState_25 (_x_143, _y_144, _s_146)) >>
                                (fun _gen_bind_148  ->
                                   _gen_bind_147 _gen_bind_148))))
           | Effect_AllocLoc  ->
               (fun (() : unit)  ->
                  fun (_k_139 : loc -> _ computation)  ->
                    value
                      (fun _s_140  ->
                         ((_getNewLoc_43 _s_140) >>
                            (fun _gen_bind_142  -> _k_139 _gen_bind_142))
                           >> (fun _gen_bind_141  -> _gen_bind_141 _s_140)))
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
      (((_var_6 _n_174) >> (fun _gen_bind_177  -> _gen_bind_177 1)) >>
         (fun _gen_bind_176  -> _createCase_173 _gen_bind_176))
        >>
        ((fun _gen_bind_175  -> value (App (_lambdaCase_167, _gen_bind_175))))
  
let _finalCase_178 = run (_createCase_173 200) 
let _bigTest_179 () =
  (_storeHandler_138
     ((_environmentHandler_155 (_interp_86 _finalCase_178)) >>
        (fun _gen_bind_181  -> _gen_bind_181 [])))
    >> (fun _gen_bind_180  -> _gen_bind_180 [])
  
