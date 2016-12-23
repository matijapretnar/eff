type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
        -> 'a computation

type ('a, 'b) value_clause = 'a -> 'b computation

type ('a, 'b) finally_clause = 'a -> 'b computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
      (('eff_arg, 'eff_res) effect ->
      ('eff_arg -> ('eff_res -> 'b computation) -> 'b computation))

type ('a, 'b, 'c) handler =
  { value_clause : ('a, 'b) value_clause;
    finally_clause : ('b, 'c) finally_clause;
    effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses
  }



let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, (fun y -> (k y) >> f))
  
let rec handle (h : ('a, 'b, 'c) handler) (c : 'a computation) :
  'c computation =
  let rec handler =
    function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff
        in clause arg (fun y -> handler (k y))
  in (handler c) >> h.finally_clause
  
let value (x : 'a) : 'a computation = Value x
  
let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
  'c computation = Call (eff, arg, cont)
  
let effect eff arg = call eff arg value

let run =
  function
  | Value x -> x
  | Call (eff, _, _) -> failwith ("Uncaught effect")

let ( ** ) =
  let rec pow a = Pervasives.(function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)) in
  pow

let string_length _ = assert false
let to_string _ = assert false

;;
value ("End of pervasives")

;;


let effy_var_1 (* <> *) = ( <> )

;;

let effy_var_2 (* - *) = ( - )

;;


let effy_var_3 (* + *) = ( + )

;;

let effy_var_4 (* < *) = ( < )

;;


let effy_var_5 (* > *) = ( > )

;;

let effy_var_6 (* ~- *) = ( ~- )

;;


let effy_abs_7 = (fun effy_x_8 ->  (match ((<) effy_x_8
0) with | true ->
           (~-)
        effy_x_8
        | false ->
           effy_x_8))

;;

let rec effy_var_11 (* @ *) = fun effy_xs_12 ->
   (fun effy_ys_13 ->
   (match effy_xs_12 with | [] ->
                             effy_ys_13
                          | ((effy_x_14) :: (effy_xs_15)) ->
                             ((::) (effy_x_14, ((effy_var_11 (* @ *)
                                    effy_xs_15) effy_ys_13)))))

;;


let effy_no_attack_18 = (fun (effy_x_19, effy_y_20) ->
   (fun (effy_x'_21, effy_y'_22) ->  (match ((<>) effy_x_19
effy_x'_21) with | true ->
                    (match ((<>)
                 effy_y_20
                 effy_y'_22) with | true ->
                                     (<>)
                                  ((effy_abs_7
                                  (((-)
                                  effy_x_19
                                  effy_x'_21))))
                                  ((effy_abs_7
                                  (((-)
                                  effy_y_20
                                  effy_y'_22))))
                                  | false ->
                                     false)
                 | false ->
                    false)))

;;


let rec effy_forall_no_attack_34 = fun (effy_x_35, effy_y_36) ->
   (fun effy_gen_function_37 ->
   (match effy_gen_function_37 with | [] ->
                                       true
                                    | (((effy_x'_38, effy_y'_39)) :: (effy_xs_40)) ->
                                       (match (effy_no_attack_18
                                    (effy_x_35, effy_y_36)
                                    (effy_x'_38, effy_y'_39)) with | true ->
                                                                     effy_forall_no_attack_34
                                                                   (effy_x_35, 
                                                                    effy_y_36)
                                                                   effy_xs_40
                                                                   | false ->
                                                                     false)))

;;


let effy_available_44 = (fun effy_number_of_queens_45 ->  (fun effy_x_46 ->
   (fun effy_qs_47 ->
   let rec effy_loop_48 = fun effy_possible_49 ->  (fun effy_y_50 ->
              (match ((<) effy_y_50
           1) with | true ->
                      effy_possible_49
                   | false ->
                      (match (effy_forall_no_attack_34
                   (effy_x_46, effy_y_50)
                   effy_qs_47) with | true ->
                                       (effy_loop_48
                                    ((::) (effy_y_50, effy_possible_49)))
                                    (((-)
                                    effy_y_50
                                    1))
                                    | false ->
                                       (effy_loop_48
                                    effy_possible_49)
                                    (((-)
                                    effy_y_50
                                    1))))) in (effy_loop_48 [])
effy_number_of_queens_45)))

;;


type (_, _) effect += Effect_Decide : ( unit,  bool) effect

;;


type (_, _) effect += Effect_Fail : ( unit, unit) effect

;;


let rec effy_choose_62 = fun effy_gen_let_rec_function_63 ->
   (match effy_gen_let_rec_function_63 with | [] ->
                                               call Effect_Fail () (fun effy_result_3 ->
                                                                     value ((match effy_result_3 with _ -> assert false)))
                                            | ((effy_x_65) :: (effy_xs_66)) ->
                                               call Effect_Decide () (
                                            fun effy_result_6 ->
                                               (match effy_result_6 with 
                                            | true ->
                                               value (effy_x_65)
                                            | false ->
                                               effy_choose_62
                                            effy_xs_66)))

;;


let effy_queens_68 = (fun effy_number_of_queens_69 ->
   let rec effy_place_70 = fun effy_x_71 ->  (fun effy_qs_72 ->  (match (((>)
           effy_x_71)
           effy_number_of_queens_69) with | true ->
                                             value (effy_qs_72)
                                          | false ->
                                             (effy_choose_62
                                             ((((effy_available_44
                                             effy_number_of_queens_69)
                                             effy_x_71) effy_qs_72))) >>
                                             fun effy_y_75 ->  (effy_place_70
                                             (((+) effy_x_71 1)))
                                             ((::) ((effy_x_71, effy_y_75), 
                                                    effy_qs_72)))) in (effy_place_70
1) [])

;;

let effy_queens_one_83 = (fun effy_number_of_queens_84 ->
   handle {
      value_clause = (fun effy_gen_id_par_89 ->
                                     value (effy_gen_id_par_89));
           
      finally_clause = (fun effy_gen_id_par_88 ->
                                       value (effy_gen_id_par_88));
           
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with | Effect_Decide -> (fun (_ :  unit) (effy_k_85 :  bool -> _ computation) -> handle {
           
      value_clause = (fun effy_gen_id_par_87 ->
                                     value (effy_gen_id_par_87));
           
      finally_clause = (fun effy_gen_id_par_86 ->
                                       value (effy_gen_id_par_86));
           
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> effy_k_85
           false) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation))
    } (effy_k_85
           true)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation))
    } (effy_queens_68
effy_number_of_queens_84))

;;


let effy_queens_all_90 = (fun effy_number_of_queens_91 ->
   handle {
      value_clause = (fun effy_x_97 ->
                                     value (((::) (effy_x_97, []))));
           
      finally_clause = (fun effy_gen_id_par_96 ->
                                       value (effy_gen_id_par_96));
           
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with | Effect_Decide -> (fun (_ :  unit) (effy_k_92 :  bool -> _ computation) ->
            (effy_k_92 true) >> fun bla -> let 
           effy_gen_bind_93 = ( let effy_gen_bind_94 = bla in
           effy_var_11 (* @ *) effy_gen_bind_94) in
           (effy_k_92 false) >>
           fun effy_gen_bind_95 ->  value (effy_gen_bind_93 effy_gen_bind_95)) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value ([])) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation))
    } (effy_queens_68
effy_number_of_queens_91))
