type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
        -> 'a computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
      (('eff_arg, 'eff_res) effect ->
      ('eff_arg -> ('eff_res -> 'b) -> 'b))

type ('a, 'b) handler_clauses =
  {
    value_clause : 'a -> 'b;
    effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses
  }


let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, (fun y -> (k y) >> f))
  
let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler =
    function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff
        in clause arg (fun y -> handler (k y))
  in
  handler

let value (x : 'a) : 'a computation = Value x
  
let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
  'c computation = Call (eff, arg, cont)
  
let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

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

let lift_unary f = fun x -> value (f x)
let lift_binary f = fun x -> value (fun y -> value (f x y))

;;
let _var_1 (* = *) x = lift_binary ( = ) x

;;


let _var_2 (* < *) x = lift_binary ( < ) x

;;


let _var_3 (* > *) x = lift_binary ( > ) x

;;


let _var_4 (* <> *) x = lift_binary ( <> ) x

;;


let _var_5 (* <= *) x = lift_binary ( <= ) x

;;


let _var_6 (* >= *) x = lift_binary ( >= ) x

;;


let _var_7 (* != *) x = lift_binary ( != ) x

;;


type (_, _) effect += Effect_Print : ( string,  unit) effect

;;


type (_, _) effect += Effect_Read : ( unit,  string) effect

;;


type (_, _) effect += Effect_Raise : ( unit, unit) effect

;;


let _absurd_8 = (fun _void_9 ->
   (match _void_9 with _ -> assert false))

;;


type (_, _) effect += Effect_DivisionByZero : ( unit, unit) effect

;;


type (_, _) effect += Effect_InvalidArgument : ( string, unit) effect

;;


type (_, _) effect += Effect_Failure : ( string, unit) effect

;;


let _failwith_10 = (fun _msg_11 ->
   call Effect_Failure _msg_11 (fun _result_3 ->  _absurd_8 _result_3))

;;


type (_, _) effect += Effect_AssertionFault : ( unit, unit) effect

;;


let _var_13 (* ~- *) x = lift_unary ( ~- ) x

;;


let _var_14 (* + *) x = lift_binary ( + ) x

;;


let _var_15 (* * *) x = lift_binary ( * ) x

;;


let _var_16 (* - *) x = lift_binary ( - ) x

;;


let _mod_17 x = lift_binary ( mod ) x

;;

let _mod_18 = (fun _m_19 ->
   value (fun _n_20 ->
   (match _n_20 with | 0 ->
                        call Effect_DivisionByZero () (fun _result_6 ->
                                                          _absurd_8
                                                       _result_6)
                     | _n_22 ->
                        (run (lift_binary (mod)
                     _m_19))
                     _n_22)))

;;


let _var_24 (* ~-. *) x = lift_unary ( ~-. ) x

;;


let _var_25 (* +. *) x = lift_binary ( +. ) x

;;


let _var_26 (* *. *) x = lift_binary ( *. ) x

;;


let _var_27 (* -. *) x = lift_binary ( -. ) x

;;


let _var_28 (* /. *) x = lift_binary ( /. ) x

;;


let _var_29 (* / *) x = lift_binary ( / ) x

;;


let _var_30 (* ** *) x = lift_binary ( ** ) x

;;


let _var_31 (* / *) = (fun _m_32 ->  value (fun _n_33 ->
   (match _n_33 with | 0 ->
                        call Effect_DivisionByZero () (fun _result_9 ->
                                                          _absurd_8
                                                       _result_9)
                     | _n_35 ->
                        (run (lift_binary (/)
                     _m_32))
                     _n_35)))

;;


let _float_of_int_37 x = lift_unary ( float_of_int ) x

;;


let _var_38 (* ^ *) x = lift_binary ( ^ ) x

;;


let _string_length_39 x = lift_unary ( string_length ) x

;;


let _to_string_40 x = lift_unary ( to_string ) x

;;


type ('t9) option = None|Some of 't9

;;

let rec _assoc_41 = fun _x_42 ->
   value (fun _gen_function_43 ->
   (match _gen_function_43 with | [] ->
                                   value None
                                | (((_y_44, _z_45)) :: (_lst_46)) ->
                                   (match run ((run (lift_binary (=)
                                _x_42))
                                _y_44) with | true ->
                                               value ((Some _z_45))
                                            | false ->
                                               (run (_assoc_41
                                            _x_42))
                                            _lst_46)))

;;


let _not_50 = (fun _x_51 ->
   (match _x_51 with | true ->
                        value false
                     | false ->
                        value true))

;;

let rec _range_52 = fun _m_53 ->
   value (fun _n_54 ->  (match run ((run (lift_binary (>) _m_53))
_n_54) with | true ->
               value []
            | false ->
               value (((::) (_m_53, run ((run (_range_52
                             (run ((run (lift_binary (+) _m_53)) 1)))) _n_54))))))

;;


let rec _map_62 = fun _f_63 ->  value (fun _gen_function_64 ->
   (match _gen_function_64 with | [] ->
                                   value []
                                | ((_x_65) :: (_xs_66)) ->
                                   (_f_63 _x_65) >>
                                   fun _y_67 ->
                                      ((run (_map_62 _f_63)) _xs_66) >>
                                      fun _ys_68 ->
                                         value (((::) (_y_67, _ys_68)))))

;;


let _ignore_70 = (fun _ ->  value ())

;;

let _take_71 = (fun _f_72 ->
   value (fun _k_73 ->  (run (_map_62 _f_72)) (run ((run (_range_52 0))
_k_73))))

;;

let rec _fold_left_77 = fun _f_78 ->  value (fun _a_79 ->
   value (fun _gen_function_80 ->
   (match _gen_function_80 with | [] ->
                                   value _a_79
                                | ((_y_81) :: (_ys_82)) ->
                                   (_f_78 _a_79) >>
                                   fun _gen_bind_84 ->
                                      (_gen_bind_84 _y_81) >>
                                      fun _a_83 ->  (run ((run (_fold_left_77
                                      _f_78)) _a_83)) _ys_82)))

;;


let rec _fold_right_87 = fun _f_88 ->  value (fun _xs_89 ->
   value (fun _a_90 ->
   (match _xs_89 with | [] ->
                         value _a_90
                      | ((_x_91) :: (_xs_92)) ->
                         ((run ((run (_fold_right_87 _f_88)) _xs_92)) _a_90)
                         >>
                         fun _a_93 ->
                            (_f_88 _x_91) >>
                            fun _gen_bind_96 ->  _gen_bind_96 _a_93)))

;;


let rec _iter_97 = fun _f_98 ->  value (fun _gen_function_99 ->
   (match _gen_function_99 with | [] ->
                                   value ()
                                | ((_x_100) :: (_xs_101)) ->
                                   (_f_98 _x_100) >>
                                   fun _ ->  (run (_iter_97 _f_98)) _xs_101))

;;


let rec _forall_103 = fun _p_104 ->  value (fun _gen_function_105 ->
   (match _gen_function_105 with | [] ->
                                    value true
                                 | ((_x_106) :: (_xs_107)) ->
                                    (_p_104 _x_106) >>
                                    fun _gen_bind_108 ->
                                       (match _gen_bind_108 with | true ->
                                                                    (run (_forall_103
                                                                 _p_104))
                                                                 _xs_107
                                                                 | false ->
                                                                    value false)))

;;


let rec _exists_110 = fun _p_111 ->  value (fun _gen_function_112 ->
   (match _gen_function_112 with | [] ->
                                    value false
                                 | ((_x_113) :: (_xs_114)) ->
                                    (_p_111 _x_113) >>
                                    fun _gen_bind_115 ->
                                       (match _gen_bind_115 with | true ->
                                                                    value true
                                                                 | false ->
                                                                    (run (_exists_110
                                                                 _p_111))
                                                                 _xs_114)))

;;


let _mem_117 = (fun _x_118 ->  _exists_110 (fun _x'_119 ->
   (run (lift_binary (=) _x_118)) _x'_119))

;;


let rec _filter_121 = fun _p_122 ->  value (fun _gen_function_123 ->
   (match _gen_function_123 with | [] ->
                                    value []
                                 | ((_x_124) :: (_xs_125)) ->
                                    (_p_122 _x_124) >>
                                    fun _gen_bind_126 ->
                                       (match _gen_bind_126 with | true ->
                                                                    ((run (_filter_121
                                                                    _p_122))
                                                                    _xs_125)
                                                                    >>
                                                                    fun _gen_bind_127 ->
                                                                     value (((::) (
                                                                    _x_124, 
                                                                    _gen_bind_127)))
                                                                 | false ->
                                                                    (run (_filter_121
                                                                 _p_122))
                                                                 _xs_125)))

;;


let rec _zip_130 = fun _xs_131 ->  value (fun _ys_132 ->
   (match (_xs_131, _ys_132) with | ([], []) ->
                                     value []
                                  | (((_x_133) :: (_xs_134)), 
                                     ((_y_135) :: (_ys_136))) ->
                                     ((run (_zip_130 _xs_134)) _ys_136) >>
                                     fun _gen_bind_137 ->
                                        value (((::) ((_x_133, _y_135), 
                                                      _gen_bind_137)))
                                  | (_, _) ->
                                     call Effect_InvalidArgument "zip: length mismatch" (
                                  fun _result_12 ->  _absurd_8 _result_12)))

;;


let _reverse_140 = (fun _lst_141 ->
   let rec _reverse_acc_142 = fun _acc_143 ->
              value (fun _gen_function_144 ->
              (match _gen_function_144 with | [] ->
                                               value _acc_143
                                            | ((_x_145) :: (_xs_146)) ->
                                               (run (_reverse_acc_142
                                            (((::) (_x_145, _acc_143)))))
                                            _xs_146)) in (run (_reverse_acc_142
[])) _lst_141)

;;

let rec _var_149 (* @ *) = fun _xs_150 ->
   value (fun _ys_151 ->
   (match _xs_150 with | [] ->
                          value _ys_151
                       | ((_x_152) :: (_xs_153)) ->
                          value (((::) (_x_152, run ((run (_var_149 (* @ *)
                                        _xs_153)) _ys_151))))))

;;


let rec _length_156 = fun _gen_let_rec_function_157 ->
   (match _gen_let_rec_function_157 with | [] ->
                                            value 0
                                         | ((_x_158) :: (_xs_159)) ->
                                            (run (lift_binary (+)
                                         (run (_length_156
                                         _xs_159))))
                                         1)

;;


let _head_162 = (fun _gen_function_163 ->
   (match _gen_function_163 with | [] ->
                                    call Effect_InvalidArgument "head: empty list" (
                                 fun _result_15 ->  _absurd_8 _result_15)
                                 | ((_x_165) :: (_)) ->
                                    value _x_165))

;;


let _tail_166 = (fun _gen_function_167 ->
   (match _gen_function_167 with | [] ->
                                    call Effect_InvalidArgument "tail: empty list" (
                                 fun _result_18 ->  _absurd_8 _result_18)
                                 | ((_x_169) :: (_xs_170)) ->
                                    value _xs_170))

;;


let _hd_171 = _head_162

;;

let _tl_172 = _tail_166

;;


let _abs_173 = (fun _x_174 ->  (match run ((run (lift_binary (<) _x_174))
0) with | true ->
           lift_unary (~-)
        _x_174
        | false ->
           value _x_174))

;;

let _min_177 = (fun _x_178 ->
   value (fun _y_179 ->  (match run ((run (lift_binary (<) _x_178))
_y_179) with | true ->
                value _x_178
             | false ->
                value _y_179)))

;;

let _max_182 = (fun _x_183 ->
   value (fun _y_184 ->  (match run ((run (lift_binary (<) _x_183))
_y_184) with | true ->
                value _y_184
             | false ->
                value _x_183)))

;;

let _odd_187 = (fun _x_188 ->
   ((run (_mod_18 _x_188)) 2) >>
   fun _gen_bind_190 ->  (run (lift_binary (=) _gen_bind_190)) 1)

;;


let _even_192 = (fun _x_193 ->
   ((run (_mod_18 _x_193)) 2) >>
   fun _gen_bind_195 ->  (run (lift_binary (=) _gen_bind_195)) 0)

;;


let _id_197 = (fun _x_198 ->  value _x_198)

;;


let _compose_199 = (fun _f_200 ->  value (fun _g_201 ->  value (fun _x_202 ->
   (_g_201 _x_202) >> fun _gen_bind_203 ->  _f_200 _gen_bind_203)))

;;


let _fst_204 = (fun (_x_205, _) ->  value _x_205)

;;


let _snd_206 = (fun (_, _y_207) ->  value _y_207)

;;


let _print_208 = (fun _v_209 ->  call Effect_Print (run (_to_string_40
_v_209)) (fun _result_20 ->  value _result_20))

;;


let _print_string_211 = (fun _str_212 ->
   call Effect_Print _str_212 (fun _result_22 ->  value _result_22))

;;


let _print_endline_213 = (fun _v_214 ->
   call Effect_Print (run (_to_string_40
_v_214)) (fun _result_27 ->
             call Effect_Print "\n" (fun _result_24 ->  value _result_24)))

;;


type (_, _) effect += Effect_Lookup : ( unit,  int) effect

;;


type (_, _) effect += Effect_Update : ( int,  unit) effect

;;


value "End of pervasives"

;;

let _absurd_216 = (fun _void_217 ->
   (match _void_217 with _ -> assert false))

;;


let _var_218 (* = *) x = lift_binary ( = ) x

;;


let _var_219 (* + *) x = lift_binary ( + ) x

;;


let _var_220 (* * *) x = lift_binary ( * ) x

;;


let _var_221 (* - *) x = lift_binary ( - ) x

;;


let _var_222 (* ~- *) x = lift_unary ( ~- ) x

;;


let _var_223 (* / *) x = lift_binary ( / ) x

;;


let rec _var_224 (* @ *) = fun _xs_225 ->  value (fun _ys_226 ->
   (match _xs_225 with | [] ->
                          value _ys_226
                       | ((_x_227) :: (_xs_228)) ->
                          value (((::) (_x_227, run ((run (_var_224 (* @ *)
                                        _xs_228)) _ys_226))))))

;;


type  num =  int

;;

type  func = ( int -> ( int) computation)

;;


type  loc =  int

;;

type  name =  string

;;

type  env = (( string*
 int)) list

;;


type  term = Num of ( int)|Add of (( term* term))|Mul of (( term* term))|
             Sub of (( term* term))|Div of (( term* term))

;;


type (_, _) effect += Effect_VarNotFound : ( unit, unit) effect

;;


type (_, _) effect += Effect_Arith_DivByZero : ( unit,  int) effect

;;


let rec _interp_231 = fun _a_232 ->
   (match _a_232 with | (Num _b_233) ->
                         value _b_233
                      | (Add (_l_234, _r_235)) ->
                         (_interp_231 _l_234) >>
                         fun _x_236 ->
                            (_interp_231 _r_235) >>
                            fun _y_237 ->  (run (lift_binary (+) _x_236))
                            _y_237
                      | (Mul (_l_239, _r_240)) ->
                         (_interp_231 _l_239) >>
                         fun _x_241 ->
                            (_interp_231 _r_240) >>
                            fun _y_242 ->  (run (lift_binary ( * ) _x_241))
                            _y_242
                      | (Sub (_l_244, _r_245)) ->
                         (_interp_231 _l_244) >>
                         fun _x_246 ->
                            (_interp_231 _r_245) >>
                            fun _y_247 ->  (run (lift_binary (-) _x_246))
                            _y_247
                      | (Div (_l_249, _r_250)) ->
                         (_interp_231 _r_250) >>
                         fun _r_num_251 ->
                            (_interp_231 _l_249) >>
                            fun _l_num_252 ->
                               (match _r_num_251 with | 0 ->
                                                         call Effect_Arith_DivByZero () (
                                                      fun _result_29 ->
                                                         value _result_29)
                                                      | _ ->
                                                         (run (lift_binary (/)
                                                      _l_num_252))
                                                      _r_num_251))

;;


let _arithmeticHandler_254 = (fun c -> handler { value_clause = (fun _gen_id_par_264 ->
                                                                    value _gen_id_par_264);
                                                effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_255 :  int -> _ computation) -> lift_unary (~-)
                                                1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c)

;;


let _addCase_256 = ((Add ((Add ((Add ((Num 20), (Num 2))), 
                                (Mul ((Num 1), (Num 2))))), 
                          (Sub ((Add ((Num 2), (Num 2))), 
                                (Add ((Num 1), (Num 2))))))))

;;


let rec _createCase_257 = fun _n_258 ->
   (match _n_258 with | 1 ->
                         value ((Div ((Num 100), (Num 10))))
                      | _ ->
                         value ((Add (_addCase_256, run (_createCase_257
                                      (run ((run (lift_binary (-) _n_258))
                                      1)))))))

;;


let _finalCase_262 = run (_createCase_257 200)

;;


let bigTest = (fun () ->
   let rec _interp_32 = fun _a_232 ->
              (match _a_232 with | (Num _b_233) ->
                                    value _b_233
                                 | (Add (_l_234, _r_235)) ->
                                    let rec _new_special_var_169 = fun (
                                            _a_232, _k_val_168) ->
                                               (match _a_232 with | (Num 
                                                                  _b_233) ->
                                                                     _k_val_168
                                                                  _b_233
                                                                  | (Add 
                                                                  (_l_234, 
                                                                   _r_235)) ->
                                                                     _new_special_var_169
                                                                  (_l_234, 
                                                                   fun _x_185 ->
                                                                     _new_special_var_169
                                                                   (_r_235, 
                                                                    fun _y_186 ->
                                                                     _k_val_168
                                                                    (run ((run (lift_binary (+)
                                                                    _x_185))
                                                                    _y_186))))
                                                                  | (Mul 
                                                                  (_l_239, 
                                                                   _r_240)) ->
                                                                     _new_special_var_169
                                                                  (_l_239, 
                                                                   fun _x_200 ->
                                                                     _new_special_var_169
                                                                   (_r_240, 
                                                                    fun _y_201 ->
                                                                     _k_val_168
                                                                    (run ((run (lift_binary ( * )
                                                                    _x_200))
                                                                    _y_201))))
                                                                  | (Sub 
                                                                  (_l_244, 
                                                                   _r_245)) ->
                                                                     _new_special_var_169
                                                                  (_l_244, 
                                                                   fun _x_215 ->
                                                                     _new_special_var_169
                                                                   (_r_245, 
                                                                    fun _y_216 ->
                                                                     _k_val_168
                                                                    (run ((run (lift_binary (-)
                                                                    _x_215))
                                                                    _y_216))))
                                                                  | (Div 
                                                                  (_l_249, 
                                                                   _r_250)) ->
                                                                     _new_special_var_169
                                                                  (_r_250, 
                                                                   fun _r_num_242 ->
                                                                     _new_special_var_169
                                                                   (_l_249, 
                                                                    fun _l_num_243 ->
                                                                     (match _r_num_242 with 
                                                                    | 0 ->
                                                                     lift_unary (~-)
                                                                    1
                                                                    | _ ->
                                                                     _k_val_168
                                                                    (run ((run (lift_binary (/)
                                                                    _l_num_243))
                                                                    _r_num_242)))))) in _new_special_var_169
                                 (_l_234, fun _x_145 ->
                                     let rec _new_special_var_146 = fun (
                                             _a_148, _k_val_147) ->
                                                (match _a_148 with | (Num 
                                                                   _b_149) ->
                                                                     _k_val_147
                                                                   _b_149
                                                                   | (Add 
                                                                   (_l_151, 
                                                                    _r_150)) ->
                                                                     _new_special_var_146
                                                                   (_l_151, 
                                                                    fun _x_152 ->
                                                                     _new_special_var_146
                                                                    (
                                                                    _r_150, 
                                                                    fun _y_153 ->
                                                                     _k_val_147
                                                                    (run ((run (lift_binary (+)
                                                                    _x_152))
                                                                    _y_153))))
                                                                   | (Mul 
                                                                   (_l_155, 
                                                                    _r_154)) ->
                                                                     _new_special_var_146
                                                                   (_l_155, 
                                                                    fun _x_156 ->
                                                                     _new_special_var_146
                                                                    (
                                                                    _r_154, 
                                                                    fun _y_157 ->
                                                                     _k_val_147
                                                                    (run ((run (lift_binary ( * )
                                                                    _x_156))
                                                                    _y_157))))
                                                                   | (Sub 
                                                                   (_l_159, 
                                                                    _r_158)) ->
                                                                     _new_special_var_146
                                                                   (_l_159, 
                                                                    fun _x_160 ->
                                                                     _new_special_var_146
                                                                    (
                                                                    _r_158, 
                                                                    fun _y_161 ->
                                                                     _k_val_147
                                                                    (run ((run (lift_binary (-)
                                                                    _x_160))
                                                                    _y_161))))
                                                                   | (Div 
                                                                   (_l_163, 
                                                                    _r_162)) ->
                                                                     _new_special_var_146
                                                                   (_r_162, 
                                                                    fun _r_num_164 ->
                                                                     _new_special_var_146
                                                                    (
                                                                    _l_163, 
                                                                    fun _l_num_165 ->
                                                                     (match _r_num_164 with 
                                                                    | 0 ->
                                                                     lift_unary (~-)
                                                                    1
                                                                    | _ ->
                                                                     _k_val_147
                                                                    (run ((run (lift_binary (/)
                                                                    _l_num_165))
                                                                    _r_num_164)))))) in _new_special_var_146
                                  (_r_235, fun _y_166 ->
                                      value (run ((run (lift_binary (+)
                                   _x_145)) _y_166))))
                                 | (Mul (_l_239, _r_240)) ->
                                    (fun c -> handler { value_clause = (
                                                       fun _x_321 ->
                                                          let rec _new_special_var_322 = fun (
                                                                  _a_324, 
                                                                  _k_val_323) ->
                                                                     (match _a_324 with 
                                                                  | (Num 
                                                                  _b_325) ->
                                                                     _k_val_323
                                                                  _b_325
                                                                  | (Add 
                                                                  (_l_327, 
                                                                   _r_326)) ->
                                                                     _new_special_var_322
                                                                  (_l_327, 
                                                                   fun _x_328 ->
                                                                     _new_special_var_322
                                                                   (_r_326, 
                                                                    fun _y_329 ->
                                                                     _k_val_323
                                                                    (run ((run (lift_binary (+)
                                                                    _x_328))
                                                                    _y_329))))
                                                                  | (Mul 
                                                                  (_l_331, 
                                                                   _r_330)) ->
                                                                     _new_special_var_322
                                                                  (_l_331, 
                                                                   fun _x_332 ->
                                                                     _new_special_var_322
                                                                   (_r_330, 
                                                                    fun _y_333 ->
                                                                     _k_val_323
                                                                    (run ((run (lift_binary ( * )
                                                                    _x_332))
                                                                    _y_333))))
                                                                  | (Sub 
                                                                  (_l_335, 
                                                                   _r_334)) ->
                                                                     (fun c -> handler {
                                                                   value_clause = (
                                                                  fun _vcvar_339 ->
                                                                     _k_val_323
                                                                  _vcvar_339);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_340 :  int -> _ computation) -> lift_unary (~-)
                                                                  1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c) (
                                                                  (_interp_231
                                                                  _l_335) >>
                                                                  fun _x_336 ->
                                                                     
                                                                  (_interp_231
                                                                  _r_334) >>
                                                                  fun _y_337 ->
                                                                     
                                                                  (_var_221 (* - *)
                                                                  _x_336) >>
                                                                  fun _gen_bind_338 ->
                                                                     _gen_bind_338
                                                                  _y_337)
                                                                  | (Div 
                                                                  (_l_342, 
                                                                   _r_341)) ->
                                                                     (fun c -> handler {
                                                                   value_clause = (
                                                                  fun _vcvar_346 ->
                                                                     _k_val_323
                                                                  _vcvar_346);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_347 :  int -> _ computation) -> lift_unary (~-)
                                                                  1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c) (
                                                                  (_interp_231
                                                                  _r_341) >>
                                                                  fun _r_num_343 ->
                                                                     
                                                                  (_interp_231
                                                                  _l_342) >>
                                                                  fun _l_num_344 ->
                                                                     (match _r_num_343 with 
                                                                  | 0 ->
                                                                     (effect Effect_Arith_DivByZero)
                                                                  ()
                                                                  | _ ->
                                                                     
                                                                  (_var_223 (* / *)
                                                                  _l_num_344)
                                                                  >>
                                                                  fun _gen_bind_345 ->
                                                                     _gen_bind_345
                                                                  _r_num_343))) in _new_special_var_322
                                                       (_r_240, fun _y_348 ->
                                                           value (run ((run (lift_binary ( * )
                                                        _x_321)) _y_348))));
                                                       effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_349 :  int -> _ computation) -> lift_unary (~-)
                                                       1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c) (_interp_231
                                 _l_239)
                                 | (Sub (_l_244, _r_245)) ->
                                    (fun c -> handler { value_clause = (
                                                       fun _gen_id_par_350 ->
                                                          value _gen_id_par_350);
                                                       effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_351 :  int -> _ computation) -> lift_unary (~-)
                                                       1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c) (
                                 (_interp_231 _l_244) >>
                                 fun _x_246 ->
                                    (_interp_231 _r_245) >>
                                    fun _y_247 ->  (run (lift_binary (-)
                                    _x_246)) _y_247)
                                 | (Div (_l_249, _r_250)) ->
                                    (fun c -> handler { value_clause = (
                                                       fun _gen_id_par_352 ->
                                                          value _gen_id_par_352);
                                                       effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_353 :  int -> _ computation) -> lift_unary (~-)
                                                       1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c) (
                                 (_interp_231 _r_250) >>
                                 fun _r_num_251 ->
                                    (_interp_231 _l_249) >>
                                    fun _l_num_252 ->
                                       (match _r_num_251 with | 0 ->
                                                                 call Effect_Arith_DivByZero () (
                                                              fun _result_34 ->
                                                                 value _result_34)
                                                              | _ ->
                                                                 (run (lift_binary (/)
                                                              _l_num_252))
                                                              _r_num_251))) in _interp_32
_finalCase_262)
