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
   ((effect Effect_Failure) _msg_11) >>
   fun _gen_bind_12 ->  _absurd_8 _gen_bind_12)

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
                        ((effect Effect_DivisionByZero) ()) >>
                        fun _gen_bind_21 ->  _absurd_8 _gen_bind_21
                     | _n_22 ->
                        (_mod_17 _m_19) >>
                        fun _gen_bind_23 ->  _gen_bind_23 _n_22)))

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
                        ((effect Effect_DivisionByZero) ()) >>
                        fun _gen_bind_34 ->  _absurd_8 _gen_bind_34
                     | _n_35 ->
                        (_var_29 (* / *) _m_32) >>
                        fun _gen_bind_36 ->  _gen_bind_36 _n_35)))

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
                                   ((_var_1 (* = *) _x_42) >>
                                    fun _gen_bind_48 ->  _gen_bind_48 _y_44)
                                   >>
                                   fun _gen_bind_47 ->
                                      (match _gen_bind_47 with | true ->
                                                                  value ((Some _z_45))
                                                               | false ->
                                                                  (_assoc_41
                                                                  _x_42) >>
                                                                  fun _gen_bind_49 ->
                                                                     _gen_bind_49
                                                                  _lst_46)))

;;


let _not_50 = (fun _x_51 ->
   (match _x_51 with | true ->
                        value false
                     | false ->
                        value true))

;;

let rec _range_52 = fun _m_53 ->
   value (fun _n_54 ->
   ((_var_3 (* > *) _m_53) >> fun _gen_bind_56 ->  _gen_bind_56 _n_54) >>
   fun _gen_bind_55 ->
      (match _gen_bind_55 with | true ->
                                  value []
                               | false ->
                                  let _r_57 = _range_52 in
                               ((((_var_14 (* + *) _m_53) >>
                                  fun _gen_bind_61 ->  _gen_bind_61 1) >>
                                 fun _gen_bind_60 ->  _r_57 _gen_bind_60) >>
                                fun _gen_bind_59 ->  _gen_bind_59 _n_54) >>
                               fun _gen_bind_58 ->
                                  value (((::) (_m_53, _gen_bind_58)))))

;;


let rec _map_62 = fun _f_63 ->  value (fun _gen_function_64 ->
   (match _gen_function_64 with | [] ->
                                   value []
                                | ((_x_65) :: (_xs_66)) ->
                                   (_f_63 _x_65) >>
                                   fun _y_67 ->
                                      ((_map_62 _f_63) >>
                                       fun _gen_bind_69 ->  _gen_bind_69
                                       _xs_66) >>
                                      fun _ys_68 ->
                                         value (((::) (_y_67, _ys_68)))))

;;


let _ignore_70 = (fun _ ->  value ())

;;

let _take_71 = (fun _f_72 ->
   value (fun _k_73 ->
   ((_range_52 0) >> fun _gen_bind_75 ->  _gen_bind_75 _k_73) >>
   fun _r_74 ->  (_map_62 _f_72) >> fun _gen_bind_76 ->  _gen_bind_76 _r_74))

;;


let rec _fold_left_77 = fun _f_78 ->  value (fun _a_79 ->
   value (fun _gen_function_80 ->
   (match _gen_function_80 with | [] ->
                                   value _a_79
                                | ((_y_81) :: (_ys_82)) ->
                                   ((_f_78 _a_79) >>
                                    fun _gen_bind_84 ->  _gen_bind_84 _y_81)
                                   >>
                                   fun _a_83 ->
                                      ((_fold_left_77 _f_78) >>
                                       fun _gen_bind_86 ->  _gen_bind_86
                                       _a_83) >>
                                      fun _gen_bind_85 ->  _gen_bind_85
                                      _ys_82)))

;;


let rec _fold_right_87 = fun _f_88 ->  value (fun _xs_89 ->
   value (fun _a_90 ->
   (match _xs_89 with | [] ->
                         value _a_90
                      | ((_x_91) :: (_xs_92)) ->
                         (((_fold_right_87 _f_88) >>
                           fun _gen_bind_95 ->  _gen_bind_95 _xs_92) >>
                          fun _gen_bind_94 ->  _gen_bind_94 _a_90) >>
                         fun _a_93 ->
                            (_f_88 _x_91) >>
                            fun _gen_bind_96 ->  _gen_bind_96 _a_93)))

;;


let rec _iter_97 = fun _f_98 ->  value (fun _gen_function_99 ->
   (match _gen_function_99 with | [] ->
                                   value ()
                                | ((_x_100) :: (_xs_101)) ->
                                   (_f_98 _x_100) >>
                                   fun _ ->
                                      (_iter_97 _f_98) >>
                                      fun _gen_bind_102 ->  _gen_bind_102
                                      _xs_101))

;;


let rec _forall_103 = fun _p_104 ->  value (fun _gen_function_105 ->
   (match _gen_function_105 with | [] ->
                                    value true
                                 | ((_x_106) :: (_xs_107)) ->
                                    (_p_104 _x_106) >>
                                    fun _gen_bind_108 ->
                                       (match _gen_bind_108 with | true ->
                                                                    (_forall_103
                                                                    _p_104)
                                                                    >>
                                                                    fun _gen_bind_109 ->
                                                                     _gen_bind_109
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
                                                                    (_exists_110
                                                                    _p_111)
                                                                    >>
                                                                    fun _gen_bind_116 ->
                                                                     _gen_bind_116
                                                                    _xs_114)))

;;


let _mem_117 = (fun _x_118 ->  _exists_110 (fun _x'_119 ->
   (_var_1 (* = *) _x_118) >> fun _gen_bind_120 ->  _gen_bind_120 _x'_119))

;;


let rec _filter_121 = fun _p_122 ->  value (fun _gen_function_123 ->
   (match _gen_function_123 with | [] ->
                                    value []
                                 | ((_x_124) :: (_xs_125)) ->
                                    (_p_122 _x_124) >>
                                    fun _gen_bind_126 ->
                                       (match _gen_bind_126 with | true ->
                                                                    (
                                                                    (_filter_121
                                                                    _p_122)
                                                                    >>
                                                                    fun _gen_bind_128 ->
                                                                     _gen_bind_128
                                                                    _xs_125)
                                                                    >>
                                                                    fun _gen_bind_127 ->
                                                                     value (((::) (
                                                                    _x_124, 
                                                                    _gen_bind_127)))
                                                                 | false ->
                                                                    (_filter_121
                                                                    _p_122)
                                                                    >>
                                                                    fun _gen_bind_129 ->
                                                                     _gen_bind_129
                                                                    _xs_125)))

;;


let rec _zip_130 = fun _xs_131 ->  value (fun _ys_132 ->
   (match (_xs_131, _ys_132) with | ([], []) ->
                                     value []
                                  | (((_x_133) :: (_xs_134)), 
                                     ((_y_135) :: (_ys_136))) ->
                                     ((_zip_130 _xs_134) >>
                                      fun _gen_bind_138 ->  _gen_bind_138
                                      _ys_136) >>
                                     fun _gen_bind_137 ->
                                        value (((::) ((_x_133, _y_135), 
                                                      _gen_bind_137)))
                                  | (_, _) ->
                                     ((effect Effect_InvalidArgument)
                                     "zip: length mismatch") >>
                                     fun _gen_bind_139 ->  _absurd_8
                                     _gen_bind_139))

;;


let _reverse_140 = (fun _lst_141 ->
   let rec _reverse_acc_142 = fun _acc_143 ->
              value (fun _gen_function_144 ->
              (match _gen_function_144 with | [] ->
                                               value _acc_143
                                            | ((_x_145) :: (_xs_146)) ->
                                               (_reverse_acc_142
                                               (((::) (_x_145, _acc_143))))
                                               >>
                                               fun _gen_bind_147 ->
                                                  _gen_bind_147
                                               _xs_146)) in (_reverse_acc_142
                                                            []) >>
                                                            fun _gen_bind_148 ->
                                                               _gen_bind_148
                                                            _lst_141)

;;


let rec _var_149 (* @ *) = fun _xs_150 ->  value (fun _ys_151 ->
   (match _xs_150 with | [] ->
                          value _ys_151
                       | ((_x_152) :: (_xs_153)) ->
                          ((_var_149 (* @ *) _xs_153) >>
                           fun _gen_bind_155 ->  _gen_bind_155 _ys_151) >>
                          fun _gen_bind_154 ->
                             value (((::) (_x_152, _gen_bind_154)))))

;;


let rec _length_156 = fun _gen_let_rec_function_157 ->
   (match _gen_let_rec_function_157 with | [] ->
                                            value 0
                                         | ((_x_158) :: (_xs_159)) ->
                                            ((_length_156 _xs_159) >>
                                             fun _gen_bind_161 ->
                                                _var_14 (* + *)
                                             _gen_bind_161) >>
                                            fun _gen_bind_160 ->
                                               _gen_bind_160
                                            1)

;;


let _head_162 = (fun _gen_function_163 ->
   (match _gen_function_163 with | [] ->
                                    ((effect Effect_InvalidArgument)
                                    "head: empty list") >>
                                    fun _gen_bind_164 ->  _absurd_8
                                    _gen_bind_164
                                 | ((_x_165) :: (_)) ->
                                    value _x_165))

;;


let _tail_166 = (fun _gen_function_167 ->
   (match _gen_function_167 with | [] ->
                                    ((effect Effect_InvalidArgument)
                                    "tail: empty list") >>
                                    fun _gen_bind_168 ->  _absurd_8
                                    _gen_bind_168
                                 | ((_x_169) :: (_xs_170)) ->
                                    value _xs_170))

;;


let _hd_171 = _head_162

;;

let _tl_172 = _tail_166

;;


let _abs_173 = (fun _x_174 ->
   ((_var_2 (* < *) _x_174) >> fun _gen_bind_176 ->  _gen_bind_176 0) >>
   fun _gen_bind_175 ->
      (match _gen_bind_175 with | true ->
                                   _var_13 (* ~- *)
                                _x_174
                                | false ->
                                   value _x_174))

;;


let _min_177 = (fun _x_178 ->  value (fun _y_179 ->
   ((_var_2 (* < *) _x_178) >> fun _gen_bind_181 ->  _gen_bind_181 _y_179) >>
   fun _gen_bind_180 ->
      (match _gen_bind_180 with | true ->
                                   value _x_178
                                | false ->
                                   value _y_179)))

;;


let _max_182 = (fun _x_183 ->  value (fun _y_184 ->
   ((_var_2 (* < *) _x_183) >> fun _gen_bind_186 ->  _gen_bind_186 _y_184) >>
   fun _gen_bind_185 ->
      (match _gen_bind_185 with | true ->
                                   value _y_184
                                | false ->
                                   value _x_183)))

;;


let _odd_187 = (fun _x_188 ->
   (((_mod_18 _x_188) >> fun _gen_bind_191 ->  _gen_bind_191 2) >>
    fun _gen_bind_190 ->  _var_1 (* = *) _gen_bind_190) >>
   fun _gen_bind_189 ->  _gen_bind_189 1)

;;

let _even_192 = (fun _x_193 ->
   (((_mod_18 _x_193) >> fun _gen_bind_196 ->  _gen_bind_196 2) >>
    fun _gen_bind_195 ->  _var_1 (* = *) _gen_bind_195) >>
   fun _gen_bind_194 ->  _gen_bind_194 0)

;;

let _id_197 = (fun _x_198 ->
   value _x_198)

;;

let _compose_199 = (fun _f_200 ->  value (fun _g_201 ->
   value (fun _x_202 ->
   (_g_201 _x_202) >> fun _gen_bind_203 ->  _f_200 _gen_bind_203)))

;;


let _fst_204 = (fun (_x_205, _) ->  value _x_205)

;;


let _snd_206 = (fun (_, _y_207) ->  value _y_207)

;;


let _print_208 = (fun _v_209 ->
   (_to_string_40 _v_209) >> fun _s_210 ->  (effect Effect_Print) _s_210)

;;


let _print_string_211 = (fun _str_212 ->  (effect Effect_Print)
_str_212)

;;

let _print_endline_213 = (fun _v_214 ->
   (_to_string_40 _v_214) >>
   fun _s_215 ->
      ((effect Effect_Print) _s_215) >> fun _ ->  (effect Effect_Print) "\n")

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
                          ((_var_224 (* @ *) _xs_228) >>
                           fun _gen_bind_230 ->  _gen_bind_230 _ys_226) >>
                          fun _gen_bind_229 ->
                             value (((::) (_x_227, _gen_bind_229)))))

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
             Sub of (( term* term))|Div of (( term* term))|Ref of ( term)|
             Deref of ( term)|Assign of (( term* term))|Var of ( string)|
             App of (( termF* term))
and

 termF = LambdaV of (( string* term))|LambdaL of (( string* term))

;;


type (_, _) effect += Effect_VarNotFound : ( unit, unit) effect

;;


type (_, _) effect += Effect_Arith_DivByZero : ( unit,  int) effect

;;


type (_, _) effect += Effect_ReadEnv : ( unit,  env) effect

;;


type (_, _) effect += Effect_InEnv : (( env* int),  int) effect

;;


type (_, _) effect += Effect_SetEnv : ( env,  env) effect

;;


type (_, _) effect += Effect_AllocLoc : ( unit,  loc) effect

;;


type (_, _) effect += Effect_LookupLoc : ( loc,  int) effect

;;


type (_, _) effect += Effect_UpdateLoc : (( loc* int),  loc) effect

;;


let rec _lookupState_231 = fun (_x_232, _y_233) ->
   (match _y_233 with | [] ->
                         ((effect Effect_VarNotFound) ()) >>
                         fun _gen_bind_234 ->  _absurd_216 _gen_bind_234
                      | (((_x'_235, _y_236)) :: (_lst_237)) ->
                         ((_var_218 (* = *) _x_232) >>
                          fun _gen_bind_239 ->  _gen_bind_239 _x'_235) >>
                         fun _gen_bind_238 ->
                            (match _gen_bind_238 with | true ->
                                                         value _y_236
                                                      | false ->
                                                         _lookupState_231
                                                      (_x_232, _lst_237)))

;;


let _updateState_240 = (fun (_k_241, _v_242, _env_243) ->
   value (((::) ((_k_241, _v_242), _env_243))))

;;


let rec _checkLoc_244 = fun (_x_245, _env_246) ->
   (match _env_246 with | [] ->
                           value false
                        | (((_x'_247, _y_248)) :: (_lst_249)) ->
                           ((_var_218 (* = *) _x_245) >>
                            fun _gen_bind_251 ->  _gen_bind_251 _x'_247) >>
                           fun _gen_bind_250 ->
                              (match _gen_bind_250 with | true ->
                                                           value true
                                                        | false ->
                                                           _checkLoc_244
                                                        (_x_245, _lst_249)))

;;


let rec _createLoc_252 = fun (_i_253, _env_254) ->
   (_checkLoc_244 (_i_253, _env_254)) >>
   fun _gen_bind_255 ->
      (match _gen_bind_255 with | true ->
                                   ((_var_219 (* + *) _i_253) >>
                                    fun _gen_bind_257 ->  _gen_bind_257 1) >>
                                   fun _gen_bind_256 ->  _createLoc_252
                                   (_gen_bind_256, _env_254)
                                | false ->
                                   value _i_253)

;;


let _getNewLoc_258 = (fun _env_259 ->  _createLoc_252 (0, _env_259))

;;


let rec _lookupEnv_260 = fun (_x_261, _y_262) ->
   (match _y_262 with | [] ->
                         ((effect Effect_VarNotFound) ()) >>
                         fun _gen_bind_263 ->  _absurd_216 _gen_bind_263
                      | (((_x'_264, _y_265)) :: (_lst_266)) ->
                         ((_var_218 (* = *) _x_261) >>
                          fun _gen_bind_268 ->  _gen_bind_268 _x'_264) >>
                         fun _gen_bind_267 ->
                            (match _gen_bind_267 with | true ->
                                                         value _y_265
                                                      | false ->
                                                         _lookupState_231
                                                      (_x_261, _lst_266)))

;;


let _extendEnv_269 = (fun (_k_270, _v_271, _env_272) ->
   value (((::) ((_k_270, _v_271), _env_272))))

;;


let rec _interp_273 = fun _a_274 ->
   (match _a_274 with | (Num _b_275) ->
                         value _b_275
                      | (Add (_l_276, _r_277)) ->
                         (_interp_273 _l_276) >>
                         fun _x_278 ->
                            (_interp_273 _r_277) >>
                            fun _y_279 ->
                               (_var_219 (* + *) _x_278) >>
                               fun _gen_bind_280 ->  _gen_bind_280 _y_279
                      | (Mul (_l_281, _r_282)) ->
                         (_interp_273 _l_281) >>
                         fun _x_283 ->
                            (_interp_273 _r_282) >>
                            fun _y_284 ->
                               (_var_220 (* * *) _x_283) >>
                               fun _gen_bind_285 ->  _gen_bind_285 _y_284
                      | (Sub (_l_286, _r_287)) ->
                         (_interp_273 _l_286) >>
                         fun _x_288 ->
                            (_interp_273 _r_287) >>
                            fun _y_289 ->
                               (_var_221 (* - *) _x_288) >>
                               fun _gen_bind_290 ->  _gen_bind_290 _y_289
                      | (Div (_l_291, _r_292)) ->
                         (_interp_273 _r_292) >>
                         fun _r_num_293 ->
                            (_interp_273 _l_291) >>
                            fun _l_num_294 ->
                               (_var_223 (* / *) _l_num_294) >>
                               fun _gen_bind_295 ->  _gen_bind_295 _r_num_293
                      | (Ref _x_296) ->
                         (_interp_273 _x_296) >>
                         fun _x_interp_297 ->
                            ((effect Effect_AllocLoc) ()) >>
                            fun _x_loc_298 ->  (effect Effect_UpdateLoc)
                            (_x_loc_298, _x_interp_297)
                      | (Deref _x_299) ->
                         (_interp_273 _x_299) >>
                         fun _x_interp_300 ->  (effect Effect_LookupLoc)
                         _x_interp_300
                      | (Assign (_lhs_301, _rhs_302)) ->
                         (_interp_273 _lhs_301) >>
                         fun _x_loc_303 ->
                            (_interp_273 _rhs_302) >>
                            fun _x_interp_304 ->
                               ((effect Effect_UpdateLoc)
                               (_x_loc_303, _x_interp_304)) >>
                               fun _ ->  value _x_interp_304
                      | (Var _v_305) ->
                         ((effect Effect_ReadEnv) ()) >>
                         fun _gen_bind_306 ->  _lookupEnv_260
                         (_v_305, _gen_bind_306)
                      | (App (_e1_307, _e2_308)) ->
                         ((match _e1_307 with | (LambdaV (_s_310, _t_311)) ->
                                                 ((effect Effect_ReadEnv) ())
                                                 >>
                                                 fun _envi_312 ->
                                                    value (fun _v_313 ->
                                                    (_extendEnv_269
                                                    (_s_310, _v_313, 
                                                     _envi_312)) >>
                                                    fun _ext_314 ->
                                                       ((effect Effect_SetEnv)
                                                       _ext_314) >>
                                                       fun _ext_2_315 ->
                                                          (_interp_273
                                                          _t_311) >>
                                                          fun _t_res_316 ->
                                                             (effect Effect_InEnv)
                                                          (_ext_2_315, 
                                                           _t_res_316))
                                              | (LambdaL (_s_317, _t_318)) ->
                                                 ((effect Effect_ReadEnv) ())
                                                 >>
                                                 fun _envi_319 ->
                                                    value (fun _v_320 ->
                                                    ((effect Effect_AllocLoc)
                                                    ()) >>
                                                    fun _x_loc_321 ->
                                                       (((effect Effect_UpdateLoc)
                                                        (_x_loc_321, _v_320))
                                                        >>
                                                        fun _ ->
                                                           value _v_320) >>
                                                       fun _thunk_322 ->
                                                          ((effect Effect_UpdateLoc)
                                                          (_x_loc_321, 
                                                           _thunk_322)) >>
                                                          fun _tmp_323 ->
                                                             (((effect Effect_LookupLoc)
                                                              _x_loc_321) >>
                                                              fun _gen_bind_325 ->
                                                                 _extendEnv_269
                                                              (_s_317, 
                                                               _gen_bind_325, 
                                                               _envi_319)) >>
                                                             fun _ext_324 ->
                                                                ((effect Effect_SetEnv)
                                                                _ext_324) >>
                                                                fun _ext_2_326 ->
                                                                   (_interp_273
                                                                   _t_318) >>
                                                                   fun _t_res_327 ->
                                                                     (effect Effect_InEnv)
                                                                   (_ext_2_326, 
                                                                    _t_res_327))))
                         >>
                         fun _interpFunc_309 ->
                            let _e1_interp_328 = _interpFunc_309 in
                         ((effect Effect_ReadEnv) ()) >>
                         fun _envi_329 ->
                            (_interp_273 _e2_308) >>
                            fun _e2_interp_330 ->
                               ((effect Effect_SetEnv) _envi_329) >>
                               fun _envi2_331 ->
                                  ((effect Effect_InEnv)
                                  (_envi2_331, _e2_interp_330)) >>
                                  fun _in_env_332 ->  _e1_interp_328
                                  _in_env_332)

;;


let rec _interpTopLevel_333 = fun _lst_334 ->  value (fun _results_335 ->
   (match _lst_334 with | [] ->
                           value _results_335
                        | ((_top_336) :: (_tail_337)) ->
                           (_interpTopLevel_333 _tail_337) >>
                           fun _gen_bind_338 ->
                              ((_var_224 (* @ *) _results_335) >>
                               fun _gen_bind_340 ->
                                  (_interp_273 _top_336) >>
                                  fun _gen_bind_341 ->  _gen_bind_340
                                  (((::) (_gen_bind_341, [])))) >>
                              fun _gen_bind_339 ->  _gen_bind_338
                              _gen_bind_339))

;;


let _storeHandler_342 = (fun c -> handler { value_clause = (fun _y_358 ->
                                                               value (fun _ ->
                                                               value _y_358));
                                           effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_LookupLoc -> (fun (_x_353 :  loc) (_k_354 :  int -> _ computation) -> value (fun _s_355 ->
                                              ((_lookupState_231
                                               (_x_353, _s_355)) >>
                                               fun _gen_bind_357 ->  _k_354
                                               _gen_bind_357) >>
                                              fun _gen_bind_356 ->
                                                 _gen_bind_356
                                              _s_355)) | Effect_UpdateLoc -> (fun ((
                                           _x_347, _y_348) : ( loc*
                                            int)) (_k_349 :  loc -> _ computation) -> value (fun _s_350 ->
                                              (_k_349 _x_347) >>
                                              fun _gen_bind_351 ->
                                                 (_updateState_240
                                                 (_x_347, _y_348, _s_350)) >>
                                                 fun _gen_bind_352 ->
                                                    _gen_bind_351
                                                 _gen_bind_352)) | Effect_AllocLoc -> (fun (() :  unit) (_k_343 :  loc -> _ computation) -> value (fun _s_344 ->
                                              ((_getNewLoc_258 _s_344) >>
                                               fun _gen_bind_346 ->  _k_343
                                               _gen_bind_346) >>
                                              fun _gen_bind_345 ->
                                                 _gen_bind_345
                                              _s_344)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c)

;;


let _environmentHandler_359 = (fun c -> handler { value_clause = (fun _y_370 ->
                                                                     value (fun _ ->
                                                                     value _y_370));
                                                 effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                 _env_366, _s_367) : ( env*
                                                  int)) (_k_368 :  int -> _ computation) -> value (fun _ ->
                                                    (_k_368 _s_367) >>
                                                    fun _gen_bind_369 ->
                                                       _gen_bind_369
                                                    _env_366)) | Effect_ReadEnv -> (fun (() :  unit) (_k_363 :  env -> _ computation) -> value (fun _env_364 ->
                                                    (_k_363 _env_364) >>
                                                    fun _gen_bind_365 ->
                                                       _gen_bind_365
                                                    _env_364)) | Effect_SetEnv -> (fun (_env_360 :  env) (_k_361 :  env -> _ computation) -> value (fun _ ->
                                                    (_k_361 _env_360) >>
                                                    fun _gen_bind_362 ->
                                                       _gen_bind_362
                                                    _env_360)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c)

;;


let _environment_store_Handler_371 = (fun c -> handler { value_clause = (
                                                        fun _y_403 ->
                                                           value (fun _ ->
                                                           value _y_403));
                                                        effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                        _env_398, _e_399) : ( env*
                                                         int)) (_k_400 :  int -> _ computation) -> value (fun (
                                                        _, _s_401) ->
                                                           (_k_400 _e_399) >>
                                                           fun _gen_bind_402 ->
                                                              _gen_bind_402
                                                           (_env_398, _s_401))) | Effect_ReadEnv -> (fun (() :  unit) (_k_394 :  env -> _ computation) -> value (fun (
                                                        _env_395, _s_396) ->
                                                           (_k_394 _env_395)
                                                           >>
                                                           fun _gen_bind_397 ->
                                                              _gen_bind_397
                                                           (_env_395, _s_396))) | Effect_SetEnv -> (fun (_env_390 :  env) (_k_391 :  env -> _ computation) -> value (fun (
                                                        _, _s_392) ->
                                                           (_k_391 _env_390)
                                                           >>
                                                           fun _gen_bind_393 ->
                                                              _gen_bind_393
                                                           (_env_390, _s_392))) | Effect_LookupLoc -> (fun (_x_384 :  loc) (_k_385 :  int -> _ computation) -> value (fun (
                                                        _env_386, _s_387) ->
                                                           ((_lookupState_231
                                                            (_x_384, _s_387))
                                                            >>
                                                            fun _gen_bind_389 ->
                                                               _k_385
                                                            _gen_bind_389) >>
                                                           fun _gen_bind_388 ->
                                                              _gen_bind_388
                                                           (_env_386, _s_387))) | Effect_UpdateLoc -> (fun ((
                                                        _x_377, _y_378) : ( loc*
                                                         int)) (_k_379 :  loc -> _ computation) -> value (fun (
                                                        _env_380, _s_381) ->
                                                           (_k_379 _x_377) >>
                                                           fun _gen_bind_382 ->
                                                              (_updateState_240
                                                              (_x_377, 
                                                               _y_378, _s_381))
                                                              >>
                                                              fun _gen_bind_383 ->
                                                                 _gen_bind_382
                                                              (_env_380, 
                                                               _gen_bind_383))) | Effect_AllocLoc -> (fun (() :  unit) (_k_372 :  loc -> _ computation) -> value (fun (
                                                        _env_373, _s_374) ->
                                                           ((_getNewLoc_258
                                                            _s_374) >>
                                                            fun _gen_bind_376 ->
                                                               _k_372
                                                            _gen_bind_376) >>
                                                           fun _gen_bind_375 ->
                                                              _gen_bind_375
                                                           (_env_373, _s_374))) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c)

;;


let _lambdaCase_404 = ((LambdaV ("a", (Add ((Var "a"), (Num 22))))))

;;


let _addCase_405 = ((Add ((Add ((Add ((Num 20), (Num 2))), 
                                (Mul ((Num 1), (Num 2))))), 
                          (Sub ((Add ((Num 2), (Num 2))), 
                                (Add ((Num 1), (Num 2))))))))

;;


let _testCaseA_406 = ((App (_lambdaCase_404, 
                            (App (_lambdaCase_404, 
                                  (App (_lambdaCase_404, 
                                        (App (_lambdaCase_404, 
                                              (App (_lambdaCase_404, 
                                                    (App (_lambdaCase_404, 
                                                          (App (_lambdaCase_404, 
                                                                _addCase_405)))))))))))))))

;;


let _testCaseB_407 = ((App (_lambdaCase_404, 
                            (App (_lambdaCase_404, 
                                  (App (_lambdaCase_404, 
                                        (App (_lambdaCase_404, 
                                              (App (_lambdaCase_404, 
                                                    (App (_lambdaCase_404, 
                                                          (App (_lambdaCase_404, 
                                                                _testCaseA_406)))))))))))))))

;;


let _testCaseC_408 = ((App (_lambdaCase_404, 
                            (App (_lambdaCase_404, 
                                  (App (_lambdaCase_404, 
                                        (App (_lambdaCase_404, 
                                              (App (_lambdaCase_404, 
                                                    (App (_lambdaCase_404, 
                                                          (App (_lambdaCase_404, 
                                                                _testCaseB_407)))))))))))))))

;;


let _testCaseD_409 = ((App (_lambdaCase_404, 
                            (App (_lambdaCase_404, 
                                  (App (_lambdaCase_404, 
                                        (App (_lambdaCase_404, 
                                              (App (_lambdaCase_404, 
                                                    (App (_lambdaCase_404, 
                                                          (App (_lambdaCase_404, 
                                                                _testCaseC_408)))))))))))))))

;;


let rec _createCase_410 = fun _n_411 ->
   (match _n_411 with | 1 ->
                         value _testCaseD_409
                      | _ ->
                         (((_var_221 (* - *) _n_411) >>
                           fun _gen_bind_414 ->  _gen_bind_414 1) >>
                          fun _gen_bind_413 ->  _createCase_410 _gen_bind_413)
                         >>
                         fun _gen_bind_412 ->
                            value ((App (_lambdaCase_404, _gen_bind_412))))

;;


let _finalCase_415 = run (_createCase_410 200)

;;


let _bigTest_416 = (fun () ->
   (_environment_store_Handler_371 (_interp_273 _finalCase_415)) >>
   fun _gen_bind_417 ->  _gen_bind_417 ([], []))
