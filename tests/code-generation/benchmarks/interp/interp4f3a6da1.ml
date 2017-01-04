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

let (=) = fun x -> value (fun y -> value (Pervasives.(=) x y))
let (<) = fun x -> value (fun y -> value (Pervasives.(<) x y))
let (<>) = fun x -> value (fun y -> value (Pervasives.(<>) x y))
let (>) = fun x -> value (fun y -> value (Pervasives.(>) x y))

let (>=) = fun x -> value (fun y -> value (Pervasives.(>=) x y))
let (<=) = fun x -> value (fun y -> value (Pervasives.(<=) x y))
let (!=) = fun x -> value (fun y -> value (Pervasives.(!=) x y))

let (~-) = fun x -> value (Pervasives.(~-) x)
let (+) = fun x -> value (fun y -> value (Pervasives.(+) x y))
let ( * ) = fun x -> value (fun y -> value (Pervasives.( * ) x y))
let (-) = fun x -> value (fun y -> value (Pervasives.(-) x y))
let (mod) = fun x -> value (fun y -> value (Pervasives.(mod) x y))
let (~-.) = fun x -> value (Pervasives.(~-.) x)
let (+.) = fun x -> value (fun y -> value (Pervasives.(+.) x y))
let ( *. ) = fun x -> value (fun y -> value (Pervasives.( *. ) x y))
let (-.) = fun x -> value (fun y -> value (Pervasives.(-.) x y))
let (/.) = fun x -> value (fun y -> value (Pervasives.(/.) x y))
let (/) = fun x -> value (fun y -> value (Pervasives.(/) x y))
let ( ** ) =
  let rec pow a = Pervasives.(function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)) in
  fun x -> value (fun y -> value (pow x y))

let float_of_int = fun x -> value (Pervasives.float_of_int x)
let (^) = fun x -> value (fun y -> value (Pervasives.(^) x y))
let string_length = fun x -> value (String.length x)
let to_string = fun _ -> failwith "Not implemented"

;;
let _var_1 (* = *) : ('t25 -> (('t25 -> ( bool) computation)) computation) = ( = )

;;


let _var_2 (* < *) : ('t26 -> (('t26 -> ( bool) computation)) computation) = ( < )

;;


let _var_3 (* > *) : ('t27 -> (('t27 -> ( bool) computation)) computation) = ( > )

;;


let _var_4 (* <> *) : ('t28 -> (('t28 -> ( bool) computation)) computation) = ( <> )

;;


let _var_5 (* <= *) : ('t29 -> (('t29 -> ( bool) computation)) computation) = ( <= )

;;


let _var_6 (* >= *) : ('t30 -> (('t30 -> ( bool) computation)) computation) = ( >= )

;;


let _var_7 (* != *) : ('t31 -> (('t31 -> ( bool) computation)) computation) = ( != )

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
   call Effect_Failure _msg_11 (fun _result_27 ->  _absurd_8 _result_27))

;;


type (_, _) effect += Effect_AssertionFault : ( unit, unit) effect

;;


let _assert_13 = (fun _b_14 ->
   (match _b_14 with | true ->
                        value ()
                     | false ->
                        call Effect_AssertionFault () (fun _result_30 ->
                                                          _absurd_8
                                                       _result_30)))

;;


let _var_16 (* ~- *) : ( int -> ( int) computation) = ( ~- )

;;


let _var_17 (* + *) : ( int -> (( int -> ( int) computation)) computation) = ( + )

;;


let _var_18 (* * *) : ( int -> (( int -> ( int) computation)) computation) = ( * )

;;


let _var_19 (* - *) : ( int -> (( int -> ( int) computation)) computation) = ( - )

;;


let _mod_20 : ( int -> (( int -> ( int) computation)) computation) = ( mod )

;;


let _mod_21 = (fun _m_22 ->  value (fun _n_23 ->
   (match _n_23 with | 0 ->
                        call Effect_DivisionByZero () (fun _result_33 ->
                                                          _absurd_8
                                                       _result_33)
                     | _n_25 ->
                        value (Pervasives.(mod)
                     _m_22
                     _n_25))))

;;


let _var_27 (* ~-. *) : ( float -> ( float) computation) = ( ~-. )

;;


let _var_28 (* +. *) : ( float -> (( float -> ( float) computation)) computation) = ( +. )

;;


let _var_29 (* *. *) : ( float -> (( float -> ( float) computation)) computation) = ( *. )

;;


let _var_30 (* -. *) : ( float -> (( float -> ( float) computation)) computation) = ( -. )

;;


let _var_31 (* /. *) : ( float -> (( float -> ( float) computation)) computation) = ( /. )

;;


let _var_32 (* / *) : ( int -> (( int -> ( int) computation)) computation) = ( / )

;;


let _var_33 (* ** *) : ( int -> (( int -> ( int) computation)) computation) = ( ** )

;;


let _var_34 (* / *) = (fun _m_35 ->  value (fun _n_36 ->
   (match _n_36 with | 0 ->
                        call Effect_DivisionByZero () (fun _result_36 ->
                                                          _absurd_8
                                                       _result_36)
                     | _n_38 ->
                        value (Pervasives.(/)
                     _m_35
                     _n_38))))

;;


let _float_of_int_40 : ( int -> ( float) computation) = ( float_of_int )

;;


let _var_41 (* ^ *) : ( string -> (( string -> ( string) computation)) computation) = ( ^ )

;;


let _string_length_42 : ( string -> ( int) computation) = ( string_length )

;;


let _to_string_43 : ('t32 -> ( string) computation) = ( to_string )

;;


type ('t33) option = None|Some of 't33

;;

let rec _assoc_44 = fun _x_45 ->
   value (fun _gen_function_46 ->
   (match _gen_function_46 with | [] ->
                                   value None
                                | (((_y_47, _z_48)) :: (_lst_49)) ->
                                   (match Pervasives.(=)
                                _x_45
                                _y_47 with | true ->
                                              value ((Some _z_48))
                                           | false ->
                                              (_assoc_44 _x_45) >>
                                              fun _gen_bind_52 ->
                                                 _gen_bind_52
                                              _lst_49)))

;;


let _not_53 = (fun _x_54 ->
   (match _x_54 with | true ->
                        value false
                     | false ->
                        value true))

;;

let rec _range_55 = fun _m_56 ->
   value (fun _n_57 ->  (match Pervasives.(>) _m_56
_n_57 with | true ->
              value []
           | false ->
              (_range_55 (Pervasives.(+) _m_56 1)) >>
              fun _gen_bind_62 ->
                 (_gen_bind_62 _n_57) >>
                 fun _gen_bind_61 ->  value (((::) (_m_56, _gen_bind_61)))))

;;


let rec _map_65 = fun _f_66 ->  value (fun _gen_function_67 ->
   (match _gen_function_67 with | [] ->
                                   value []
                                | ((_x_68) :: (_xs_69)) ->
                                   (_f_66 _x_68) >>
                                   fun _y_70 ->
                                      (_map_65 _f_66) >>
                                      fun _gen_bind_72 ->
                                         (_gen_bind_72 _xs_69) >>
                                         fun _ys_71 ->
                                            value (((::) (_y_70, _ys_71)))))

;;


let _ignore_73 = (fun _ ->  value ())

;;

let _take_74 = (fun _f_75 ->
   value (fun _k_76 ->
   (_range_55 0) >>
   fun _gen_bind_78 ->
      (_gen_bind_78 _k_76) >>
      fun _r_77 ->
         (_map_65 _f_75) >> fun _gen_bind_79 ->  _gen_bind_79 _r_77))

;;


let rec _fold_left_80 = fun _f_81 ->  value (fun _a_82 ->
   value (fun _gen_function_83 ->
   (match _gen_function_83 with | [] ->
                                   value _a_82
                                | ((_y_84) :: (_ys_85)) ->
                                   (_f_81 _a_82) >>
                                   fun _gen_bind_87 ->
                                      (_gen_bind_87 _y_84) >>
                                      fun _a_86 ->
                                         (_fold_left_80 _f_81) >>
                                         fun _gen_bind_89 ->
                                            (_gen_bind_89 _a_86) >>
                                            fun _gen_bind_88 ->  _gen_bind_88
                                            _ys_85)))

;;


let rec _fold_right_90 = fun _f_91 ->  value (fun _xs_92 ->
   value (fun _a_93 ->
   (match _xs_92 with | [] ->
                         value _a_93
                      | ((_x_94) :: (_xs_95)) ->
                         (_fold_right_90 _f_91) >>
                         fun _gen_bind_98 ->
                            (_gen_bind_98 _xs_95) >>
                            fun _gen_bind_97 ->
                               (_gen_bind_97 _a_93) >>
                               fun _a_96 ->
                                  (_f_91 _x_94) >>
                                  fun _gen_bind_99 ->  _gen_bind_99 _a_96)))

;;


let rec _iter_100 = fun _f_101 ->  value (fun _gen_function_102 ->
   (match _gen_function_102 with | [] ->
                                    value ()
                                 | ((_x_103) :: (_xs_104)) ->
                                    (_f_101 _x_103) >>
                                    fun _ ->
                                       (_iter_100 _f_101) >>
                                       fun _gen_bind_105 ->  _gen_bind_105
                                       _xs_104))

;;


let rec _forall_106 = fun _p_107 ->  value (fun _gen_function_108 ->
   (match _gen_function_108 with | [] ->
                                    value true
                                 | ((_x_109) :: (_xs_110)) ->
                                    (_p_107 _x_109) >>
                                    fun _gen_bind_111 ->
                                       (match _gen_bind_111 with | true ->
                                                                    (_forall_106
                                                                    _p_107)
                                                                    >>
                                                                    fun _gen_bind_112 ->
                                                                     _gen_bind_112
                                                                    _xs_110
                                                                 | false ->
                                                                    value false)))

;;


let rec _exists_113 = fun _p_114 ->  value (fun _gen_function_115 ->
   (match _gen_function_115 with | [] ->
                                    value false
                                 | ((_x_116) :: (_xs_117)) ->
                                    (_p_114 _x_116) >>
                                    fun _gen_bind_118 ->
                                       (match _gen_bind_118 with | true ->
                                                                    value true
                                                                 | false ->
                                                                    (_exists_113
                                                                    _p_114)
                                                                    >>
                                                                    fun _gen_bind_119 ->
                                                                     _gen_bind_119
                                                                    _xs_117)))

;;


let _mem_120 = (fun _x_121 ->  _exists_113 (fun _x'_122 ->
   value (Pervasives.(=) _x_121 _x'_122)))

;;


let rec _filter_124 = fun _p_125 ->  value (fun _gen_function_126 ->
   (match _gen_function_126 with | [] ->
                                    value []
                                 | ((_x_127) :: (_xs_128)) ->
                                    (_p_125 _x_127) >>
                                    fun _gen_bind_129 ->
                                       (match _gen_bind_129 with | true ->
                                                                    (_filter_124
                                                                    _p_125)
                                                                    >>
                                                                    fun _gen_bind_131 ->

                                                                    (_gen_bind_131
                                                                    _xs_128)
                                                                    >>
                                                                    fun _gen_bind_130 ->
                                                                     value (((::) (
                                                                    _x_127,
                                                                    _gen_bind_130)))
                                                                 | false ->
                                                                    (_filter_124
                                                                    _p_125)
                                                                    >>
                                                                    fun _gen_bind_132 ->
                                                                     _gen_bind_132
                                                                    _xs_128)))

;;


let _complement_133 = (fun _xs_134 ->  value (fun _ys_135 ->
   (_filter_124 (fun _x_137 ->
      (_mem_120 _x_137) >>
      fun _gen_bind_139 ->
         (_gen_bind_139 _ys_135) >>
         fun _gen_bind_138 ->  _not_53 _gen_bind_138)) >>
   fun _gen_bind_136 ->  _gen_bind_136 _xs_134))

;;


let _intersection_140 = (fun _xs_141 ->  value (fun _ys_142 ->
   (_filter_124 (fun _x_144 ->
      (_mem_120 _x_144) >> fun _gen_bind_145 ->  _gen_bind_145 _ys_142)) >>
   fun _gen_bind_143 ->  _gen_bind_143 _xs_141))

;;


let rec _zip_146 = fun _xs_147 ->  value (fun _ys_148 ->
   (match (_xs_147, _ys_148) with | ([], []) ->
                                     value []
                                  | (((_x_149) :: (_xs_150)),
                                     ((_y_151) :: (_ys_152))) ->
                                     (_zip_146 _xs_150) >>
                                     fun _gen_bind_154 ->
                                        (_gen_bind_154 _ys_152) >>
                                        fun _gen_bind_153 ->
                                           value (((::) ((_x_149, _y_151),
                                                         _gen_bind_153)))
                                  | (_, _) ->
                                     call Effect_InvalidArgument "zip: length mismatch" (
                                  fun _result_45 ->  _absurd_8 _result_45)))

;;


let _reverse_156 = (fun _lst_157 ->
   let rec _reverse_acc_158 = fun _acc_159 ->
              value (fun _gen_function_160 ->
              (match _gen_function_160 with | [] ->
                                               value _acc_159
                                            | ((_x_161) :: (_xs_162)) ->
                                               (_reverse_acc_158
                                               (((::) (_x_161, _acc_159))))
                                               >>
                                               fun _gen_bind_163 ->
                                                  _gen_bind_163
                                               _xs_162)) in (_reverse_acc_158
                                                            []) >>
                                                            fun _gen_bind_164 ->
                                                               _gen_bind_164
                                                            _lst_157)

;;


let rec _var_165 (* @ *) = fun _xs_166 ->  value (fun _ys_167 ->
   (match _xs_166 with | [] ->
                          value _ys_167
                       | ((_x_168) :: (_xs_169)) ->
                          (_var_165 (* @ *) _xs_169) >>
                          fun _gen_bind_171 ->
                             (_gen_bind_171 _ys_167) >>
                             fun _gen_bind_170 ->
                                value (((::) (_x_168, _gen_bind_170)))))

;;


let rec _length_172 = fun _gen_let_rec_function_173 ->
   (match _gen_let_rec_function_173 with | [] ->
                                            value 0
                                         | ((_x_174) :: (_xs_175)) ->
                                            (_length_172 _xs_175) >>
                                            fun _gen_bind_177 ->
                                               value (Pervasives.(+)
                                            _gen_bind_177 1))

;;


let _head_178 = (fun _gen_function_179 ->
   (match _gen_function_179 with | [] ->
                                    call Effect_InvalidArgument "head: empty list" (
                                 fun _result_48 ->  _absurd_8 _result_48)
                                 | ((_x_181) :: (_)) ->
                                    value _x_181))

;;


let _tail_182 = (fun _gen_function_183 ->
   (match _gen_function_183 with | [] ->
                                    call Effect_InvalidArgument "tail: empty list" (
                                 fun _result_51 ->  _absurd_8 _result_51)
                                 | ((_x_185) :: (_xs_186)) ->
                                    value _xs_186))

;;


let _hd_187 = _head_178

;;

let _tl_188 = _tail_182

;;


let _abs_189 = (fun _x_190 ->  (match Pervasives.(<) _x_190
0 with | true ->
          value (Pervasives.(~-)
       _x_190)
       | false ->
          value _x_190))

;;

let _min_193 = (fun _x_194 ->
   value (fun _y_195 ->  (match Pervasives.(<) _x_194
_y_195 with | true ->
               value _x_194
            | false ->
               value _y_195)))

;;

let _max_198 = (fun _x_199 ->
   value (fun _y_200 ->  (match Pervasives.(<) _x_199
_y_200 with | true ->
               value _y_200
            | false ->
               value _x_199)))

;;

let rec _gcd_203 = fun _m_204 ->
   value (fun _n_205 ->
   (match _n_205 with | 0 ->
                         value _m_204
                      | _ ->
                         (_gcd_203 _n_205) >>
                         fun _g_206 ->
                            (_mod_21 _m_204) >>
                            fun _gen_bind_208 ->
                               (_gen_bind_208 _n_205) >>
                               fun _gen_bind_207 ->  _g_206 _gen_bind_207))

;;


let rec _lcm_209 = fun _m_210 ->  value (fun _n_211 ->
   (_gcd_203 _m_210) >>
   fun _gen_bind_213 ->
      (_gen_bind_213 _n_211) >>
      fun _d_212 ->
         (_var_34 (* / *) (Pervasives.( * ) _m_210 _n_211)) >>
         fun _gen_bind_214 ->  _gen_bind_214 _d_212)

;;


let _odd_217 = (fun _x_218 ->
   (_mod_21 _x_218) >>
   fun _gen_bind_221 ->
      (_gen_bind_221 2) >>
      fun _gen_bind_220 ->  value (Pervasives.(=) _gen_bind_220 1))

;;


let _even_222 = (fun _x_223 ->
   (_mod_21 _x_223) >>
   fun _gen_bind_226 ->
      (_gen_bind_226 2) >>
      fun _gen_bind_225 ->  value (Pervasives.(=) _gen_bind_225 0))

;;


let _id_227 = (fun _x_228 ->  value _x_228)

;;


let _compose_229 = (fun _f_230 ->  value (fun _g_231 ->  value (fun _x_232 ->
   (_g_231 _x_232) >> fun _gen_bind_233 ->  _f_230 _gen_bind_233)))

;;


let _fst_234 = (fun (_x_235, _) ->  value _x_235)

;;


let _snd_236 = (fun (_, _y_237) ->  value _y_237)

;;


let _print_238 = (fun _v_239 ->
   (_to_string_43 _v_239) >>
   fun _s_240 ->
      call Effect_Print _s_240 (fun _result_63 ->  value _result_63))

;;


let _print_string_241 = (fun _str_242 ->
   call Effect_Print _str_242 (fun _result_65 ->  value _result_65))

;;


let _print_endline_243 = (fun _v_244 ->
   (_to_string_43 _v_244) >>
   fun _s_245 ->
      call Effect_Print _s_245 (fun _result_70 ->
                                   call Effect_Print "\n" (fun _result_67 ->
                                                              value _result_67)))

;;


type (_, _) effect += Effect_Lookup : ( unit,  int) effect

;;


type (_, _) effect += Effect_Update : ( int,  unit) effect

;;


let _state_246 = (fun _r_247 ->  value (fun _x_248 ->
   value { value_clause = (fun _y_256 ->  value (fun _ ->  value _y_256));
          finally_clause = (fun _f_255 ->  _f_255 _x_248);
          effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Lookup -> (fun (() :  unit) (_k_252 :  int -> _ computation) -> value (fun _s_253 ->
             (_k_252 _s_253) >> fun _gen_bind_254 ->  _gen_bind_254 _s_253)) | Effect_Update -> (fun (_s'_249 :  int) (_k_250 :  unit -> _ computation) -> value (fun _ ->
             (_k_250 ()) >> fun _gen_bind_251 ->  _gen_bind_251 _s'_249)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }))

;;


value "End of pervasives"

;;

type  num =  int

;;


type  func = ( int -> ( int) computation)

;;

type  loc =  int

;;


type  name =  string

;;

type  env = (( string* int)) list

;;


type  term = Num of ( int)|Add of (( term* term))|Mul of (( term* term))|
             Sub of (( term* term))|Div of (( term* term))|Ref of ( term)|
             Deref of ( term)|Assign of (( term* term))|Var of ( string)|
             App of (( termF* term))
and

 termF = LambdaN of (( string* term))|LambdaV of (( string* term))|
         LambdaL of (( string* term))

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


let rec _lookupState_257 = fun (_x_258, _y_259) ->
   (match _y_259 with | [] ->
                         call Effect_VarNotFound () (fun _result_73 ->
                                                        _absurd_8
                                                     _result_73)
                      | (((_x'_261, _y_262)) :: (_lst_263)) ->
                         (match Pervasives.(=)
                      _x_258
                      _x'_261 with | true ->
                                      value _y_262
                                   | false ->
                                      _lookupState_257
                                   (_x_258, _lst_263)))

;;


let _updateState_266 = (fun (_k_267, _v_268, _env_269) ->
   value (((::) ((_k_267, _v_268), _env_269))))

;;


let rec _checkLoc_270 = fun (_x_271, _env_272) ->
   (match _env_272 with | [] ->
                           value false
                        | (((_x'_273, _y_274)) :: (_lst_275)) ->
                           (match Pervasives.(=)
                        _x_271
                        _x'_273 with | true ->
                                        value true
                                     | false ->
                                        _checkLoc_270
                                     (_x_271, _lst_275)))

;;


let rec _createLoc_278 = fun (_i_279, _env_280) ->
   (_checkLoc_270 (_i_279, _env_280)) >>
   fun _gen_bind_281 ->
      (match _gen_bind_281 with | true ->
                                   _createLoc_278
                                (Pervasives.(+) _i_279 1, _env_280)
                                | false ->
                                   value _i_279)

;;


let _getNewLoc_284 = (fun _env_285 ->  _createLoc_278 (0, _env_285))

;;


let rec _lookupEnv_286 = fun (_x_287, _y_288) ->
   (match _y_288 with | [] ->
                         call Effect_VarNotFound () (fun _result_80 ->
                                                        _absurd_8
                                                     _result_80)
                      | (((_x'_290, _y_291)) :: (_lst_292)) ->
                         (match Pervasives.(=)
                      _x_287
                      _x'_290 with | true ->
                                      value _y_291
                                   | false ->
                                      _lookupState_257
                                   (_x_287, _lst_292)))

;;


let _extendEnv_295 = (fun (_k_296, _v_297, _env_298) ->
   value (((::) ((_k_296, _v_297), _env_298))))

;;


let rec _interpFunc_299 = fun (_a_300, _interpT_301) ->
   (match _a_300 with | (LambdaN (_s_302, _t_303)) ->
                         call Effect_ReadEnv () (fun _result_90 ->
                                                    value (fun _v_305 ->
                                                    (_extendEnv_295
                                                    (_s_302, _v_305,
                                                     _result_90)) >>
                                                    fun _ext_306 ->
                                                       call Effect_SetEnv _ext_306 (
                                                    fun _result_87 ->
                                                       (_interpT_301 _t_303)
                                                       >>
                                                       fun _gen_bind_308 ->
                                                          call Effect_InEnv (
                                                       _result_87,
                                                       _gen_bind_308) (
                                                       fun _result_84 ->
                                                          value _result_84))))
                      | (LambdaV (_s_309, _t_310)) ->
                         call Effect_ReadEnv () (fun _result_98 ->
                                                    value (fun _v_312 ->
                                                    (_extendEnv_295
                                                    (_s_309, _v_312,
                                                     _result_98)) >>
                                                    fun _ext_313 ->
                                                       call Effect_SetEnv _ext_313 (
                                                    fun _result_95 ->
                                                       (_interpT_301 _t_310)
                                                       >>
                                                       fun _gen_bind_315 ->
                                                          call Effect_InEnv (
                                                       _result_95,
                                                       _gen_bind_315) (
                                                       fun _result_92 ->
                                                          value _result_92))))
                      | (LambdaL (_s_316, _t_317)) ->
                         call Effect_ReadEnv () (fun _result_120 ->
                                                    value (fun _v_319 ->
                                                    call Effect_AllocLoc () (
                                                 fun _result_117 ->
                                                    call Effect_UpdateLoc (
                                                 _result_117, _v_319) (
                                                 fun _result_114 ->
                                                    call Effect_UpdateLoc (
                                                 _result_117, _v_319) (
                                                 fun _result_110 ->
                                                    call Effect_LookupLoc _result_117 (
                                                 fun _result_107 ->
                                                    (_extendEnv_295
                                                    (_s_316, _result_107,
                                                     _result_120)) >>
                                                    fun _ext_323 ->
                                                       call Effect_SetEnv _ext_323 (
                                                    fun _result_103 ->
                                                       (_interpT_301 _t_317)
                                                       >>
                                                       fun _gen_bind_326 ->
                                                          call Effect_InEnv (
                                                       _result_103,
                                                       _gen_bind_326) (
                                                       fun _result_100 ->
                                                          value _result_100)))))))))

;;


let rec _interp_327 = fun _a_328 ->
   (match _a_328 with | (Num _b_329) ->
                         value _b_329
                      | (Add (_l_330, _r_331)) ->
                         (_interp_327 _l_330) >>
                         fun _gen_bind_333 ->
                            let _gen_bind_332 = fun _x2_23 ->
                                   value (Pervasives.(+) _gen_bind_333
                                _x2_23) in
                         (_interp_327 _r_331) >>
                         fun _gen_bind_334 ->  _gen_bind_332 _gen_bind_334
                      | (Mul (_l_335, _r_336)) ->
                         (_interp_327 _l_335) >>
                         fun _gen_bind_338 ->
                            let _gen_bind_337 = fun _x2_21 ->
                                   value (Pervasives.( * ) _gen_bind_338
                                _x2_21) in
                         (_interp_327 _r_336) >>
                         fun _gen_bind_339 ->  _gen_bind_337 _gen_bind_339
                      | (Sub (_l_340, _r_341)) ->
                         (_interp_327 _l_340) >>
                         fun _gen_bind_343 ->
                            let _gen_bind_342 = fun _x2_19 ->
                                   value (Pervasives.(-) _gen_bind_343
                                _x2_19) in
                         (_interp_327 _r_341) >>
                         fun _gen_bind_344 ->  _gen_bind_342 _gen_bind_344
                      | (Div (_l_345, _r_346)) ->
                         (_interp_327 _r_346) >>
                         fun _r_num_347 ->
                            (match _r_num_347 with | 0 ->
                                                      call Effect_Arith_DivByZero () (
                                                   fun _result_122 ->
                                                      value _result_122)
                                                   | _ ->
                                                      (_interp_327 _l_345) >>
                                                      fun _gen_bind_349 ->
                                                         (_var_34 (* / *)
                                                         _gen_bind_349) >>
                                                         fun _gen_bind_348 ->
                                                            _gen_bind_348
                                                         _r_num_347)
                      | (Ref _x_350) ->
                         (_interp_327 _x_350) >>
                         fun _x_interp_351 ->
                            call Effect_AllocLoc () (fun _result_127 ->
                                                        call Effect_UpdateLoc (
                                                     _result_127,
                                                     _x_interp_351) (
                                                     fun _result_124 ->
                                                        value _result_124))
                      | (Deref _x_353) ->
                         (_interp_327 _x_353) >>
                         fun _x_interp_354 ->
                            call Effect_LookupLoc _x_interp_354 (fun _result_129 ->
                                                                    value _result_129)
                      | (Assign (_lhs_355, _rhs_356)) ->
                         (_interp_327 _lhs_355) >>
                         fun _x_loc_357 ->
                            (_interp_327 _rhs_356) >>
                            fun _x_interp_358 ->
                               call Effect_UpdateLoc (_x_loc_357,
                                                      _x_interp_358) (
                            fun _result_132 ->  value _x_interp_358)
                      | (Var _v_359) ->
                         call Effect_ReadEnv () (fun _result_135 ->
                                                    _lookupEnv_286
                                                 (_v_359, _result_135))
                      | (App (_e1_361, _e2_362)) ->
                         (_interpFunc_299 (_e1_361, _interp_327)) >>
                         fun _e1_interp_363 ->
                            call Effect_ReadEnv () (fun _result_144 ->
                                                       (_interp_327 _e2_362)
                                                       >>
                                                       fun _e2_interp_365 ->
                                                          call Effect_SetEnv _result_144 (
                                                       fun _result_141 ->
                                                          call Effect_InEnv (
                                                       _result_141,
                                                       _e2_interp_365) (
                                                       fun _result_138 ->
                                                          _e1_interp_363
                                                       _result_138))))

;;


let rec _interpTopLevel_368 = fun _lst_369 ->  value (fun _results_370 ->
   (match _lst_369 with | [] ->
                           value _results_370
                        | ((_top_371) :: (_tail_372)) ->
                           (_interpTopLevel_368 _tail_372) >>
                           fun _gen_bind_373 ->
                              ((_var_165 (* @ *) _results_370) >>
                               fun _gen_bind_375 ->
                                  (_interp_327 _top_371) >>
                                  fun _gen_bind_376 ->  _gen_bind_375
                                  (((::) (_gen_bind_376, [])))) >>
                              fun _gen_bind_374 ->  _gen_bind_373
                              _gen_bind_374))

;;


let _arithmeticHandler_377 = { value_clause = (fun _gen_id_par_380 ->
                                                  value _gen_id_par_380);
                              finally_clause = (fun _gen_id_par_379 ->
                                                   value _gen_id_par_379);
                              effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_378 :  int -> _ computation) -> value (Pervasives.(~-)
                              1)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _storeHandler_381 = { value_clause = (fun _y_398 ->  value (fun _ ->
                                             value _y_398));
                         finally_clause = (fun _gen_id_par_397 ->
                                              value _gen_id_par_397);
                         effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_LookupLoc -> (fun (_x_392 :  loc) (_k_393 :  int -> _ computation) -> value (fun _s_394 ->
                            (_lookupState_257 (_x_392, _s_394)) >>
                            fun _gen_bind_396 ->
                               (_k_393 _gen_bind_396) >>
                               fun _gen_bind_395 ->  _gen_bind_395 _s_394)) | Effect_UpdateLoc -> (fun ((
                         _x_386, _y_387) : ( loc*
                          int)) (_k_388 :  loc -> _ computation) -> value (fun _s_389 ->
                            (_k_388 _x_386) >>
                            fun _gen_bind_390 ->
                               (_updateState_266 (_x_386, _y_387, _s_389)) >>
                               fun _gen_bind_391 ->  _gen_bind_390
                               _gen_bind_391)) | Effect_AllocLoc -> (fun (() :  unit) (_k_382 :  loc -> _ computation) -> value (fun _s_383 ->
                            (_getNewLoc_284 _s_383) >>
                            fun _gen_bind_385 ->
                               (_k_382 _gen_bind_385) >>
                               fun _gen_bind_384 ->  _gen_bind_384 _s_383)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _environmentHandler_399 = { value_clause = (fun _y_411 ->
                                                   value (fun _ ->
                                                   value _y_411));
                               finally_clause = (fun _gen_id_par_410 ->
                                                    value _gen_id_par_410);
                               effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                               _env_406, _s_407) : ( env*
                                int)) (_k_408 :  int -> _ computation) -> value (fun _ ->
                                  (_k_408 _s_407) >>
                                  fun _gen_bind_409 ->  _gen_bind_409
                                  _env_406)) | Effect_ReadEnv -> (fun (() :  unit) (_k_403 :  env -> _ computation) -> value (fun _env_404 ->
                                  (_k_403 _env_404) >>
                                  fun _gen_bind_405 ->  _gen_bind_405
                                  _env_404)) | Effect_SetEnv -> (fun (_env_400 :  env) (_k_401 :  env -> _ computation) -> value (fun _ ->
                                  (_k_401 _env_400) >>
                                  fun _gen_bind_402 ->  _gen_bind_402
                                  _env_400)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _lambdaCase_412 = ((LambdaV ("a",
                                 (Add ((Add ((Add ((Var "a"), (Num 2))),
                                             (Add ((Num 1), (Num 2))))),
                                       (Add ((Add ((Num 1), (Num 2))),
                                             (Add ((Num 1), (Num 2))))))))))

;;


let _addCase_413 = ((Add ((Add ((Add ((Num 1), (Num 2))),
                                (Add ((Num 1), (Num 2))))),
                          (Add ((Add ((Num 1), (Num 2))),
                                (Add ((Num 1), (Num 2))))))))

;;


let _testCaseA_414 = ((App (_lambdaCase_412,
                            (App (_lambdaCase_412,
                                  (App (_lambdaCase_412,
                                        (App (_lambdaCase_412,
                                              (App (_lambdaCase_412,
                                                    (App (_lambdaCase_412,
                                                          (App (_lambdaCase_412,
                                                                _addCase_413)))))))))))))))

;;


let _testCaseB_415 = ((App (_lambdaCase_412,
                            (App (_lambdaCase_412,
                                  (App (_lambdaCase_412,
                                        (App (_lambdaCase_412,
                                              (App (_lambdaCase_412,
                                                    (App (_lambdaCase_412,
                                                          (App (_lambdaCase_412,
                                                                _testCaseA_414)))))))))))))))

;;


let _testCaseC_416 = ((App (_lambdaCase_412,
                            (App (_lambdaCase_412,
                                  (App (_lambdaCase_412,
                                        (App (_lambdaCase_412,
                                              (App (_lambdaCase_412,
                                                    (App (_lambdaCase_412,
                                                          (App (_lambdaCase_412,
                                                                _testCaseB_415)))))))))))))))

;;


let _testCaseD_417 = ((App (_lambdaCase_412,
                            (App (_lambdaCase_412,
                                  (App (_lambdaCase_412,
                                        (App (_lambdaCase_412,
                                              (App (_lambdaCase_412,
                                                    (App (_lambdaCase_412,
                                                          (App (_lambdaCase_412,
                                                                _testCaseC_416)))))))))))))))

;;


let rec _createCase_418 = fun _n_419 ->
   (match _n_419 with | 1 ->
                         value _testCaseD_417
                      | _ ->
                         (_createCase_418 (Pervasives.(-) _n_419 1)) >>
                         fun _gen_bind_420 ->
                            value ((App (_lambdaCase_412, _gen_bind_420))))

;;


let _finalCase_423 = run (_createCase_418 3000)

;;


let _bigTest_424 = run ((let rec _newvar_157 = fun _a_328 ->
                                    (match _a_328 with | (Num _b_329) ->
                                                          value (fun _ ->
                                                          value _b_329)
                                                       | (Add (_l_330, _r_331)) ->
                                                          handle { value_clause = (
                                                                  fun _gen_bind_289 ->
                                                                     let
                                                                  _gen_bind_290 =
                                                                  fun _x2_304 ->
                                                                     value (Pervasives.(+)
                                                                  _gen_bind_289
                                                                  _x2_304) in
                                                                  handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_292 ->
                                                                     value ((* pure *) let _y_293 = Pervasives.(+)
                                                                  _gen_bind_289
                                                                  _gen_bind_292 in
                                                                  fun _ ->
                                                                     value _y_293));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_291 ->
                                                                     value _gen_id_par_291);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_296,
                                                                  _s_295) : ( env*
                                                                   int)) (_k_294 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_294
                                                                  _s_295) >>
                                                                  fun _gen_bind_297 ->
                                                                     _gen_bind_297
                                                                  _env_296)) | Effect_ReadEnv -> (fun (() :  unit) (_k_298 :  env -> _ computation) -> value (fun _env_299 ->

                                                                  (_k_298
                                                                  _env_299)
                                                                  >>
                                                                  fun _gen_bind_300 ->
                                                                     _gen_bind_300
                                                                  _env_299)) | Effect_SetEnv -> (fun (_env_302 :  env) (_k_301 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_301
                                                                  _env_302)
                                                                  >>
                                                                  fun _gen_bind_303 ->
                                                                     _gen_bind_303
                                                                  _env_302)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _r_331));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_288 ->
                                                                     value _gen_id_par_288);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_307,
                                                                  _s_306) : ( env*
                                                                   int)) (_k_305 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_305
                                                                  _s_306) >>
                                                                  fun _gen_bind_308 ->
                                                                     _gen_bind_308
                                                                  _env_307)) | Effect_ReadEnv -> (fun (() :  unit) (_k_309 :  env -> _ computation) -> value (fun _env_310 ->

                                                                  (_k_309
                                                                  _env_310)
                                                                  >>
                                                                  fun _gen_bind_311 ->
                                                                     _gen_bind_311
                                                                  _env_310)) | Effect_SetEnv -> (fun (_env_313 :  env) (_k_312 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_312
                                                                  _env_313)
                                                                  >>
                                                                  fun _gen_bind_314 ->
                                                                     _gen_bind_314
                                                                  _env_313)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _l_330)
                                                       | (Mul (_l_335, _r_336)) ->
                                                          handle { value_clause = (
                                                                  fun _gen_bind_410 ->
                                                                     let
                                                                  _gen_bind_411 =
                                                                  fun _x2_425 ->
                                                                     value (Pervasives.( * )
                                                                  _gen_bind_410
                                                                  _x2_425) in
                                                                  handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_413 ->
                                                                     value ((* pure *) let _y_414 = Pervasives.( * )
                                                                  _gen_bind_410
                                                                  _gen_bind_413 in
                                                                  fun _ ->
                                                                     value _y_414));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_412 ->
                                                                     value _gen_id_par_412);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_417,
                                                                  _s_416) : ( env*
                                                                   int)) (_k_415 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_415
                                                                  _s_416) >>
                                                                  fun _gen_bind_418 ->
                                                                     _gen_bind_418
                                                                  _env_417)) | Effect_ReadEnv -> (fun (() :  unit) (_k_419 :  env -> _ computation) -> value (fun _env_420 ->

                                                                  (_k_419
                                                                  _env_420)
                                                                  >>
                                                                  fun _gen_bind_421 ->
                                                                     _gen_bind_421
                                                                  _env_420)) | Effect_SetEnv -> (fun (_env_423 :  env) (_k_422 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_422
                                                                  _env_423)
                                                                  >>
                                                                  fun _gen_bind_424 ->
                                                                     _gen_bind_424
                                                                  _env_423)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _r_336));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_409 ->
                                                                     value _gen_id_par_409);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_428,
                                                                  _s_427) : ( env*
                                                                   int)) (_k_426 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_426
                                                                  _s_427) >>
                                                                  fun _gen_bind_429 ->
                                                                     _gen_bind_429
                                                                  _env_428)) | Effect_ReadEnv -> (fun (() :  unit) (_k_430 :  env -> _ computation) -> value (fun _env_431 ->

                                                                  (_k_430
                                                                  _env_431)
                                                                  >>
                                                                  fun _gen_bind_432 ->
                                                                     _gen_bind_432
                                                                  _env_431)) | Effect_SetEnv -> (fun (_env_434 :  env) (_k_433 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_433
                                                                  _env_434)
                                                                  >>
                                                                  fun _gen_bind_435 ->
                                                                     _gen_bind_435
                                                                  _env_434)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _l_335)
                                                       | (Sub (_l_340, _r_341)) ->
                                                          handle { value_clause = (
                                                                  fun _gen_bind_531 ->
                                                                     let
                                                                  _gen_bind_532 =
                                                                  fun _x2_546 ->
                                                                     value (Pervasives.(-)
                                                                  _gen_bind_531
                                                                  _x2_546) in
                                                                  handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_534 ->
                                                                     value ((* pure *) let _y_535 = Pervasives.(-)
                                                                  _gen_bind_531
                                                                  _gen_bind_534 in
                                                                  fun _ ->
                                                                     value _y_535));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_533 ->
                                                                     value _gen_id_par_533);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_538,
                                                                  _s_537) : ( env*
                                                                   int)) (_k_536 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_536
                                                                  _s_537) >>
                                                                  fun _gen_bind_539 ->
                                                                     _gen_bind_539
                                                                  _env_538)) | Effect_ReadEnv -> (fun (() :  unit) (_k_540 :  env -> _ computation) -> value (fun _env_541 ->

                                                                  (_k_540
                                                                  _env_541)
                                                                  >>
                                                                  fun _gen_bind_542 ->
                                                                     _gen_bind_542
                                                                  _env_541)) | Effect_SetEnv -> (fun (_env_544 :  env) (_k_543 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_543
                                                                  _env_544)
                                                                  >>
                                                                  fun _gen_bind_545 ->
                                                                     _gen_bind_545
                                                                  _env_544)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _r_341));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_530 ->
                                                                     value _gen_id_par_530);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_549,
                                                                  _s_548) : ( env*
                                                                   int)) (_k_547 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_547
                                                                  _s_548) >>
                                                                  fun _gen_bind_550 ->
                                                                     _gen_bind_550
                                                                  _env_549)) | Effect_ReadEnv -> (fun (() :  unit) (_k_551 :  env -> _ computation) -> value (fun _env_552 ->

                                                                  (_k_551
                                                                  _env_552)
                                                                  >>
                                                                  fun _gen_bind_553 ->
                                                                     _gen_bind_553
                                                                  _env_552)) | Effect_SetEnv -> (fun (_env_555 :  env) (_k_554 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_554
                                                                  _env_555)
                                                                  >>
                                                                  fun _gen_bind_556 ->
                                                                     _gen_bind_556
                                                                  _env_555)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _l_340)
                                                       | (Div (_l_345, _r_346)) ->
                                                          handle { value_clause = (
                                                                  fun _r_num_644 ->
                                                                     (match _r_num_644 with
                                                                  | 0 ->
                                                                     call Effect_Arith_DivByZero () (
                                                                  fun _result_645 ->
                                                                     value (fun _ ->
                                                                     value _result_645))
                                                                  | _ ->
                                                                     handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_647 ->

                                                                  (_var_34 (* / *)
                                                                  _gen_bind_647)
                                                                  >>
                                                                  fun _gen_bind_648 ->

                                                                  (_gen_bind_648
                                                                  _r_num_644)
                                                                  >>
                                                                  fun _y_649 ->
                                                                     value (fun _ ->
                                                                     value _y_649));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_646 ->
                                                                     value _gen_id_par_646);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_652,
                                                                  _s_651) : ( env*
                                                                   int)) (_k_650 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_650
                                                                  _s_651) >>
                                                                  fun _gen_bind_653 ->
                                                                     _gen_bind_653
                                                                  _env_652)) | Effect_ReadEnv -> (fun (() :  unit) (_k_654 :  env -> _ computation) -> value (fun _env_655 ->

                                                                  (_k_654
                                                                  _env_655)
                                                                  >>
                                                                  fun _gen_bind_656 ->
                                                                     _gen_bind_656
                                                                  _env_655)) | Effect_SetEnv -> (fun (_env_658 :  env) (_k_657 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_657
                                                                  _env_658)
                                                                  >>
                                                                  fun _gen_bind_659 ->
                                                                     _gen_bind_659
                                                                  _env_658)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _l_345)));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_643 ->
                                                                     value _gen_id_par_643);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_662,
                                                                  _s_661) : ( env*
                                                                   int)) (_k_660 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_660
                                                                  _s_661) >>
                                                                  fun _gen_bind_663 ->
                                                                     _gen_bind_663
                                                                  _env_662)) | Effect_ReadEnv -> (fun (() :  unit) (_k_664 :  env -> _ computation) -> value (fun _env_665 ->

                                                                  (_k_664
                                                                  _env_665)
                                                                  >>
                                                                  fun _gen_bind_666 ->
                                                                     _gen_bind_666
                                                                  _env_665)) | Effect_SetEnv -> (fun (_env_668 :  env) (_k_667 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_667
                                                                  _env_668)
                                                                  >>
                                                                  fun _gen_bind_669 ->
                                                                     _gen_bind_669
                                                                  _env_668)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _r_346)
                                                       | (Ref _x_350) ->
                                                          handle { value_clause = (
                                                                  fun _x_interp_690 ->
                                                                     call Effect_AllocLoc () (
                                                                  fun _result_691 ->
                                                                     call Effect_UpdateLoc (
                                                                  _result_691,
                                                                  _x_interp_690) (
                                                                  fun _result_692 ->
                                                                     value (fun _ ->
                                                                     value _result_692))));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_689 ->
                                                                     value _gen_id_par_689);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_695,
                                                                  _s_694) : ( env*
                                                                   int)) (_k_693 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_693
                                                                  _s_694) >>
                                                                  fun _gen_bind_696 ->
                                                                     _gen_bind_696
                                                                  _env_695)) | Effect_ReadEnv -> (fun (() :  unit) (_k_697 :  env -> _ computation) -> value (fun _env_698 ->

                                                                  (_k_697
                                                                  _env_698)
                                                                  >>
                                                                  fun _gen_bind_699 ->
                                                                     _gen_bind_699
                                                                  _env_698)) | Effect_SetEnv -> (fun (_env_701 :  env) (_k_700 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_700
                                                                  _env_701)
                                                                  >>
                                                                  fun _gen_bind_702 ->
                                                                     _gen_bind_702
                                                                  _env_701)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _x_350)
                                                       | (Deref _x_353) ->
                                                          handle { value_clause = (
                                                                  fun _x_interp_720 ->
                                                                     call Effect_LookupLoc _x_interp_720 (
                                                                  fun _result_721 ->
                                                                     value (fun _ ->
                                                                     value _result_721)));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_719 ->
                                                                     value _gen_id_par_719);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_724,
                                                                  _s_723) : ( env*
                                                                   int)) (_k_722 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_722
                                                                  _s_723) >>
                                                                  fun _gen_bind_725 ->
                                                                     _gen_bind_725
                                                                  _env_724)) | Effect_ReadEnv -> (fun (() :  unit) (_k_726 :  env -> _ computation) -> value (fun _env_727 ->

                                                                  (_k_726
                                                                  _env_727)
                                                                  >>
                                                                  fun _gen_bind_728 ->
                                                                     _gen_bind_728
                                                                  _env_727)) | Effect_SetEnv -> (fun (_env_730 :  env) (_k_729 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_729
                                                                  _env_730)
                                                                  >>
                                                                  fun _gen_bind_731 ->
                                                                     _gen_bind_731
                                                                  _env_730)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _x_353)
                                                       | (Assign (_lhs_355,
                                                                  _rhs_356)) ->
                                                          handle { value_clause = (
                                                                  fun _x_loc_790 ->
                                                                     handle {
                                                                   value_clause = (
                                                                  fun _x_interp_792 ->
                                                                     call Effect_UpdateLoc (
                                                                  _x_loc_790,
                                                                  _x_interp_792) (
                                                                  fun _result_793 ->
                                                                     value (fun _ ->
                                                                     value _x_interp_792)));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_791 ->
                                                                     value _gen_id_par_791);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_796,
                                                                  _s_795) : ( env*
                                                                   int)) (_k_794 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_794
                                                                  _s_795) >>
                                                                  fun _gen_bind_797 ->
                                                                     _gen_bind_797
                                                                  _env_796)) | Effect_ReadEnv -> (fun (() :  unit) (_k_798 :  env -> _ computation) -> value (fun _env_799 ->

                                                                  (_k_798
                                                                  _env_799)
                                                                  >>
                                                                  fun _gen_bind_800 ->
                                                                     _gen_bind_800
                                                                  _env_799)) | Effect_SetEnv -> (fun (_env_802 :  env) (_k_801 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_801
                                                                  _env_802)
                                                                  >>
                                                                  fun _gen_bind_803 ->
                                                                     _gen_bind_803
                                                                  _env_802)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _rhs_356));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_789 ->
                                                                     value _gen_id_par_789);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_806,
                                                                  _s_805) : ( env*
                                                                   int)) (_k_804 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_804
                                                                  _s_805) >>
                                                                  fun _gen_bind_807 ->
                                                                     _gen_bind_807
                                                                  _env_806)) | Effect_ReadEnv -> (fun (() :  unit) (_k_808 :  env -> _ computation) -> value (fun _env_809 ->

                                                                  (_k_808
                                                                  _env_809)
                                                                  >>
                                                                  fun _gen_bind_810 ->
                                                                     _gen_bind_810
                                                                  _env_809)) | Effect_SetEnv -> (fun (_env_812 :  env) (_k_811 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_811
                                                                  _env_812)
                                                                  >>
                                                                  fun _gen_bind_813 ->
                                                                     _gen_bind_813
                                                                  _env_812)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                       _lhs_355)
                                                       | (Var _v_359) ->
                                                          value (fun _env_840 ->
                                                          (_lookupEnv_286
                                                          (_v_359, _env_840))
                                                          >>
                                                          fun _y_828 ->
                                                             value _y_828)
                                                       | (App (_e1_361,
                                                               _e2_362)) ->
                                                          let rec _newvar_1043 = fun (
                                                                  _a_300,
                                                                  _interpT_301) ->
                                                                     (match _a_300 with
                                                                  | (LambdaN
                                                                  (_s_302,
                                                                   _t_303)) ->
                                                                     value (fun _env_1246 ->

                                                                  (handle {
                                                                   value_clause = (
                                                                  fun _e2_interp_1132 ->
                                                                     value (fun _ ->

                                                                  (_extendEnv_295
                                                                  (_s_302,
                                                                   _e2_interp_1132,
                                                                   _env_1246))
                                                                  >>
                                                                  fun _ext_1167 ->

                                                                  (handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_1231 ->
                                                                     value (fun _ ->
                                                                     value _gen_bind_1231));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_1230 ->
                                                                     value _gen_id_par_1230);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_1234,
                                                                  _s_1233) : ( env*
                                                                   int)) (_k_1232 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_1232
                                                                  _s_1233) >>
                                                                  fun _gen_bind_1235 ->
                                                                     _gen_bind_1235
                                                                  _env_1234)) | Effect_ReadEnv -> (fun (() :  unit) (_k_1236 :  env -> _ computation) -> value (fun _env_1237 ->

                                                                  (_k_1236
                                                                  _env_1237)
                                                                  >>
                                                                  fun _gen_bind_1238 ->
                                                                     _gen_bind_1238
                                                                  _env_1237)) | Effect_SetEnv -> (fun (_env_1240 :  env) (_k_1239 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_1239
                                                                  _env_1240)
                                                                  >>
                                                                  fun _gen_bind_1241 ->
                                                                     _gen_bind_1241
                                                                  _env_1240)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interpT_301
                                                                  _t_303)) >>
                                                                  fun _gen_bind_1244 ->
                                                                     _gen_bind_1244
                                                                  _ext_1167));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_1131 ->
                                                                     value _gen_id_par_1131);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_1148,
                                                                  _s_1147) : ( env*
                                                                   int)) (_k_1146 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_1146
                                                                  _s_1147) >>
                                                                  fun _gen_bind_1149 ->
                                                                     _gen_bind_1149
                                                                  _env_1148)) | Effect_ReadEnv -> (fun (() :  unit) (_k_1150 :  env -> _ computation) -> value (fun _env_1151 ->

                                                                  (_k_1150
                                                                  _env_1151)
                                                                  >>
                                                                  fun _gen_bind_1152 ->
                                                                     _gen_bind_1152
                                                                  _env_1151)) | Effect_SetEnv -> (fun (_env_1154 :  env) (_k_1153 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_1153
                                                                  _env_1154)
                                                                  >>
                                                                  fun _gen_bind_1155 ->
                                                                     _gen_bind_1155
                                                                  _env_1154)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _e2_362))
                                                                  >>
                                                                  fun _gen_bind_1130 ->
                                                                     _gen_bind_1130
                                                                  _env_1246)
                                                                  | (LambdaV
                                                                  (_s_309,
                                                                   _t_310)) ->
                                                                     value (fun _env_1412 ->

                                                                  (handle {
                                                                   value_clause = (
                                                                  fun _e2_interp_1298 ->
                                                                     value (fun _ ->

                                                                  (_extendEnv_295
                                                                  (_s_309,
                                                                   _e2_interp_1298,
                                                                   _env_1412))
                                                                  >>
                                                                  fun _ext_1333 ->

                                                                  (handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_1397 ->
                                                                     value (fun _ ->
                                                                     value _gen_bind_1397));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_1396 ->
                                                                     value _gen_id_par_1396);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_1400,
                                                                  _s_1399) : ( env*
                                                                   int)) (_k_1398 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_1398
                                                                  _s_1399) >>
                                                                  fun _gen_bind_1401 ->
                                                                     _gen_bind_1401
                                                                  _env_1400)) | Effect_ReadEnv -> (fun (() :  unit) (_k_1402 :  env -> _ computation) -> value (fun _env_1403 ->

                                                                  (_k_1402
                                                                  _env_1403)
                                                                  >>
                                                                  fun _gen_bind_1404 ->
                                                                     _gen_bind_1404
                                                                  _env_1403)) | Effect_SetEnv -> (fun (_env_1406 :  env) (_k_1405 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_1405
                                                                  _env_1406)
                                                                  >>
                                                                  fun _gen_bind_1407 ->
                                                                     _gen_bind_1407
                                                                  _env_1406)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interpT_301
                                                                  _t_310)) >>
                                                                  fun _gen_bind_1410 ->
                                                                     _gen_bind_1410
                                                                  _ext_1333));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_1297 ->
                                                                     value _gen_id_par_1297);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_1314,
                                                                  _s_1313) : ( env*
                                                                   int)) (_k_1312 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_1312
                                                                  _s_1313) >>
                                                                  fun _gen_bind_1315 ->
                                                                     _gen_bind_1315
                                                                  _env_1314)) | Effect_ReadEnv -> (fun (() :  unit) (_k_1316 :  env -> _ computation) -> value (fun _env_1317 ->

                                                                  (_k_1316
                                                                  _env_1317)
                                                                  >>
                                                                  fun _gen_bind_1318 ->
                                                                     _gen_bind_1318
                                                                  _env_1317)) | Effect_SetEnv -> (fun (_env_1320 :  env) (_k_1319 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_1319
                                                                  _env_1320)
                                                                  >>
                                                                  fun _gen_bind_1321 ->
                                                                     _gen_bind_1321
                                                                  _env_1320)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _e2_362))
                                                                  >>
                                                                  fun _gen_bind_1296 ->
                                                                     _gen_bind_1296
                                                                  _env_1412)
                                                                  | (LambdaL
                                                                  (_s_316,
                                                                   _t_317)) ->
                                                                     value (fun _env_1726 ->

                                                                  (handle {
                                                                   value_clause = (
                                                                  fun _e2_interp_1468 ->
                                                                     value (fun _ ->
                                                                     call Effect_AllocLoc () (
                                                                  fun _result_1659 ->
                                                                     call Effect_UpdateLoc (
                                                                  _result_1659,
                                                                  _e2_interp_1468) (
                                                                  fun _result_1677 ->
                                                                     call Effect_UpdateLoc (
                                                                  _result_1659,
                                                                  _e2_interp_1468) (
                                                                  fun _result_1694 ->
                                                                     call Effect_LookupLoc _result_1659 (
                                                                  fun _result_1710 ->

                                                                  (_extendEnv_295
                                                                  (_s_316,
                                                                   _result_1710,
                                                                   _env_1726))
                                                                  >>
                                                                  fun _ext_1711 ->

                                                                  (handle {
                                                                   value_clause = (
                                                                  fun _gen_bind_1714 ->
                                                                     value (fun _ ->
                                                                     value _gen_bind_1714));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_1713 ->
                                                                     value _gen_id_par_1713);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_1717,
                                                                  _s_1716) : ( env*
                                                                   int)) (_k_1715 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_1715
                                                                  _s_1716) >>
                                                                  fun _gen_bind_1718 ->
                                                                     _gen_bind_1718
                                                                  _env_1717)) | Effect_ReadEnv -> (fun (() :  unit) (_k_1719 :  env -> _ computation) -> value (fun _env_1720 ->

                                                                  (_k_1719
                                                                  _env_1720)
                                                                  >>
                                                                  fun _gen_bind_1721 ->
                                                                     _gen_bind_1721
                                                                  _env_1720)) | Effect_SetEnv -> (fun (_env_1723 :  env) (_k_1722 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_1722
                                                                  _env_1723)
                                                                  >>
                                                                  fun _gen_bind_1724 ->
                                                                     _gen_bind_1724
                                                                  _env_1723)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interpT_301
                                                                  _t_317)) >>
                                                                  fun _gen_bind_1712 ->
                                                                     _gen_bind_1712
                                                                  _ext_1711))))));
                                                                  finally_clause = (
                                                                  fun _gen_id_par_1467 ->
                                                                     value _gen_id_par_1467);
                                                                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_InEnv -> (fun ((
                                                                  _env_1484,
                                                                  _s_1483) : ( env*
                                                                   int)) (_k_1482 :  int -> _ computation) -> value (fun _ ->

                                                                  (_k_1482
                                                                  _s_1483) >>
                                                                  fun _gen_bind_1485 ->
                                                                     _gen_bind_1485
                                                                  _env_1484)) | Effect_ReadEnv -> (fun (() :  unit) (_k_1486 :  env -> _ computation) -> value (fun _env_1487 ->

                                                                  (_k_1486
                                                                  _env_1487)
                                                                  >>
                                                                  fun _gen_bind_1488 ->
                                                                     _gen_bind_1488
                                                                  _env_1487)) | Effect_SetEnv -> (fun (_env_1490 :  env) (_k_1489 :  env -> _ computation) -> value (fun _ ->

                                                                  (_k_1489
                                                                  _env_1490)
                                                                  >>
                                                                  fun _gen_bind_1491 ->
                                                                     _gen_bind_1491
                                                                  _env_1490)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_interp_327
                                                                  _e2_362))
                                                                  >>
                                                                  fun _gen_bind_1466 ->
                                                                     _gen_bind_1466
                                                                  _env_1726)) in _newvar_1043
                                                       (_e1_361, _interp_327)) in _newvar_157
                        _finalCase_423) >>
                        fun _gen_bind_426 ->
                           (handle { value_clause = (fun _y_1746 ->
                                                        value (fun _ ->
                                                        value _y_1746));
                                    finally_clause = (fun _gen_id_par_1745 ->
                                                         value _gen_id_par_1745);
                                    effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_LookupLoc -> (fun (_x_1748 :  loc) (_k_1747 :  int -> _ computation) -> value (fun _s_1749 ->
                                       (_lookupState_257 (_x_1748, _s_1749))
                                       >>
                                       fun _gen_bind_1750 ->
                                          (_k_1747 _gen_bind_1750) >>
                                          fun _gen_bind_1751 ->
                                             _gen_bind_1751
                                          _s_1749)) | Effect_UpdateLoc -> (fun ((
                                    _x_1754, _y_1753) : ( loc*
                                     int)) (_k_1752 :  loc -> _ computation) -> value (fun _s_1755 ->
                                       (_k_1752 _x_1754) >>
                                       fun _gen_bind_1756 ->
                                          (_updateState_266
                                          (_x_1754, _y_1753, _s_1755)) >>
                                          fun _gen_bind_1757 ->
                                             _gen_bind_1756
                                          _gen_bind_1757)) | Effect_AllocLoc -> (fun (() :  unit) (_k_1758 :  loc -> _ computation) -> value (fun _s_1759 ->
                                       (_getNewLoc_284 _s_1759) >>
                                       fun _gen_bind_1760 ->
                                          (_k_1758 _gen_bind_1760) >>
                                          fun _gen_bind_1761 ->
                                             _gen_bind_1761
                                          _s_1759)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_gen_bind_426
                           [])) >> fun _gen_bind_425 ->  _gen_bind_425 [])
