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


let _failwith_10 = (fun _msg_11 ->  (effect Effect_Failure)
_msg_11 >> fun _gen_bind_12 -> _absurd_8 _gen_bind_12)

;;


type (_, _) effect += Effect_AssertionFault : ( unit, unit) effect

;;


let _assert_13 = (fun _b_14 ->
   (match _b_14 with | true ->
                        value ()
                     | false ->
                        (effect Effect_AssertionFault)
                     () >> fun _gen_bind_15 -> _absurd_8
                     _gen_bind_15))

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
                        (effect Effect_DivisionByZero)
                     () >> fun _gen_bind_24 -> _absurd_8
                     _gen_bind_24
                     | _n_25 ->
                        _mod_20
                     _m_22 >> fun _gen_bind_26 -> _gen_bind_26
                     _n_25)))

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
                        (effect Effect_DivisionByZero)
                     () >> fun _gen_bind_37 -> _absurd_8
                     _gen_bind_37
                     | _n_38 ->
                        _var_32 (* / *)
                     _m_35 >> fun _gen_bind_39 -> _gen_bind_39
                     _n_38)))

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
                                   _var_1 (* = *)
                                _x_45 >> fun _gen_bind_51 -> _gen_bind_51
                                _y_47 >> fun _gen_bind_50 -> (match _gen_bind_50 with
                                | true ->
                                   value ((Some _z_48))
                                | false ->
                                   _assoc_44
                                _x_45 >> fun _gen_bind_52 -> _gen_bind_52
                                _lst_49)))

;;

let _not_53 = (fun _x_54 ->
   (match _x_54 with | true ->
                        value false
                     | false ->
                        value true))

;;

let rec _range_55 = fun _m_56 ->
   value (fun _n_57 ->  _var_3 (* > *)
_m_56 >> fun _gen_bind_59 -> _gen_bind_59
_n_57 >> fun _gen_bind_58 -> (match _gen_bind_58 with | true ->
                                                         value []
                                                      | false ->
                                                         value _range_55 >> fun _r_60 -> _var_17 (* + *)
                                                      _m_56 >> fun _gen_bind_64 -> _gen_bind_64
                                                      1 >> fun _gen_bind_63 -> _r_60
                                                      _gen_bind_63 >> fun _gen_bind_62 -> _gen_bind_62
                                                      _n_57 >> fun _gen_bind_61 -> value (((::) (
                                                      _m_56, _gen_bind_61)))))

;;


let rec _map_65 = fun _f_66 ->  value (fun _gen_function_67 ->
   (match _gen_function_67 with | [] ->
                                   value []
                                | ((_x_68) :: (_xs_69)) ->
                                   _f_66
                                _x_68 >> fun _y_70 -> _map_65
                                _f_66 >> fun _gen_bind_72 -> _gen_bind_72
                                _xs_69 >> fun _ys_71 -> value (((::) (
                                _y_70, _ys_71)))))

;;


let _ignore_73 = (fun _ ->  value ())

;;

let _take_74 = (fun _f_75 ->
   value (fun _k_76 ->  _range_55 0 >> fun _gen_bind_78 -> _gen_bind_78
_k_76 >> fun _r_77 -> _map_65 _f_75 >> fun _gen_bind_79 -> _gen_bind_79
_r_77))

;;

let rec _fold_left_80 = fun _f_81 ->  value (fun _a_82 ->
   value (fun _gen_function_83 ->
   (match _gen_function_83 with | [] ->
                                   value _a_82
                                | ((_y_84) :: (_ys_85)) ->
                                   _f_81
                                _a_82 >> fun _gen_bind_87 -> _gen_bind_87
                                _y_84 >> fun _a_86 -> _fold_left_80
                                _f_81 >> fun _gen_bind_89 -> _gen_bind_89
                                _a_86 >> fun _gen_bind_88 -> _gen_bind_88
                                _ys_85)))

;;


let rec _fold_right_90 = fun _f_91 ->  value (fun _xs_92 ->
   value (fun _a_93 ->
   (match _xs_92 with | [] ->
                         value _a_93
                      | ((_x_94) :: (_xs_95)) ->
                         _fold_right_90
                      _f_91 >> fun _gen_bind_98 -> _gen_bind_98
                      _xs_95 >> fun _gen_bind_97 -> _gen_bind_97
                      _a_93 >> fun _a_96 -> _f_91
                      _x_94 >> fun _gen_bind_99 -> _gen_bind_99
                      _a_96)))

;;

let rec _iter_100 = fun _f_101 ->
   value (fun _gen_function_102 ->
   (match _gen_function_102 with | [] ->
                                    value ()
                                 | ((_x_103) :: (_xs_104)) ->
                                    _f_101
                                 _x_103 >> fun _ -> _iter_100
                                 _f_101 >> fun _gen_bind_105 -> _gen_bind_105
                                 _xs_104))

;;


let rec _forall_106 = fun _p_107 ->  value (fun _gen_function_108 ->
   (match _gen_function_108 with | [] ->
                                    value true
                                 | ((_x_109) :: (_xs_110)) ->
                                    _p_107
                                 _x_109 >> fun _gen_bind_111 -> (match _gen_bind_111 with
                                 | true ->
                                    _forall_106
                                 _p_107 >> fun _gen_bind_112 -> _gen_bind_112
                                 _xs_110
                                 | false ->
                                    value false)))

;;


let rec _exists_113 = fun _p_114 ->  value (fun _gen_function_115 ->
   (match _gen_function_115 with | [] ->
                                    value false
                                 | ((_x_116) :: (_xs_117)) ->
                                    _p_114
                                 _x_116 >> fun _gen_bind_118 -> (match _gen_bind_118 with
                                 | true ->
                                    value true
                                 | false ->
                                    _exists_113
                                 _p_114 >> fun _gen_bind_119 -> _gen_bind_119
                                 _xs_117)))

;;


let _mem_120 = (fun _x_121 ->  _exists_113 (fun _x'_122 ->  _var_1 (* = *)
_x_121 >> fun _gen_bind_123 -> _gen_bind_123 _x'_122))

;;


let rec _filter_124 = fun _p_125 ->  value (fun _gen_function_126 ->
   (match _gen_function_126 with | [] ->
                                    value []
                                 | ((_x_127) :: (_xs_128)) ->
                                    _p_125
                                 _x_127 >> fun _gen_bind_129 -> (match _gen_bind_129 with
                                 | true ->
                                    _filter_124
                                 _p_125 >> fun _gen_bind_131 -> _gen_bind_131
                                 _xs_128 >> fun _gen_bind_130 -> value (((::) (
                                 _x_127, _gen_bind_130)))
                                 | false ->
                                    _filter_124
                                 _p_125 >> fun _gen_bind_132 -> _gen_bind_132
                                 _xs_128)))

;;


let _complement_133 = (fun _xs_134 ->  value (fun _ys_135 ->  _filter_124
(fun _x_137 ->  _mem_120 _x_137 >> fun _gen_bind_139 -> _gen_bind_139
_ys_135 >> fun _gen_bind_138 -> _not_53
_gen_bind_138) >> fun _gen_bind_136 -> _gen_bind_136 _xs_134))

;;


let _intersection_140 = (fun _xs_141 ->  value (fun _ys_142 ->  _filter_124
(fun _x_144 ->  _mem_120 _x_144 >> fun _gen_bind_145 -> _gen_bind_145
_ys_142) >> fun _gen_bind_143 -> _gen_bind_143 _xs_141))

;;


let rec _zip_146 = fun _xs_147 ->  value (fun _ys_148 ->
   (match (_xs_147, _ys_148) with | ([], []) ->
                                     value []
                                  | (((_x_149) :: (_xs_150)),
                                     ((_y_151) :: (_ys_152))) ->
                                     _zip_146
                                  _xs_150 >> fun _gen_bind_154 -> _gen_bind_154
                                  _ys_152 >> fun _gen_bind_153 -> value (((::) (
                                  (_x_149, _y_151), _gen_bind_153)))
                                  | (_, _) ->
                                     (effect Effect_InvalidArgument)
                                  "zip: length mismatch" >> fun _gen_bind_155 -> _absurd_8
                                  _gen_bind_155))

;;


let _reverse_156 = (fun _lst_157 ->
   let rec _reverse_acc_158 = fun _acc_159 ->
              value (fun _gen_function_160 ->
              (match _gen_function_160 with | [] ->
                                               value _acc_159
                                            | ((_x_161) :: (_xs_162)) ->
                                               _reverse_acc_158
                                            (((::) (_x_161, _acc_159))) >> fun _gen_bind_163 -> _gen_bind_163
                                            _xs_162)) in _reverse_acc_158
[] >> fun _gen_bind_164 -> _gen_bind_164 _lst_157)

;;


let rec _var_165 (* @ *) = fun _xs_166 ->  value (fun _ys_167 ->
   (match _xs_166 with | [] ->
                          value _ys_167
                       | ((_x_168) :: (_xs_169)) ->
                          _var_165 (* @ *)
                       _xs_169 >> fun _gen_bind_171 -> _gen_bind_171
                       _ys_167 >> fun _gen_bind_170 -> value (((::) (
                       _x_168, _gen_bind_170)))))

;;


let rec _length_172 = fun _gen_let_rec_function_173 ->
   (match _gen_let_rec_function_173 with | [] ->
                                            value 0
                                         | ((_x_174) :: (_xs_175)) ->
                                            _length_172
                                         _xs_175 >> fun _gen_bind_177 -> _var_17 (* + *)
                                         _gen_bind_177 >> fun _gen_bind_176 -> _gen_bind_176
                                         1)

;;


let _head_178 = (fun _gen_function_179 ->
   (match _gen_function_179 with | [] ->
                                    (effect Effect_InvalidArgument)
                                 "head: empty list" >> fun _gen_bind_180 -> _absurd_8
                                 _gen_bind_180
                                 | ((_x_181) :: (_)) ->
                                    value _x_181))

;;


let _tail_182 = (fun _gen_function_183 ->
   (match _gen_function_183 with | [] ->
                                    (effect Effect_InvalidArgument)
                                 "tail: empty list" >> fun _gen_bind_184 -> _absurd_8
                                 _gen_bind_184
                                 | ((_x_185) :: (_xs_186)) ->
                                    value _xs_186))

;;


let _hd_187 = _head_178

;;

let _tl_188 = _tail_182

;;


let _abs_189 = (fun _x_190 ->  _var_2 (* < *)
_x_190 >> fun _gen_bind_192 -> _gen_bind_192
0 >> fun _gen_bind_191 -> (match _gen_bind_191 with | true ->
                                                       _var_16 (* ~- *)
                                                    _x_190
                                                    | false ->
                                                       value _x_190))

;;


let _min_193 = (fun _x_194 ->  value (fun _y_195 ->  _var_2 (* < *)
_x_194 >> fun _gen_bind_197 -> _gen_bind_197
_y_195 >> fun _gen_bind_196 -> (match _gen_bind_196 with | true ->
                                                            value _x_194
                                                         | false ->
                                                            value _y_195)))

;;


let _max_198 = (fun _x_199 ->  value (fun _y_200 ->  _var_2 (* < *)
_x_199 >> fun _gen_bind_202 -> _gen_bind_202
_y_200 >> fun _gen_bind_201 -> (match _gen_bind_201 with | true ->
                                                            value _y_200
                                                         | false ->
                                                            value _x_199)))

;;


let rec _gcd_203 = fun _m_204 ->  value (fun _n_205 ->
   (match _n_205 with | 0 ->
                         value _m_204
                      | _ ->
                         _gcd_203
                      _n_205 >> fun _g_206 -> _mod_21
                      _m_204 >> fun _gen_bind_208 -> _gen_bind_208
                      _n_205 >> fun _gen_bind_207 -> _g_206
                      _gen_bind_207))

;;

let rec _lcm_209 = fun _m_210 ->
   value (fun _n_211 ->  _gcd_203
_m_210 >> fun _gen_bind_213 -> _gen_bind_213
_n_211 >> fun _d_212 -> _var_18 (* * *)
_m_210 >> fun _gen_bind_216 -> _gen_bind_216
_n_211 >> fun _gen_bind_215 -> _var_34 (* / *)
_gen_bind_215 >> fun _gen_bind_214 -> _gen_bind_214 _d_212)

;;


let _odd_217 = (fun _x_218 ->  _mod_21
_x_218 >> fun _gen_bind_221 -> _gen_bind_221
2 >> fun _gen_bind_220 -> _var_1 (* = *)
_gen_bind_220 >> fun _gen_bind_219 -> _gen_bind_219 1)

;;


let _even_222 = (fun _x_223 ->  _mod_21
_x_223 >> fun _gen_bind_226 -> _gen_bind_226
2 >> fun _gen_bind_225 -> _var_1 (* = *)
_gen_bind_225 >> fun _gen_bind_224 -> _gen_bind_224 0)

;;


let _id_227 = (fun _x_228 ->  value _x_228)

;;


let _compose_229 = (fun _f_230 ->  value (fun _g_231 ->  value (fun _x_232 ->
   _g_231 _x_232 >> fun _gen_bind_233 -> _f_230 _gen_bind_233)))

;;


let _fst_234 = (fun (_x_235, _) ->  value _x_235)

;;


let _snd_236 = (fun (_, _y_237) ->  value _y_237)

;;


let _print_238 = (fun _v_239 ->  _to_string_43
_v_239 >> fun _s_240 -> (effect Effect_Print) _s_240)

;;


let _print_string_241 = (fun _str_242 ->  (effect Effect_Print)
_str_242)

;;

let _print_endline_243 = (fun _v_244 ->  _to_string_43
_v_244 >> fun _s_245 -> (effect Effect_Print)
_s_245 >> fun _ -> (effect Effect_Print) "\n")

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
             _k_252 _s_253 >> fun _gen_bind_254 -> _gen_bind_254
          _s_253)) | Effect_Update -> (fun (_s'_249 :  int) (_k_250 :  unit -> _ computation) -> value (fun _ ->
             _k_250 () >> fun _gen_bind_251 -> _gen_bind_251
          _s'_249)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }))

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
                         (effect Effect_VarNotFound)
                      () >> fun _gen_bind_260 -> _absurd_8
                      _gen_bind_260
                      | (((_x'_261, _y_262)) :: (_lst_263)) ->
                         _var_1 (* = *)
                      _x_258 >> fun _gen_bind_265 -> _gen_bind_265
                      _x'_261 >> fun _gen_bind_264 -> (match _gen_bind_264 with
                      | true ->
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
                           _var_1 (* = *)
                        _x_271 >> fun _gen_bind_277 -> _gen_bind_277
                        _x'_273 >> fun _gen_bind_276 -> (match _gen_bind_276 with
                        | true ->
                           value true
                        | false ->
                           _checkLoc_270
                        (_x_271, _lst_275)))

;;


let rec _createLoc_278 = fun (_i_279, _env_280) ->  _checkLoc_270
(_i_279, _env_280) >> fun _gen_bind_281 -> (match _gen_bind_281 with
| true ->
   _var_17 (* + *)
_i_279 >> fun _gen_bind_283 -> _gen_bind_283
1 >> fun _gen_bind_282 -> _createLoc_278
(_gen_bind_282, _env_280)
| false ->
   value _i_279)

;;

let _getNewLoc_284 = (fun _env_285 ->  _createLoc_278
(0, _env_285))

;;

let rec _lookupEnv_286 = fun (_x_287, _y_288) ->
   (match _y_288 with | [] ->
                         (effect Effect_VarNotFound)
                      () >> fun _gen_bind_289 -> _absurd_8
                      _gen_bind_289
                      | (((_x'_290, _y_291)) :: (_lst_292)) ->
                         _var_1 (* = *)
                      _x_287 >> fun _gen_bind_294 -> _gen_bind_294
                      _x'_290 >> fun _gen_bind_293 -> (match _gen_bind_293 with
                      | true ->
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
                         (effect Effect_ReadEnv)
                      () >> fun _envi_304 -> value (fun _v_305 ->
                         _extendEnv_295
                      (_s_302, _v_305, _envi_304) >> fun _ext_306 -> (effect Effect_SetEnv)
                      _ext_306 >> fun _ext_307 -> _interpT_301
                      _t_303 >> fun _gen_bind_308 -> (effect Effect_InEnv)
                      (_ext_307, _gen_bind_308))
                      | (LambdaV (_s_309, _t_310)) ->
                         (effect Effect_ReadEnv)
                      () >> fun _envi_311 -> value (fun _v_312 ->
                         _extendEnv_295
                      (_s_309, _v_312, _envi_311) >> fun _ext_313 -> (effect Effect_SetEnv)
                      _ext_313 >> fun _ext_314 -> _interpT_301
                      _t_310 >> fun _gen_bind_315 -> (effect Effect_InEnv)
                      (_ext_314, _gen_bind_315))
                      | (LambdaL (_s_316, _t_317)) ->
                         (effect Effect_ReadEnv)
                      () >> fun _envi_318 -> value (fun _v_319 ->
                         (effect Effect_AllocLoc)
                      () >> fun _x_loc_320 -> (effect Effect_UpdateLoc)
                      (_x_loc_320, _v_319) >> fun _ -> value _v_319 >> fun _thunk_321 -> (effect Effect_UpdateLoc)
                      (_x_loc_320, _thunk_321) >> fun _tmp_322 -> (effect Effect_LookupLoc)
                      _x_loc_320 >> fun _gen_bind_324 -> _extendEnv_295
                      (_s_316, _gen_bind_324, _envi_318) >> fun _ext_323 -> (effect Effect_SetEnv)
                      _ext_323 >> fun _ext_325 -> _interpT_301
                      _t_317 >> fun _gen_bind_326 -> (effect Effect_InEnv)
                      (_ext_325, _gen_bind_326)))

;;


let rec _interp_327 = fun _a_328 ->
   (match _a_328 with | (Num _b_329) ->
                         value _b_329
                      | (Add (_l_330, _r_331)) ->
                         _interp_327
                      _l_330 >> fun _gen_bind_333 -> _var_17 (* + *)
                      _gen_bind_333 >> fun _gen_bind_332 -> _interp_327
                      _r_331 >> fun _gen_bind_334 -> _gen_bind_332
                      _gen_bind_334
                      | (Mul (_l_335, _r_336)) ->
                         _interp_327
                      _l_335 >> fun _gen_bind_338 -> _var_18 (* * *)
                      _gen_bind_338 >> fun _gen_bind_337 -> _interp_327
                      _r_336 >> fun _gen_bind_339 -> _gen_bind_337
                      _gen_bind_339
                      | (Sub (_l_340, _r_341)) ->
                         _interp_327
                      _l_340 >> fun _gen_bind_343 -> _var_19 (* - *)
                      _gen_bind_343 >> fun _gen_bind_342 -> _interp_327
                      _r_341 >> fun _gen_bind_344 -> _gen_bind_342
                      _gen_bind_344
                      | (Div (_l_345, _r_346)) ->
                         _interp_327
                      _r_346 >> fun _r_num_347 -> (match _r_num_347 with
                      | 0 ->
                         (effect Effect_Arith_DivByZero)
                      ()
                      | _ ->
                         _interp_327
                      _l_345 >> fun _gen_bind_349 -> _var_34 (* / *)
                      _gen_bind_349 >> fun _gen_bind_348 -> _gen_bind_348
                      _r_num_347)
                      | (Ref _x_350) ->
                         _interp_327
                      _x_350 >> fun _x_interp_351 -> (effect Effect_AllocLoc)
                      () >> fun _x_loc_352 -> (effect Effect_UpdateLoc)
                      (_x_loc_352, _x_interp_351)
                      | (Deref _x_353) ->
                         _interp_327
                      _x_353 >> fun _x_interp_354 -> (effect Effect_LookupLoc)
                      _x_interp_354
                      | (Assign (_lhs_355, _rhs_356)) ->
                         _interp_327
                      _lhs_355 >> fun _x_loc_357 -> _interp_327
                      _rhs_356 >> fun _x_interp_358 -> (effect Effect_UpdateLoc)
                      (_x_loc_357, _x_interp_358) >> fun _ -> value _x_interp_358
                      | (Var _v_359) ->
                         (effect Effect_ReadEnv)
                      () >> fun _gen_bind_360 -> _lookupEnv_286
                      (_v_359, _gen_bind_360)
                      | (App (_e1_361, _e2_362)) ->
                         _interpFunc_299
                      (_e1_361, _interp_327) >> fun _e1_interp_363 -> (effect Effect_ReadEnv)
                      () >> fun _envi_364 -> _interp_327
                      _e2_362 >> fun _e2_interp_365 -> (effect Effect_SetEnv)
                      _envi_364 >> fun _envi_366 -> (effect Effect_InEnv)
                      (_envi_366, _e2_interp_365) >> fun _in_env_367 -> _e1_interp_363
                      _in_env_367)

;;


let rec _interpTopLevel_368 = fun _lst_369 ->  value (fun _results_370 ->
   (match _lst_369 with | [] ->
                           value _results_370
                        | ((_top_371) :: (_tail_372)) ->
                           _interpTopLevel_368
                        _tail_372 >> fun _gen_bind_373 -> _var_165 (* @ *)
                        _results_370 >> fun _gen_bind_375 -> _interp_327
                        _top_371 >> fun _gen_bind_376 -> _gen_bind_375
                        (((::) (_gen_bind_376, []))) >> fun _gen_bind_374 -> _gen_bind_373
                        _gen_bind_374))

;;


let _arithmeticHandler_377 = { value_clause = (fun _gen_id_par_380 ->
                                                  value _gen_id_par_380);
                              finally_clause = (fun _gen_id_par_379 ->
                                                   value _gen_id_par_379);
                              effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Arith_DivByZero -> (fun (() :  unit) (_k_378 :  int -> _ computation) -> _var_16 (* ~- *)
                              1) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _storeHandler_381 = { value_clause = (fun _y_398 ->  value (fun _ ->
                                             value _y_398));
                         finally_clause = (fun _gen_id_par_397 ->
                                              value _gen_id_par_397);
                         effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_LookupLoc -> (fun (_x_392 :  loc) (_k_393 :  int -> _ computation) -> value (fun _s_394 ->
                            _lookupState_257
                         (_x_392, _s_394) >> fun _gen_bind_396 -> _k_393
                         _gen_bind_396 >> fun _gen_bind_395 -> _gen_bind_395
                         _s_394)) | Effect_UpdateLoc -> (fun ((_x_386, _y_387) : ( loc*
                          int)) (_k_388 :  loc -> _ computation) -> value (fun _s_389 ->
                            _k_388
                         _x_386 >> fun _gen_bind_390 -> _updateState_266
                         (_x_386, _y_387, _s_389) >> fun _gen_bind_391 -> _gen_bind_390
                         _gen_bind_391)) | Effect_AllocLoc -> (fun (() :  unit) (_k_382 :  loc -> _ computation) -> value (fun _s_383 ->
                            _getNewLoc_284
                         _s_383 >> fun _gen_bind_385 -> _k_382
                         _gen_bind_385 >> fun _gen_bind_384 -> _gen_bind_384
                         _s_383)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

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
                                  _k_408
                               _s_407 >> fun _gen_bind_409 -> _gen_bind_409
                               _env_406)) | Effect_ReadEnv -> (fun (() :  unit) (_k_403 :  env -> _ computation) -> value (fun _env_404 ->
                                  _k_403
                               _env_404 >> fun _gen_bind_405 -> _gen_bind_405
                               _env_404)) | Effect_SetEnv -> (fun (_env_400 :  env) (_k_401 :  env -> _ computation) -> value (fun _ ->
                                  _k_401
                               _env_400 >> fun _gen_bind_402 -> _gen_bind_402
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
                         _var_19 (* - *)
                      _n_419 >> fun _gen_bind_422 -> _gen_bind_422
                      1 >> fun _gen_bind_421 -> _createCase_418
                      _gen_bind_421 >> fun _gen_bind_420 -> value ((App (
                      _lambdaCase_412, _gen_bind_420))))

;;


let _finalCase_423 = run (_createCase_418 200)

;;


let _bigTest_424 = (fun () ->
   handle _storeHandler_381 (handle _environmentHandler_399 (_interp_327
_finalCase_423) >> fun _gen_bind_426 -> _gen_bind_426
[]) >> fun _gen_bind_425 -> _gen_bind_425
[])
