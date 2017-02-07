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


type (_, _) effect += Effect_Symbol : ( string, ( unit -> ( string) computation)) effect

;;


type (_, _) effect += Effect_Fail : ( unit, unit) effect

;;


type (_, _) effect += Effect_Decide : ( unit,  bool) effect

;;


let _parse_257 = { value_clause = (fun _y_271 ->  value (fun _s_272 ->
                                      (match _s_272 with | [] ->
                                                            value _y_271
                                                         | _ ->
                                                            call Effect_Fail () (
                                                         fun _result_73 ->
                                                            _absurd_8
                                                         _result_73))));
                  finally_clause = (fun _gen_id_par_270 ->
                                       value _gen_id_par_270);
                  effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Symbol -> (fun (_c_258 :  string) (_k_259 : ( unit -> ( string) computation) -> _ computation) -> value (fun _s_260 ->
                     (match _s_260 with | [] ->
                                           (_k_259 (fun () ->
                                              call Effect_Fail () (fun _result_76 ->
                                                                     _absurd_8
                                                                   _result_76)))
                                           >>
                                           fun _gen_bind_261 ->
                                              _gen_bind_261
                                           []
                                        | ((_x_263) :: (_xs_264)) ->
                                           (match Pervasives.(=)
                                        _c_258
                                        _x_263 with | true ->
                                                       (_k_259 (fun () ->
                                                          value _x_263)) >>
                                                       fun _gen_bind_267 ->
                                                          _gen_bind_267
                                                       _xs_264
                                                    | false ->
                                                       (_k_259 (fun () ->
                                                          call Effect_Fail () (
                                                       fun _result_79 ->
                                                          _absurd_8
                                                       _result_79))) >>
                                                       fun _gen_bind_268 ->
                                                          _gen_bind_268
                                                       _s_260)))) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _allsols_274 = { value_clause = (fun _x_280 ->
                                        value (((::) (_x_280, []))));
                    finally_clause = (fun _gen_id_par_279 ->
                                         value _gen_id_par_279);
                    effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_275 :  bool -> _ computation) ->
                    (_k_275 true) >>
                    fun _gen_bind_277 ->
                       (_var_165 (* @ *) _gen_bind_277) >>
                       fun _gen_bind_276 ->
                          (_k_275 false) >>
                          fun _gen_bind_278 ->  _gen_bind_276 _gen_bind_278) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _backtrack_281 = { value_clause = (fun _gen_id_par_286 ->
                                          value _gen_id_par_286);
                      finally_clause = (fun _gen_id_par_285 ->
                                           value _gen_id_par_285);
                      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_282 :  bool -> _ computation) -> handle {
                       value_clause = (fun _gen_id_par_284 ->
                                          value _gen_id_par_284);
                      finally_clause = (fun _gen_id_par_283 ->
                                           value _gen_id_par_283);
                      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> _k_282
                      false) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_k_282
                      true)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _createNumber_287 = (fun (_prev_288, _num_289) ->
   value ((* pure *) let _gen_bind_291 = Pervasives.( * ) _prev_288 10 in
Pervasives.(+) _gen_bind_291 _num_289))

;;


let rec _parseNum_293 = fun (_l_294, _v_295) ->
   (match _l_294 with | [] ->
                         value _v_295
                      | ((_x_296) :: (_xs_297)) ->
                         (match _x_296 with | "0" ->
                                               (_createNumber_287
                                               (_v_295, 0)) >>
                                               fun _gen_bind_298 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_298)
                                            | "1" ->
                                               (_createNumber_287
                                               (_v_295, 1)) >>
                                               fun _gen_bind_299 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_299)
                                            | "2" ->
                                               (_createNumber_287
                                               (_v_295, 2)) >>
                                               fun _gen_bind_300 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_300)
                                            | "3" ->
                                               (_createNumber_287
                                               (_v_295, 3)) >>
                                               fun _gen_bind_301 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_301)
                                            | "4" ->
                                               (_createNumber_287
                                               (_v_295, 4)) >>
                                               fun _gen_bind_302 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_302)
                                            | "5" ->
                                               (_createNumber_287
                                               (_v_295, 5)) >>
                                               fun _gen_bind_303 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_303)
                                            | "6" ->
                                               (_createNumber_287
                                               (_v_295, 6)) >>
                                               fun _gen_bind_304 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_304)
                                            | "7" ->
                                               (_createNumber_287
                                               (_v_295, 7)) >>
                                               fun _gen_bind_305 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_305)
                                            | "8" ->
                                               (_createNumber_287
                                               (_v_295, 8)) >>
                                               fun _gen_bind_306 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_306)
                                            | "9" ->
                                               (_createNumber_287
                                               (_v_295, 9)) >>
                                               fun _gen_bind_307 ->
                                                  _parseNum_293
                                               (_xs_297, _gen_bind_307)))

;;


let rec _toNum_308 = fun _l_309 ->  _parseNum_293 (_l_309, 0)

;;


let _digit_310 = (fun () ->
   let rec _checkNums_312 = fun _n_313 ->
              (match _n_313 with | [] ->
                                    call Effect_Fail () (fun _result_84 ->
                                                            _absurd_8
                                                         _result_84)
                                 | ((_x_315) :: (_xs_316)) ->
                                    call Effect_Decide () (fun _result_90 ->
                                                              (match _result_90 with
                                                           | true ->
                                                              call Effect_Symbol _x_315 (
                                                           fun _result_87 ->
                                                              _result_87
                                                           ())
                                                           | false ->
                                                              _checkNums_312
                                                           _xs_316))) in let rec
_newvar_96 = fun _n_313 ->
   (match _n_313 with | [] ->
                         call Effect_Fail () (fun _result_102 ->
                                                 (_absurd_8 _result_102) >>
                                                 fun _gen_id_par_98 ->
                                                    value _gen_id_par_98)
                      | ((_x_315) :: (_xs_316)) ->
                         call Effect_Symbol _x_315 (fun _result_134 ->
                                                       handle { value_clause = (
                                                               fun _gen_id_par_141 ->
                                                                  value _gen_id_par_141);
                                                               finally_clause = (
                                                               fun _gen_id_par_140 ->
                                                                  value _gen_id_par_140);
                                                               effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> _newvar_96
                                                               _xs_316) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (handle {
                                                     value_clause = (
                                                    fun _gen_id_par_136 ->
                                                       value _gen_id_par_136);
                                                    finally_clause = (
                                                    fun _gen_id_par_135 ->
                                                       value _gen_id_par_135);
                                                    effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_137 :  bool -> _ computation) -> handle {
                                                     value_clause = (
                                                    fun _gen_id_par_139 ->
                                                       value _gen_id_par_139);
                                                    finally_clause = (
                                                    fun _gen_id_par_138 ->
                                                       value _gen_id_par_138);
                                                    effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> _k_137
                                                    false) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_k_137
                                                    true)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_result_134
                                                    ())))) in _newvar_96
(((::) ("0",
        ((::) ("1",
               ((::) ("2",
                      ((::) ("3",
                             ((::) ("4",
                                    ((::) ("5",
                                           ((::) ("6",
                                                  ((::) ("7",
                                                         ((::) ("8",
                                                                ((::) (
                                                                "9", []))))))))))))))))))))))

;;


let rec _many_319 = fun _m_320 ->
   call Effect_Decide () (fun _result_144 ->
                             (match _result_144 with | true ->
                                                        _m_320
                                                     ()
                                                     | false ->
                                                        value []))

;;


let rec _many1_322 = fun () ->
   (_digit_310 ()) >>
   fun _x_323 ->
      (_many_319 _many1_322) >>
      fun _xs_324 ->
         (_var_165 (* @ *) (((::) (_x_323, [])))) >>
         fun _gen_bind_325 ->  _gen_bind_325 _xs_324

;;


let rec _expr_326 = fun () ->
   let rec _term_327 = fun () ->
              let rec _factor_328 = fun () ->
                         call Effect_Decide () (fun _result_169 ->
                                                   (match _result_169 with
                                                | true ->
                                                   (_many1_322 ()) >>
                                                   fun _i_330 ->  _toNum_308
                                                   _i_330
                                                | false ->
                                                   call Effect_Symbol "(" (
                                                fun _result_166 ->
                                                   (_result_166 ()) >>
                                                   fun _p_331 ->
                                                      (_expr_326 ()) >>
                                                      fun _j_333 ->
                                                         call Effect_Symbol ")" (
                                                      fun _result_162 ->
                                                         (_result_162 ()) >>
                                                         fun _p_334 ->
                                                            value _j_333)))) in call Effect_Decide () (
           fun _result_158 ->
              (match _result_158 with | true ->
                                         (_factor_328 ()) >>
                                         fun _i_337 ->
                                            call Effect_Symbol "*" (fun _result_155 ->

                                                                    (_result_155
                                                                    ()) >>
                                                                    fun _p_338 ->

                                                                    (_term_327
                                                                    ()) >>
                                                                    fun _j_340 ->
                                                                     value (Pervasives.( * )
                                                                    _i_337
                                                                    _j_340))
                                      | false ->
                                         _factor_328
                                      ())) in call Effect_Decide () (
fun _result_151 ->
   (match _result_151 with | true ->
                              (_term_327 ()) >>
                              fun _i_343 ->
                                 call Effect_Symbol "+" (fun _result_148 ->
                                                            (_result_148 ())
                                                            >>
                                                            fun _p_344 ->
                                                               (_expr_326 ())
                                                               >>
                                                               fun _j_346 ->
                                                                  value (Pervasives.(+)
                                                               _i_343 _j_346))
                           | false ->
                              _term_327
                           ()))

;;

let _parseTest_348 = (fun () ->
   let rec _newvar_409 = fun () ->
              let rec _term_410 = fun () ->
                         let rec _factor_411 = fun () ->
                                    call Effect_Decide () (fun _result_412 ->
                                                              (match _result_412 with
                                                           | true ->
                                                              (_many1_322 ())
                                                              >>
                                                              fun _i_413 ->
                                                                 _toNum_308
                                                              _i_413
                                                           | false ->
                                                              call Effect_Symbol "(" (
                                                           fun _result_414 ->
                                                              (_result_414
                                                              ()) >>
                                                              fun _p_415 ->
                                                                 (_expr_326
                                                                 ()) >>
                                                                 fun _j_416 ->
                                                                    call Effect_Symbol ")" (
                                                                 fun _result_417 ->
                                                                    (_result_417
                                                                    ()) >>
                                                                    fun _p_418 ->
                                                                     value _j_416)))) in call Effect_Decide () (
                      fun _result_419 ->
                         (match _result_419 with | true ->
                                                    (_factor_411 ()) >>
                                                    fun _i_420 ->
                                                       call Effect_Symbol "*" (
                                                    fun _result_421 ->
                                                       (_result_421 ()) >>
                                                       fun _p_422 ->
                                                          (_term_410 ()) >>
                                                          fun _j_423 ->
                                                             value (Pervasives.( * )
                                                          _i_420 _j_423))
                                                 | false ->
                                                    _factor_411
                                                 ())) in call Effect_Decide () (
           fun _result_424 ->
              (match _result_424 with | true ->
                                         handle { value_clause = (fun _i_426 ->
                                                                     value (fun _s_427 ->
                                                                     (match _s_427 with
                                                                  | [] ->
                                                                     call Effect_Fail () (
                                                                  fun _result_428 ->

                                                                  (_absurd_8
                                                                  _result_428)
                                                                  >>
                                                                  fun _p_429 ->

                                                                  (_newvar_409
                                                                  ()) >>
                                                                  fun _gen_bind_430 ->
                                                                     _gen_bind_430
                                                                  [])
                                                                  | ((_x_432) :: (_xs_431)) ->
                                                                     (match Pervasives.(=)
                                                                  "+"
                                                                  _x_432 with
                                                                  | true ->

                                                                  (_newvar_409
                                                                  ()) >>
                                                                  fun _gen_bind_433 ->
                                                                     _gen_bind_433
                                                                  _xs_431
                                                                  | false ->
                                                                     call Effect_Fail () (
                                                                  fun _result_434 ->

                                                                  (_absurd_8
                                                                  _result_434)
                                                                  >>
                                                                  fun _p_435 ->

                                                                  (_newvar_409
                                                                  ()) >>
                                                                  fun _gen_bind_436 ->
                                                                     _gen_bind_436
                                                                  _s_427)))));
                                                 finally_clause = (fun _gen_id_par_425 ->
                                                                     value _gen_id_par_425);
                                                 effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Symbol -> (fun (_c_438 :  string) (_k_437 : ( unit -> ( string) computation) -> _ computation) -> value (fun _s_439 ->
                                                    (match _s_439 with
                                                 | [] ->
                                                    (_k_437 (fun () ->
                                                       call Effect_Fail () (
                                                    fun _result_441 ->
                                                       _absurd_8
                                                    _result_441))) >>
                                                    fun _gen_bind_440 ->
                                                       _gen_bind_440
                                                    []
                                                 | ((_x_443) :: (_xs_442)) ->
                                                    (match Pervasives.(=)
                                                 _c_438
                                                 _x_443 with | true ->
                                                                (_k_437
                                                                (fun () ->
                                                                   value _x_443))
                                                                >>
                                                                fun _gen_bind_444 ->
                                                                   _gen_bind_444
                                                                _xs_442
                                                             | false ->
                                                                (_k_437
                                                                (fun () ->
                                                                   call Effect_Fail () (
                                                                fun _result_446 ->
                                                                   _absurd_8
                                                                _result_446)))
                                                                >>
                                                                fun _gen_bind_445 ->
                                                                   _gen_bind_445
                                                                _s_439)))) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_term_410
                                      ())
                                      | false ->
                                         handle { value_clause = (fun _y_448 ->
                                                                     value (fun _s_449 ->
                                                                     (match _s_449 with
                                                                  | [] ->
                                                                     value _y_448
                                                                  | _ ->
                                                                     call Effect_Fail () (
                                                                  fun _result_450 ->
                                                                     _absurd_8
                                                                  _result_450))));
                                                 finally_clause = (fun _gen_id_par_447 ->
                                                                     value _gen_id_par_447);
                                                 effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Symbol -> (fun (_c_452 :  string) (_k_451 : ( unit -> ( string) computation) -> _ computation) -> value (fun _s_453 ->
                                                    (match _s_453 with
                                                 | [] ->
                                                    (_k_451 (fun () ->
                                                       call Effect_Fail () (
                                                    fun _result_455 ->
                                                       _absurd_8
                                                    _result_455))) >>
                                                    fun _gen_bind_454 ->
                                                       _gen_bind_454
                                                    []
                                                 | ((_x_457) :: (_xs_456)) ->
                                                    (match Pervasives.(=)
                                                 _c_452
                                                 _x_457 with | true ->
                                                                (_k_451
                                                                (fun () ->
                                                                   value _x_457))
                                                                >>
                                                                fun _gen_bind_458 ->
                                                                   _gen_bind_458
                                                                _xs_456
                                                             | false ->
                                                                (_k_451
                                                                (fun () ->
                                                                   call Effect_Fail () (
                                                                fun _result_460 ->
                                                                   _absurd_8
                                                                _result_460)))
                                                                >>
                                                                fun _gen_bind_459 ->
                                                                   _gen_bind_459
                                                                _s_453)))) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_term_410
                                      ()))) in let rec _newvar_473 = fun () ->
                                                          let rec _term_410 = fun () ->
                                                                     let rec
                                                                  _factor_411 = fun () ->
                                                                     call Effect_Decide () (
                                                                  fun _result_412 ->
                                                                     (match _result_412 with
                                                                  | true ->

                                                                  (_many1_322
                                                                  ()) >>
                                                                  fun _i_413 ->
                                                                     _toNum_308
                                                                  _i_413
                                                                  | false ->
                                                                     call Effect_Symbol "(" (
                                                                  fun _result_414 ->

                                                                  (_result_414
                                                                  ()) >>
                                                                  fun _p_415 ->

                                                                  (_expr_326
                                                                  ()) >>
                                                                  fun _j_416 ->
                                                                     call Effect_Symbol ")" (
                                                                  fun _result_417 ->

                                                                  (_result_417
                                                                  ()) >>
                                                                  fun _p_418 ->
                                                                     value _j_416)))) in call Effect_Decide () (
                                                                  fun _result_419 ->
                                                                     (match _result_419 with
                                                                  | true ->

                                                                  (_factor_411
                                                                  ()) >>
                                                                  fun _i_420 ->
                                                                     call Effect_Symbol "*" (
                                                                  fun _result_421 ->

                                                                  (_result_421
                                                                  ()) >>
                                                                  fun _p_422 ->

                                                                  (_term_410
                                                                  ()) >>
                                                                  fun _j_423 ->
                                                                     value (Pervasives.( * )
                                                                  _i_420
                                                                  _j_423))
                                                                  | false ->
                                                                     _factor_411
                                                                  ())) in
                                                       (handle { value_clause = (
                                                                fun _gen_bind_524 ->
                                                                   handle {
                                                                 value_clause = (
                                                                fun _x_526 ->
                                                                   value (((::) (
                                                                _x_526, []))));
                                                                finally_clause = (
                                                                fun _gen_id_par_525 ->
                                                                   value _gen_id_par_525);
                                                                effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_527 :  bool -> _ computation) ->
                                                                (_k_527 true)
                                                                >>
                                                                fun _gen_bind_528 ->
                                                                   (_var_165 (* @ *)
                                                                   _gen_bind_528)
                                                                   >>
                                                                   fun _gen_bind_529 ->

                                                                   (_k_527
                                                                   false) >>
                                                                   fun _gen_bind_530 ->
                                                                     _gen_bind_529
                                                                   _gen_bind_530) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_gen_bind_524
                                                                (((::) (
                                                                "4",
                                                                ((::) (
                                                                "3",
                                                                ((::) (
                                                                "*",
                                                                ((::) (
                                                                "(",
                                                                ((::) (
                                                                "3",
                                                                ((::) (
                                                                "+",
                                                                ((::) (
                                                                "3",
                                                                ((::) (
                                                                ")", [])))))))))))))))))));
                                                                finally_clause = (
                                                                fun _gen_id_par_523 ->
                                                                   value _gen_id_par_523);
                                                                effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_531 :  bool -> _ computation) ->
                                                                (_k_531 true)
                                                                >>
                                                                fun _gen_bind_532 ->
                                                                   (_var_165 (* @ *)
                                                                   _gen_bind_532)
                                                                   >>
                                                                   fun _gen_bind_533 ->

                                                                   (_k_531
                                                                   false) >>
                                                                   fun _gen_bind_534 ->
                                                                     _gen_bind_533
                                                                   _gen_bind_534) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (handle {
                                                        value_clause = (
                                                       fun _i_476 ->
                                                          value (fun _s_477 ->
                                                          (match _s_477 with
                                                       | [] ->
                                                          call Effect_Fail () (
                                                       fun _result_478 ->
                                                          (_absurd_8
                                                          _result_478) >>
                                                          fun _p_479 ->
                                                             (_newvar_409 ())
                                                             >>
                                                             fun _gen_bind_480 ->
                                                                _gen_bind_480
                                                             [])
                                                       | ((_x_482) :: (_xs_481)) ->
                                                          (match Pervasives.(=)
                                                       "+"
                                                       _x_482 with | true ->

                                                                   (_newvar_409
                                                                   ()) >>
                                                                   fun _gen_bind_483 ->
                                                                     _gen_bind_483
                                                                   _xs_481
                                                                   | false ->
                                                                     call Effect_Fail () (
                                                                   fun _result_484 ->

                                                                   (_absurd_8
                                                                   _result_484)
                                                                   >>
                                                                   fun _p_485 ->

                                                                   (_newvar_409
                                                                   ()) >>
                                                                   fun _gen_bind_486 ->
                                                                     _gen_bind_486
                                                                   _s_477)))));
                                                       finally_clause = (
                                                       fun _gen_id_par_475 ->
                                                          value _gen_id_par_475);
                                                       effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Symbol -> (fun (_c_488 :  string) (_k_487 : ( unit -> ( string) computation) -> _ computation) -> value (fun _s_489 ->
                                                          (match _s_489 with
                                                       | [] ->
                                                          (_k_487 (fun () ->
                                                             call Effect_Fail () (
                                                          fun _result_491 ->
                                                             _absurd_8
                                                          _result_491))) >>
                                                          fun _gen_bind_490 ->
                                                             _gen_bind_490
                                                          []
                                                       | ((_x_493) :: (_xs_492)) ->
                                                          (match Pervasives.(=)
                                                       _c_488
                                                       _x_493 with | true ->

                                                                   (_k_487
                                                                   (fun () ->
                                                                     value _x_493))
                                                                   >>
                                                                   fun _gen_bind_494 ->
                                                                     _gen_bind_494
                                                                   _xs_492
                                                                   | false ->

                                                                   (_k_487
                                                                   (fun () ->
                                                                     call Effect_Fail () (
                                                                   fun _result_496 ->
                                                                     _absurd_8
                                                                   _result_496)))
                                                                   >>
                                                                   fun _gen_bind_495 ->
                                                                     _gen_bind_495
                                                                   _s_489)))) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_term_410
                                                       ()))) >>
                                                       fun _gen_bind_548 ->
                                                          (_var_165 (* @ *)
                                                          _gen_bind_548) >>
                                                          fun _gen_bind_549 ->
                                                             (handle {
                                                              value_clause = (
                                                             fun _gen_bind_536 ->
                                                                handle {
                                                              value_clause = (
                                                             fun _x_538 ->
                                                                value (((::) (
                                                             _x_538, []))));
                                                             finally_clause = (
                                                             fun _gen_id_par_537 ->
                                                                value _gen_id_par_537);
                                                             effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_539 :  bool -> _ computation) ->
                                                             (_k_539 true) >>
                                                             fun _gen_bind_540 ->
                                                                (_var_165 (* @ *)
                                                                _gen_bind_540)
                                                                >>
                                                                fun _gen_bind_541 ->
                                                                   (_k_539
                                                                   false) >>
                                                                   fun _gen_bind_542 ->
                                                                     _gen_bind_541
                                                                   _gen_bind_542) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_gen_bind_536
                                                             (((::) (
                                                             "4",
                                                             ((::) ("3",
                                                                    ((::) (
                                                                    "*",
                                                                    ((::) (
                                                                    "(",
                                                                    ((::) (
                                                                    "3",
                                                                    ((::) (
                                                                    "+",
                                                                    ((::) (
                                                                    "3",
                                                                    ((::) (
                                                                    ")", [])))))))))))))))))));
                                                             finally_clause = (
                                                             fun _gen_id_par_535 ->
                                                                value _gen_id_par_535);
                                                             effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_543 :  bool -> _ computation) ->
                                                             (_k_543 true) >>
                                                             fun _gen_bind_544 ->
                                                                (_var_165 (* @ *)
                                                                _gen_bind_544)
                                                                >>
                                                                fun _gen_bind_545 ->
                                                                   (_k_543
                                                                   false) >>
                                                                   fun _gen_bind_546 ->
                                                                     _gen_bind_545
                                                                   _gen_bind_546) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (handle {
                                                              value_clause = (
                                                             fun _y_498 ->
                                                                value (fun _s_499 ->
                                                                (match _s_499 with
                                                             | [] ->
                                                                value _y_498
                                                             | _ ->
                                                                call Effect_Fail () (
                                                             fun _result_500 ->
                                                                _absurd_8
                                                             _result_500))));
                                                             finally_clause = (
                                                             fun _gen_id_par_497 ->
                                                                value _gen_id_par_497);
                                                             effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Symbol -> (fun (_c_502 :  string) (_k_501 : ( unit -> ( string) computation) -> _ computation) -> value (fun _s_503 ->
                                                                (match _s_503 with
                                                             | [] ->
                                                                (_k_501
                                                                (fun () ->
                                                                   call Effect_Fail () (
                                                                fun _result_505 ->
                                                                   _absurd_8
                                                                _result_505)))
                                                                >>
                                                                fun _gen_bind_504 ->
                                                                   _gen_bind_504
                                                                []
                                                             | ((_x_507) :: (_xs_506)) ->
                                                                (match Pervasives.(=)
                                                             _c_502
                                                             _x_507 with
                                                             | true ->
                                                                (_k_501
                                                                (fun () ->
                                                                   value _x_507))
                                                                >>
                                                                fun _gen_bind_508 ->
                                                                   _gen_bind_508
                                                                _xs_506
                                                             | false ->
                                                                (_k_501
                                                                (fun () ->
                                                                   call Effect_Fail () (
                                                                fun _result_510 ->
                                                                   _absurd_8
                                                                _result_510)))
                                                                >>
                                                                fun _gen_bind_509 ->
                                                                   _gen_bind_509
                                                                _s_503)))) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_term_410
                                                             ()))) >>
                                                             fun _gen_bind_550 ->
                                                                _gen_bind_549
                                                             _gen_bind_550 in _newvar_473
())
