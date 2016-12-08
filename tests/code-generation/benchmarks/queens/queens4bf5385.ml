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
let _var_1 (* = *) : 't25 -> ('t25 -> ( bool) computation) computation = ( = )

;;


let _var_2 (* < *) : 't26 -> ('t26 -> ( bool) computation) computation = ( < )

;;


let _var_3 (* > *) : 't27 -> ('t27 -> ( bool) computation) computation = ( > )

;;


let _var_4 (* <> *) : 't28 -> ('t28 -> ( bool) computation) computation = ( <> )

;;


let _var_5 (* <= *) : 't29 -> ('t29 -> ( bool) computation) computation = ( <= )

;;


let _var_6 (* >= *) : 't30 -> ('t30 -> ( bool) computation) computation = ( >= )

;;


let _var_7 (* != *) : 't31 -> ('t31 -> ( bool) computation) computation = ( != )

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


let _var_16 (* ~- *) :  int -> ( int) computation = ( ~- )

;;


let _var_17 (* + *) :  int -> ( int -> ( int) computation) computation = ( + )

;;


let _var_18 (* * *) :  int -> ( int -> ( int) computation) computation = ( * )

;;


let _var_19 (* - *) :  int -> ( int -> ( int) computation) computation = ( - )

;;


let _mod_20 :  int -> ( int -> ( int) computation) computation = ( mod )

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


let _var_27 (* ~-. *) :  float -> ( float) computation = ( ~-. )

;;


let _var_28 (* +. *) :  float -> ( float -> ( float) computation) computation = ( +. )

;;


let _var_29 (* *. *) :  float -> ( float -> ( float) computation) computation = ( *. )

;;


let _var_30 (* -. *) :  float -> ( float -> ( float) computation) computation = ( -. )

;;


let _var_31 (* /. *) :  float -> ( float -> ( float) computation) computation = ( /. )

;;


let _var_32 (* / *) :  int -> ( int -> ( int) computation) computation = ( / )

;;


let _var_33 (* ** *) :  int -> ( int -> ( int) computation) computation = ( ** )

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


let _float_of_int_40 :  int -> ( float) computation = ( float_of_int )

;;


let _var_41 (* ^ *) :  string -> ( string -> ( string) computation) computation = ( ^ )

;;


let _string_length_42 :  string -> ( int) computation = ( string_length )

;;


let _to_string_43 : 't32 -> ( string) computation = ( to_string )

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

let _no_attack_257 = (fun (_x_258, _y_259) ->
   value (fun (_x'_260, _y'_261) ->  (match Pervasives.(<>) _x_258
_x'_260 with | true ->
                (match Pervasives.(<>)
             _y_259
             _y'_261 with | true ->
                             (_abs_189 (Pervasives.(-) _x_258 _x'_260)) >>
                             fun _gen_bind_267 ->
                                let _gen_bind_266 = fun _x2_72 ->
                                       value (Pervasives.(<>) _gen_bind_267
                                    _x2_72) in
                             (_abs_189 (Pervasives.(-) _y_259 _y'_261)) >>
                             fun _gen_bind_270 ->  _gen_bind_266
                             _gen_bind_270
                          | false ->
                             value false)
             | false ->
                value false)))

;;


let _available_273 = (fun (_number_of_queens_274, _x_275, _qs_276) ->
   let rec _loop_277 = fun _possible_278 ->  value (fun _y_279 ->
              (match Pervasives.(<) _y_279
           1 with | true ->
                     value _possible_278
                  | false ->
                     (_no_attack_257 (_x_275, _y_279)) >>
                     fun _gen_bind_284 ->
                        (_forall_106 _gen_bind_284) >>
                        fun _gen_bind_283 ->
                           (_gen_bind_283 _qs_276) >>
                           fun _gen_bind_282 ->
                              (match _gen_bind_282 with | true ->
                                                           (_loop_277
                                                           (((::) (_y_279,
                                                                   _possible_278))))
                                                           >>
                                                           fun _gen_bind_285 ->
                                                              _gen_bind_285
                                                           (Pervasives.(-)
                                                           _y_279 1)
                                                        | false ->
                                                           (_loop_277
                                                           _possible_278) >>
                                                           fun _gen_bind_288 ->
                                                              _gen_bind_288
                                                           (Pervasives.(-)
                                                           _y_279 1)))) in
(_loop_277 []) >> fun _gen_bind_291 ->  _gen_bind_291 _number_of_queens_274)

;;


type (_, _) effect += Effect_Decide : ( unit,  bool) effect

;;


type (_, _) effect += Effect_Fail : ( unit, unit) effect

;;


let rec _choose_292 = fun _gen_let_rec_function_293 ->
   (match _gen_let_rec_function_293 with | [] ->
                                            call Effect_Fail () (fun _result_81 ->
                                                                    _absurd_8
                                                                 _result_81)
                                         | ((_x_295) :: (_xs_296)) ->
                                            call Effect_Decide () (fun _result_84 ->
                                                                     (match _result_84 with
                                                                   | true ->
                                                                     value _x_295
                                                                   | false ->
                                                                     _choose_292
                                                                   _xs_296)))

;;


let _backtrack_298 = { value_clause = (fun _gen_id_par_303 ->
                                          value _gen_id_par_303);
                      finally_clause = (fun _gen_id_par_302 ->
                                           value _gen_id_par_302);
                      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_299 :  bool -> _ computation) -> handle {
                       value_clause = (fun _gen_id_par_301 ->
                                          value _gen_id_par_301);
                      finally_clause = (fun _gen_id_par_300 ->
                                           value _gen_id_par_300);
                      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> _k_299
                      false) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_k_299
                      true)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _choose_all_304 = { value_clause = (fun _x_310 ->
                                           value (((::) (_x_310, []))));
                       finally_clause = (fun _gen_id_par_309 ->
                                            value _gen_id_par_309);
                       effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_305 :  bool -> _ computation) ->
                       (_k_305 true) >>
                       fun _gen_bind_307 ->
                          (_var_165 (* @ *) _gen_bind_307) >>
                          fun _gen_bind_306 ->
                             (_k_305 false) >>
                             fun _gen_bind_308 ->  _gen_bind_306
                             _gen_bind_308) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) }

;;


let _queens_311 = (fun _number_of_queens_312 ->
   let rec _place_313 = fun (_x_314, _qs_315) ->  (match Pervasives.(>)
           _x_314
           _number_of_queens_312 with | true ->
                                         value _qs_315
                                      | false ->
                                         (_available_273
                                         (_number_of_queens_312, _x_314,
                                          _qs_315)) >>
                                         fun _gen_bind_319 ->
                                            (_choose_292 _gen_bind_319) >>
                                            fun _y_318 ->  _place_313
                                            (Pervasives.(+) _x_314 1,
                                             ((::) ((_x_314, _y_318), _qs_315)))) in _place_313
(1, []))

;;

let _queens_one_322 = (fun _number_of_queens_323 ->
   let rec _place_93 = fun (_x_95, _qs_94) ->  (match Pervasives.(>) _x_95
           _number_of_queens_323 with | true ->
                                         value _qs_94
                                      | false ->
                                         (_available_273
                                         (_number_of_queens_323, _x_95,
                                          _qs_94)) >>
                                         fun _gen_bind_96 ->
                                            (_choose_292 _gen_bind_96) >>
                                            fun _y_97 ->  _place_93
                                            (Pervasives.(+) _x_95 1,
                                             ((::) ((_x_95, _y_97), _qs_94)))) in let rec
_newvar_99 = fun (_x_95, _qs_94) ->  (match Pervasives.(>) _x_95
_number_of_queens_323 with | true ->
                              value _qs_94
                           | false ->
                              (_available_273
                              (_number_of_queens_323, _x_95, _qs_94)) >>
                              fun _gen_bind_96 ->
                                 handle { value_clause = (fun _y_127 ->
                                                             handle {
                                                           value_clause = (
                                                          fun _gen_id_par_129 ->
                                                             value _gen_id_par_129);
                                                          finally_clause = (
                                                          fun _gen_id_par_128 ->
                                                             value _gen_id_par_128);
                                                          effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_130 :  bool -> _ computation) -> handle {
                                                           value_clause = (
                                                          fun _gen_id_par_132 ->
                                                             value _gen_id_par_132);
                                                          finally_clause = (
                                                          fun _gen_id_par_131 ->
                                                             value _gen_id_par_131);
                                                          effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> _k_130
                                                          false) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_k_130
                                                          true)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_place_93
                                                          (Pervasives.(+)
                                                           _x_95 1,
                                                           ((::) ((_x_95,
                                                                   _y_127),
                                                                  _qs_94)))));
                                         finally_clause = (fun _gen_id_par_126 ->
                                                              value _gen_id_par_126);
                                         effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_133 :  bool -> _ computation) -> handle {
                                          value_clause = (fun _gen_id_par_135 ->
                                                             value _gen_id_par_135);
                                         finally_clause = (fun _gen_id_par_134 ->
                                                              value _gen_id_par_134);
                                         effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> _k_133
                                         false) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_k_133
                                         true)) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_choose_292
                              _gen_bind_96)) in _newvar_99 (1, []))

;;


let _queens_all_324 = (fun _number_of_queens_325 ->
   let rec _place_143 = fun (_x_145, _qs_144) ->  (match Pervasives.(>)
           _x_145
           _number_of_queens_325 with | true ->
                                         value _qs_144
                                      | false ->
                                         (_available_273
                                         (_number_of_queens_325, _x_145,
                                          _qs_144)) >>
                                         fun _gen_bind_146 ->
                                            (_choose_292 _gen_bind_146) >>
                                            fun _y_147 ->  _place_143
                                            (Pervasives.(+) _x_145 1,
                                             ((::) ((_x_145, _y_147), _qs_144)))) in let rec
_newvar_149 = fun (_x_145, _qs_144) ->  (match Pervasives.(>) _x_145
_number_of_queens_325 with | true ->
                              value (((::) (_qs_144, [])))
                           | false ->
                              (_available_273
                              (_number_of_queens_325, _x_145, _qs_144)) >>
                              fun _gen_bind_146 ->
                                 handle { value_clause = (fun _y_182 ->
                                                             handle {
                                                           value_clause = (
                                                          fun _x_184 ->
                                                             value (((::) (
                                                          _x_184, []))));
                                                          finally_clause = (
                                                          fun _gen_id_par_183 ->
                                                             value _gen_id_par_183);
                                                          effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_185 :  bool -> _ computation) ->
                                                          (_k_185 true) >>
                                                          fun _gen_bind_186 ->
                                                             (_var_165 (* @ *)
                                                             _gen_bind_186)
                                                             >>
                                                             fun _gen_bind_187 ->
                                                                (_k_185
                                                                false) >>
                                                                fun _gen_bind_188 ->
                                                                   _gen_bind_187
                                                                _gen_bind_188) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_place_143
                                                          (Pervasives.(+)
                                                           _x_145 1,
                                                           ((::) ((_x_145,
                                                                   _y_182),
                                                                  _qs_144)))));
                                         finally_clause = (fun _gen_id_par_181 ->
                                                              value _gen_id_par_181);
                                         effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Decide -> (fun (_ :  unit) (_k_189 :  bool -> _ computation) ->
                                         (_k_189 true) >>
                                         fun _gen_bind_190 ->
                                            (_var_165 (* @ *) _gen_bind_190)
                                            >>
                                            fun _gen_bind_191 ->
                                               (_k_189 false) >>
                                               fun _gen_bind_192 ->
                                                  _gen_bind_191
                                               _gen_bind_192) | Effect_Fail -> (fun (_ :  unit) (_ : unit -> _ computation) -> value []) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } (_choose_292
                              _gen_bind_146)) in _newvar_149
(1, []))
