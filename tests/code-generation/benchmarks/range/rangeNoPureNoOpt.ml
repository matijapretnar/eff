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


type (_, _) effect += Effect_Fetch : ( unit,  int) effect

;;


let rec _range_216 = fun _n_217 ->
   (match _n_217 with | 0 ->
                         value []
                      | _ ->
                         ((_var_16 (* - *) _n_217) >>
                          fun _gen_bind_219 ->  _gen_bind_219 1) >>
                         fun _n1_218 ->
                            ((effect Effect_Fetch) ()) >>
                            fun _gen_bind_220 ->
                               (_range_216 _n1_218) >>
                               fun _gen_bind_221 ->
                                  value (((::) (_gen_bind_220, _gen_bind_221))))

;;


let _test_222 = (fun _n_223 ->
   (fun c -> handler { value_clause = (fun _x_225 ->  value _x_225);
                      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with | Effect_Fetch -> (fun (_ :  unit) (_k_224 :  int -> _ computation) -> _k_224
                      42) | eff' -> fun arg k -> Call (eff', arg, k)) : a -> (b -> _ computation) -> _ computation)) } c) (_range_216
_n_223))