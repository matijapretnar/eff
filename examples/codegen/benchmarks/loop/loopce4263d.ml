(*
=== GENERATED FROM loop.eff ===
=== BEGIN SOURCE ===

effect Fail : unit -> empty

(******************************************************************************)

let rec loop n =
  if n < 0 then
    absurd (#Fail ())
  else if n = 0 then
    0
  else
    loop (n - 1) + 1

let rec loop_acc n acc =
  if n < 0 then
    absurd (#Fail ())
  else if n = 0 then
    acc
  else
    loop_acc (n - 1) (acc + 1)

=== END SOURCE ===
*)

type ('eff_arg,'eff_res) effect = ..
type 'a computation =
  | Value: 'a -> 'a computation 
  | Call: ('eff_arg,'eff_res) effect* 'eff_arg* ('eff_res -> 'a computation)
  -> 'a computation 
type ('a,'b) value_clause = 'a -> 'b computation
type ('a,'b) finally_clause = 'a -> 'b computation
type ('eff_arg,'eff_res,'b) effect_clauses =
  ('eff_arg,'eff_res) effect ->
    'eff_arg -> ('eff_res -> 'b computation) -> 'b computation
type ('a,'b,'c) handler =
  {
  value_clause: ('a,'b) value_clause ;
  finally_clause: ('b,'c) finally_clause ;
  effect_clauses: 'eff_arg 'eff_res . ('eff_arg,'eff_res,'b) effect_clauses }
let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> (k y) >> f))) 
let rec handle (h : ('a,'b,'c) handler) (c : 'a computation) =
  (let rec handler =
     function
     | Value x -> h.value_clause x
     | Call (eff,arg,k) ->
         let clause = h.effect_clauses eff  in
         clause arg (fun y  -> handler (k y))
      in
   (handler c) >> h.finally_clause : 'c computation)
  
let value (x : 'a) = (Value x : 'a computation) 
let call (eff : ('a,'b) effect) (arg : 'a) (cont : 'b -> 'c computation) =
  (Call (eff, arg, cont) : 'c computation) 
let effect eff arg = call eff arg value 
let run =
  function | Value x -> x | Call (eff,_,_) -> failwith "Uncaught effect" 
let (=) x = value (fun y  -> value (Pervasives.(=) x y)) 
let (<) x = value (fun y  -> value (Pervasives.(<) x y)) 
let (<>) x = value (fun y  -> value (Pervasives.(<>) x y)) 
let (>) x = value (fun y  -> value (Pervasives.(>) x y)) 
let (~-) x = value (Pervasives.(~-) x) 
let (+) x = value (fun y  -> value (Pervasives.(+) x y)) 
let ( * ) x = value (fun y  -> value (Pervasives.( * ) x y)) 
let (-) x = value (fun y  -> value (Pervasives.(-) x y)) 
let (mod) x = value (fun y  -> value (Pervasives.(mod) x y)) 
let (~-.) x = value (Pervasives.(~-.) x) 
let (+.) x = value (fun y  -> value (Pervasives.(+.) x y)) 
let ( *. ) x = value (fun y  -> value (Pervasives.( *. ) x y)) 
let (-.) x = value (fun y  -> value (Pervasives.(-.) x y)) 
let (/.) x = value (fun y  -> value (Pervasives.(/.) x y)) 
let (/) x = value (fun y  -> value (Pervasives.(/) x y)) 
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
  fun x  -> value (fun y  -> value (pow x y)) 
let float_of_int x = value (Pervasives.float_of_int x) 
let (^) x = value (fun y  -> value (Pervasives.(^) x y)) 
let string_length x = value (String.length x) 
let to_string _ = failwith "Not implemented" 
let _var_1 : 't1 -> ('t1 -> bool computation) computation = (=) 
let _var_2 : 't2 -> ('t2 -> bool computation) computation = (<) 
let _var_3 : 't3 -> ('t3 -> bool computation) computation = (>) 
let _var_4 : 't4 -> ('t4 -> bool computation) computation = (<>) 
type (_,_) effect +=
  | Effect_Print: (string,unit) effect 
type (_,_) effect +=
  | Effect_Read: (unit,string) effect 
type (_,_) effect +=
  | Effect_Raise: (unit,unit) effect 
let _absurd_5 _void_6 = match _void_6 with | _ -> assert false 
type (_,_) effect +=
  | Effect_DivisionByZero: (unit,unit) effect 
type (_,_) effect +=
  | Effect_InvalidArgument: (string,unit) effect 
type (_,_) effect +=
  | Effect_Failure: (string,unit) effect 
let _failwith_7 _msg_8 =
  call Effect_Failure _msg_8 (fun _result_3  -> _absurd_5 _result_3) 
type (_,_) effect +=
  | Effect_AssertionFault: (unit,unit) effect 
let _assert_10 _b_11 =
  match _b_11 with
  | true  -> value ()
  | false  ->
      call Effect_AssertionFault () (fun _result_6  -> _absurd_5 _result_6)
  
let _var_13 : int -> int computation = (~-) 
let _var_14 : int -> (int -> int computation) computation = (+) 
let _var_15 : int -> (int -> int computation) computation = ( * ) 
let _var_16 : int -> (int -> int computation) computation = (-) 
let _mod_17 : int -> (int -> int computation) computation = (mod) 
let _mod_18 _m_19 =
  value
    (fun _n_20  ->
       match _n_20 with
       | 0 ->
           call Effect_DivisionByZero ()
             (fun _result_9  -> _absurd_5 _result_9)
       | _n_22 -> value (Pervasives.(mod) _m_19 _n_22))
  
let _var_24 : float -> float computation = (~-.) 
let _var_25 : float -> (float -> float computation) computation = (+.) 
let _var_26 : float -> (float -> float computation) computation = ( *. ) 
let _var_27 : float -> (float -> float computation) computation = (-.) 
let _var_28 : float -> (float -> float computation) computation = (/.) 
let _var_29 : int -> (int -> int computation) computation = (/) 
let _var_30 : int -> (int -> int computation) computation = ( ** ) 
let _var_31 _m_32 =
  value
    (fun _n_33  ->
       match _n_33 with
       | 0 ->
           call Effect_DivisionByZero ()
             (fun _result_14  -> _absurd_5 _result_14)
       | _n_35 -> value (Pervasives.(/) _m_32 _n_35))
  
let _float_of_int_37 : int -> float computation = float_of_int 
let _var_38 : string -> (string -> string computation) computation = (^) 
let _string_length_39 : string -> int computation = string_length 
let _to_string_40 : 't5 -> string computation = to_string 
type 't6 option =
  | None 
  | Some of 't6 
let rec _assoc_41 _x_42 =
  value
    (fun _gen_function_43  ->
       match _gen_function_43 with
       | [] -> value None
       | (_y_44,_z_45)::_lst_46 ->
           (match Pervasives.(=) _x_42 _y_44 with
            | true  -> value (Some _z_45)
            | false  ->
                (_assoc_41 _x_42) >>
                  ((fun _gen_bind_49  -> _gen_bind_49 _lst_46))))
  
let _not_50 _x_51 =
  match _x_51 with | true  -> value false | false  -> value true 
let _var_52 _x_53 = value (fun _y_54  -> value (Pervasives.(<) _y_54 _x_53)) 
let _var_56 _x_57 =
  value
    (fun _y_58  ->
       let _lt_59 = Pervasives.(<) _x_57 _y_58  in
       let _eq_61 = Pervasives.(=) _x_57 _y_58  in
       match _lt_59 with | true  -> value true | false  -> value _eq_61)
  
let _var_63 _x_64 =
  value
    (fun _y_65  ->
       (_var_56 _y_65) >> (fun _gen_bind_66  -> _gen_bind_66 _x_64))
  
let _var_67 _x_68 =
  value (fun _y_69  -> _not_50 (Pervasives.(=) _x_68 _y_69)) 
let _var_72 _x_73 =
  value (fun _y_74  -> _not_50 (Pervasives.(=) _x_73 _y_74)) 
let rec _range_77 _m_78 =
  value
    (fun _n_79  ->
       (_var_52 _m_78) >>
         (fun _gen_bind_81  ->
            (_gen_bind_81 _n_79) >>
              (fun _gen_bind_80  ->
                 match _gen_bind_80 with
                 | true  -> value []
                 | false  ->
                     (_range_77 (Pervasives.(+) _m_78 1)) >>
                       ((fun _gen_bind_84  ->
                           (_gen_bind_84 _n_79) >>
                             (fun _gen_bind_83  ->
                                value (_m_78 :: _gen_bind_83)))))))
  
let rec _map_87 _f_88 =
  value
    (fun _gen_function_89  ->
       match _gen_function_89 with
       | [] -> value []
       | _x_90::_xs_91 ->
           (_f_88 _x_90) >>
             ((fun _y_92  ->
                 (_map_87 _f_88) >>
                   (fun _gen_bind_94  ->
                      (_gen_bind_94 _xs_91) >>
                        (fun _ys_93  -> value (_y_92 :: _ys_93))))))
  
let _ignore_95 _ = value () 
let _take_96 _f_97 =
  value
    (fun _k_98  ->
       (_range_77 0) >>
         (fun _gen_bind_100  ->
            (_gen_bind_100 _k_98) >>
              (fun _r_99  ->
                 (_map_87 _f_97) >>
                   (fun _gen_bind_101  -> _gen_bind_101 _r_99))))
  
let rec _fold_left_102 _f_103 =
  value
    (fun _a_104  ->
       value
         (fun _gen_function_105  ->
            match _gen_function_105 with
            | [] -> value _a_104
            | _y_106::_ys_107 ->
                (_f_103 _a_104) >>
                  ((fun _gen_bind_109  ->
                      (_gen_bind_109 _y_106) >>
                        (fun _a_108  ->
                           (_fold_left_102 _f_103) >>
                             (fun _gen_bind_111  ->
                                (_gen_bind_111 _a_108) >>
                                  (fun _gen_bind_110  ->
                                     _gen_bind_110 _ys_107)))))))
  
let rec _fold_right_112 _f_113 =
  value
    (fun _xs_114  ->
       value
         (fun _a_115  ->
            match _xs_114 with
            | [] -> value _a_115
            | _x_116::_xs_117 ->
                (_fold_right_112 _f_113) >>
                  ((fun _gen_bind_120  ->
                      (_gen_bind_120 _xs_117) >>
                        (fun _gen_bind_119  ->
                           (_gen_bind_119 _a_115) >>
                             (fun _a_118  ->
                                (_f_113 _x_116) >>
                                  (fun _gen_bind_121  -> _gen_bind_121 _a_118)))))))
  
let rec _iter_122 _f_123 =
  value
    (fun _gen_function_124  ->
       match _gen_function_124 with
       | [] -> value ()
       | _x_125::_xs_126 ->
           (_f_123 _x_125) >>
             ((fun _  ->
                 (_iter_122 _f_123) >>
                   (fun _gen_bind_127  -> _gen_bind_127 _xs_126))))
  
let rec _forall_128 _p_129 =
  value
    (fun _gen_function_130  ->
       match _gen_function_130 with
       | [] -> value true
       | _x_131::_xs_132 ->
           (_p_129 _x_131) >>
             ((fun _gen_bind_133  ->
                 match _gen_bind_133 with
                 | true  ->
                     (_forall_128 _p_129) >>
                       ((fun _gen_bind_134  -> _gen_bind_134 _xs_132))
                 | false  -> value false)))
  
let rec _exists_135 _p_136 =
  value
    (fun _gen_function_137  ->
       match _gen_function_137 with
       | [] -> value false
       | _x_138::_xs_139 ->
           (_p_136 _x_138) >>
             ((fun _gen_bind_140  ->
                 match _gen_bind_140 with
                 | true  -> value true
                 | false  ->
                     (_exists_135 _p_136) >>
                       ((fun _gen_bind_141  -> _gen_bind_141 _xs_139)))))
  
let _mem_142 _x_143 =
  _exists_135 (fun _x'_144  -> value (Pervasives.(=) _x_143 _x'_144)) 
let rec _filter_146 _p_147 =
  value
    (fun _gen_function_148  ->
       match _gen_function_148 with
       | [] -> value []
       | _x_149::_xs_150 ->
           (_p_147 _x_149) >>
             ((fun _gen_bind_151  ->
                 match _gen_bind_151 with
                 | true  ->
                     (_filter_146 _p_147) >>
                       ((fun _gen_bind_153  ->
                           (_gen_bind_153 _xs_150) >>
                             (fun _gen_bind_152  ->
                                value (_x_149 :: _gen_bind_152))))
                 | false  ->
                     (_filter_146 _p_147) >>
                       ((fun _gen_bind_154  -> _gen_bind_154 _xs_150)))))
  
let _complement_155 _xs_156 =
  value
    (fun _ys_157  ->
       (_filter_146
          (fun _x_159  ->
             (_mem_142 _x_159) >>
               (fun _gen_bind_161  ->
                  (_gen_bind_161 _ys_157) >>
                    (fun _gen_bind_160  -> _not_50 _gen_bind_160))))
         >> (fun _gen_bind_158  -> _gen_bind_158 _xs_156))
  
let _intersection_162 _xs_163 =
  value
    (fun _ys_164  ->
       (_filter_146
          (fun _x_166  ->
             (_mem_142 _x_166) >>
               (fun _gen_bind_167  -> _gen_bind_167 _ys_164)))
         >> (fun _gen_bind_165  -> _gen_bind_165 _xs_163))
  
let rec _zip_168 _xs_169 =
  value
    (fun _ys_170  ->
       match (_xs_169, _ys_170) with
       | ([],[]) -> value []
       | (_x_171::_xs_172,_y_173::_ys_174) ->
           (_zip_168 _xs_172) >>
             ((fun _gen_bind_176  ->
                 (_gen_bind_176 _ys_174) >>
                   (fun _gen_bind_175  ->
                      value ((_x_171, _y_173) :: _gen_bind_175))))
       | (_,_) ->
           call Effect_InvalidArgument "zip: length mismatch"
             (fun _result_35  -> _absurd_5 _result_35))
  
let _reverse_178 _lst_179 =
  let rec _reverse_acc_180 _acc_181 =
    value
      (fun _gen_function_182  ->
         match _gen_function_182 with
         | [] -> value _acc_181
         | _x_183::_xs_184 ->
             (_reverse_acc_180 (_x_183 :: _acc_181)) >>
               ((fun _gen_bind_185  -> _gen_bind_185 _xs_184)))
     in
  (_reverse_acc_180 []) >> (fun _gen_bind_186  -> _gen_bind_186 _lst_179) 
let rec _var_187 _xs_188 =
  value
    (fun _ys_189  ->
       match _xs_188 with
       | [] -> value _ys_189
       | _x_190::_xs_191 ->
           (_var_187 _xs_191) >>
             ((fun _gen_bind_193  ->
                 (_gen_bind_193 _ys_189) >>
                   (fun _gen_bind_192  -> value (_x_190 :: _gen_bind_192)))))
  
let rec _length_194 _gen_let_rec_function_195 =
  match _gen_let_rec_function_195 with
  | [] -> value 0
  | _x_196::_xs_197 ->
      (_length_194 _xs_197) >>
        ((fun _gen_bind_199  -> value (Pervasives.(+) _gen_bind_199 1)))
  
let _head_200 _gen_function_201 =
  match _gen_function_201 with
  | [] ->
      call Effect_InvalidArgument "head: empty list"
        (fun _result_40  -> _absurd_5 _result_40)
  | _x_203::_ -> value _x_203 
let _tail_204 _gen_function_205 =
  match _gen_function_205 with
  | [] ->
      call Effect_InvalidArgument "tail: empty list"
        (fun _result_43  -> _absurd_5 _result_43)
  | _x_207::_xs_208 -> value _xs_208 
let _hd_209 = _head_200 
let _tl_210 = _tail_204 
let _abs_211 _x_212 =
  match Pervasives.(<) _x_212 0 with
  | true  -> value (Pervasives.(~-) _x_212)
  | false  -> value _x_212 
let _min_215 _x_216 =
  value
    (fun _y_217  ->
       match Pervasives.(<) _x_216 _y_217 with
       | true  -> value _x_216
       | false  -> value _y_217)
  
let _max_220 _x_221 =
  value
    (fun _y_222  ->
       match Pervasives.(<) _x_221 _y_222 with
       | true  -> value _y_222
       | false  -> value _x_221)
  
let rec _gcd_225 _m_226 =
  value
    (fun _n_227  ->
       match _n_227 with
       | 0 -> value _m_226
       | _ ->
           (_gcd_225 _n_227) >>
             ((fun _g_228  ->
                 (_mod_18 _m_226) >>
                   (fun _gen_bind_230  ->
                      (_gen_bind_230 _n_227) >>
                        (fun _gen_bind_229  -> _g_228 _gen_bind_229)))))
  
let rec _lcm_231 _m_232 =
  value
    (fun _n_233  ->
       (_gcd_225 _m_232) >>
         (fun _gen_bind_235  ->
            (_gen_bind_235 _n_233) >>
              (fun _d_234  ->
                 (_var_31 (Pervasives.( * ) _m_232 _n_233)) >>
                   (fun _gen_bind_236  -> _gen_bind_236 _d_234))))
  
let _odd_239 _x_240 =
  (_mod_18 _x_240) >>
    (fun _gen_bind_243  ->
       (_gen_bind_243 2) >>
         (fun _gen_bind_242  -> value (Pervasives.(=) _gen_bind_242 1)))
  
let _even_244 _x_245 =
  (_mod_18 _x_245) >>
    (fun _gen_bind_248  ->
       (_gen_bind_248 2) >>
         (fun _gen_bind_247  -> value (Pervasives.(=) _gen_bind_247 0)))
  
let _id_249 _x_250 = value _x_250 
let _compose_251 _f_252 =
  value
    (fun _g_253  ->
       value
         (fun _x_254  ->
            (_g_253 _x_254) >> (fun _gen_bind_255  -> _f_252 _gen_bind_255)))
  
let _fst_256 (_x_257,_) = value _x_257 
let _snd_258 (_,_y_259) = value _y_259 
let _print_260 _v_261 =
  (_to_string_40 _v_261) >>
    (fun _s_262  ->
       call Effect_Print _s_262 (fun _result_58  -> value _result_58))
  
let _print_string_263 _str_264 =
  call Effect_Print _str_264 (fun _result_60  -> value _result_60) 
let _print_endline_265 _v_266 =
  (_to_string_40 _v_266) >>
    (fun _s_267  ->
       call Effect_Print _s_267
         (fun _result_65  ->
            call Effect_Print "\n" (fun _result_62  -> value _result_62)))
  
type (_,_) effect +=
  | Effect_Lookup: (unit,int) effect 
type (_,_) effect +=
  | Effect_Update: (int,unit) effect 
let _state_268 _r_269 =
  value
    (fun _x_270  ->
       value
         {
           value_clause = (fun _y_278  -> value (fun _  -> value _y_278));
           finally_clause = (fun _f_277  -> _f_277 _x_270);
           effect_clauses = fun (type a) -> fun (type b) ->
             fun (x : (a,b) effect)  ->
               (match x with
                | Effect_Lookup  ->
                    (fun (() : unit)  ->
                       fun (_k_274 : int -> _ computation)  ->
                         value
                           (fun _s_275  ->
                              (_k_274 _s_275) >>
                                (fun _gen_bind_276  -> _gen_bind_276 _s_275)))
                | Effect_Update  ->
                    (fun (_s'_271 : int)  ->
                       fun (_k_272 : unit -> _ computation)  ->
                         value
                           (fun _  ->
                              (_k_272 ()) >>
                                (fun _gen_bind_273  -> _gen_bind_273 _s'_271)))
                | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
               a -> (b -> _ computation) -> _ computation)
         })
  
;;value "End of pervasives"
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _loop_279 _n_280 =
  match Pervasives.(<) _n_280 0 with
  | true  -> call Effect_Fail () (fun _result_68  -> _absurd_5 _result_68)
  | false  ->
      (match Pervasives.(=) _n_280 0 with
       | true  -> value 0
       | false  ->
           (_loop_279 (Pervasives.(-) _n_280 1)) >>
             ((fun _gen_bind_287  -> value (Pervasives.(+) _gen_bind_287 1))))
  
let rec _loop_acc_290 _n_291 =
  value
    (fun _acc_292  ->
       match Pervasives.(<) _n_291 0 with
       | true  ->
           call Effect_Fail () (fun _result_79  -> _absurd_5 _result_79)
       | false  ->
           (match Pervasives.(=) _n_291 0 with
            | true  -> value _acc_292
            | false  ->
                (_loop_acc_290 (Pervasives.(-) _n_291 1)) >>
                  ((fun _gen_bind_298  ->
                      _gen_bind_298 (Pervasives.(+) _acc_292 1)))))
  
