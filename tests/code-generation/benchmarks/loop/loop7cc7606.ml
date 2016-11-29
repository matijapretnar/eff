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
  call Effect_Failure _msg_8
    (fun __call_result_4  -> _absurd_5 __call_result_4)
  
type (_,_) effect +=
  | Effect_AssertionFault: (unit,unit) effect 
let _assert_10 _b_11 =
  match _b_11 with
  | true  -> value ()
  | false  ->
      call Effect_AssertionFault ()
        (fun __call_result_9  -> _absurd_5 __call_result_9)
  
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
             (fun __call_result_14  -> _absurd_5 __call_result_14)
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
             (fun __call_result_21  -> _absurd_5 __call_result_21)
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
let _take_100 _f_101 =
  value
    (fun _k_102  ->
       (_range_77 0) >>
         (fun _gen_bind_104  ->
            (_gen_bind_104 _k_102) >>
              (fun _r_103  ->
                 (_map_87 _f_101) >>
                   (fun _gen_bind_105  -> _gen_bind_105 _r_103))))
  
let rec _fold_left_106 _f_107 =
  value
    (fun _a_108  ->
       value
         (fun _gen_function_109  ->
            match _gen_function_109 with
            | [] -> value _a_108
            | _y_110::_ys_111 ->
                (_f_107 _a_108) >>
                  ((fun _gen_bind_113  ->
                      (_gen_bind_113 _y_110) >>
                        (fun _a_112  ->
                           (_fold_left_106 _f_107) >>
                             (fun _gen_bind_115  ->
                                (_gen_bind_115 _a_112) >>
                                  (fun _gen_bind_114  ->
                                     _gen_bind_114 _ys_111)))))))
  
let rec _fold_right_116 _f_117 =
  value
    (fun _xs_118  ->
       value
         (fun _a_119  ->
            match _xs_118 with
            | [] -> value _a_119
            | _x_120::_xs_121 ->
                (_fold_right_116 _f_117) >>
                  ((fun _gen_bind_124  ->
                      (_gen_bind_124 _xs_121) >>
                        (fun _gen_bind_123  ->
                           (_gen_bind_123 _a_119) >>
                             (fun _a_122  ->
                                (_f_117 _x_120) >>
                                  (fun _gen_bind_125  -> _gen_bind_125 _a_122)))))))
  
let rec _iter_126 _f_127 =
  value
    (fun _gen_function_128  ->
       match _gen_function_128 with
       | [] -> value ()
       | _x_129::_xs_130 ->
           (_f_127 _x_129) >>
             ((fun _  ->
                 (_iter_126 _f_127) >>
                   (fun _gen_bind_131  -> _gen_bind_131 _xs_130))))
  
let rec _forall_132 _p_133 =
  value
    (fun _gen_function_134  ->
       match _gen_function_134 with
       | [] -> value true
       | _x_135::_xs_136 ->
           (_p_133 _x_135) >>
             ((fun _gen_bind_137  ->
                 match _gen_bind_137 with
                 | true  ->
                     (_forall_132 _p_133) >>
                       ((fun _gen_bind_138  -> _gen_bind_138 _xs_136))
                 | false  -> value false)))
  
let rec _exists_139 _p_140 =
  value
    (fun _gen_function_141  ->
       match _gen_function_141 with
       | [] -> value false
       | _x_142::_xs_143 ->
           (_p_140 _x_142) >>
             ((fun _gen_bind_144  ->
                 match _gen_bind_144 with
                 | true  -> value true
                 | false  ->
                     (_exists_139 _p_140) >>
                       ((fun _gen_bind_145  -> _gen_bind_145 _xs_143)))))
  
let _mem_146 _x_147 =
  _exists_139 (fun _x'_148  -> value (Pervasives.(=) _x_147 _x'_148)) 
let rec _filter_150 _p_151 =
  value
    (fun _gen_function_152  ->
       match _gen_function_152 with
       | [] -> value []
       | _x_153::_xs_154 ->
           (_p_151 _x_153) >>
             ((fun _gen_bind_155  ->
                 match _gen_bind_155 with
                 | true  ->
                     (_filter_150 _p_151) >>
                       ((fun _gen_bind_157  ->
                           (_gen_bind_157 _xs_154) >>
                             (fun _gen_bind_156  ->
                                value (_x_153 :: _gen_bind_156))))
                 | false  ->
                     (_filter_150 _p_151) >>
                       ((fun _gen_bind_158  -> _gen_bind_158 _xs_154)))))
  
let _complement_159 _xs_160 =
  value
    (fun _ys_161  ->
       (_filter_150
          (fun _x_163  ->
             (_mem_146 _x_163) >>
               (fun _gen_bind_165  ->
                  (_gen_bind_165 _ys_161) >>
                    (fun _gen_bind_164  -> _not_50 _gen_bind_164))))
         >> (fun _gen_bind_162  -> _gen_bind_162 _xs_160))
  
let _intersection_166 _xs_167 =
  value
    (fun _ys_168  ->
       (_filter_150
          (fun _x_170  ->
             (_mem_146 _x_170) >>
               (fun _gen_bind_171  -> _gen_bind_171 _ys_168)))
         >> (fun _gen_bind_169  -> _gen_bind_169 _xs_167))
  
let rec _zip_172 _xs_173 =
  value
    (fun _ys_174  ->
       match (_xs_173, _ys_174) with
       | ([],[]) -> value []
       | (_x_175::_xs_176,_y_177::_ys_178) ->
           (_zip_172 _xs_176) >>
             ((fun _gen_bind_180  ->
                 (_gen_bind_180 _ys_178) >>
                   (fun _gen_bind_179  ->
                      value ((_x_175, _y_177) :: _gen_bind_179))))
       | (_,_) ->
           call Effect_InvalidArgument "zip: length mismatch"
             (fun __call_result_44  -> _absurd_5 __call_result_44))
  
let _reverse_182 _lst_183 =
  let rec _reverse_acc_184 _acc_185 =
    value
      (fun _gen_function_186  ->
         match _gen_function_186 with
         | [] -> value _acc_185
         | _x_187::_xs_188 ->
             (_reverse_acc_184 (_x_187 :: _acc_185)) >>
               ((fun _gen_bind_189  -> _gen_bind_189 _xs_188)))
     in
  (_reverse_acc_184 []) >> (fun _gen_bind_190  -> _gen_bind_190 _lst_183) 
let rec _var_191 _xs_192 =
  value
    (fun _ys_193  ->
       match _xs_192 with
       | [] -> value _ys_193
       | _x_194::_xs_195 ->
           (_var_191 _xs_195) >>
             ((fun _gen_bind_197  ->
                 (_gen_bind_197 _ys_193) >>
                   (fun _gen_bind_196  -> value (_x_194 :: _gen_bind_196)))))
  
let rec _length_198 _gen_let_rec_function_199 =
  match _gen_let_rec_function_199 with
  | [] -> value 0
  | _x_200::_xs_201 ->
      (_length_198 _xs_201) >>
        ((fun _gen_bind_203  -> value (Pervasives.(+) _gen_bind_203 1)))
  
let _head_204 _gen_function_205 =
  match _gen_function_205 with
  | [] ->
      call Effect_InvalidArgument "head: empty list"
        (fun __call_result_51  -> _absurd_5 __call_result_51)
  | _x_207::_ -> value _x_207 
let rec _tail_208 _gen_let_rec_function_209 =
  match _gen_let_rec_function_209 with
  | [] ->
      call Effect_InvalidArgument "tail: empty list"
        (fun __call_result_56  -> _absurd_5 __call_result_56)
  | _x_211::_xs_212 -> value _xs_212 
let _abs_213 _x_214 =
  match Pervasives.(<) _x_214 0 with
  | true  -> value (Pervasives.(~-) _x_214)
  | false  -> value _x_214 
let _min_217 _x_218 =
  value
    (fun _y_219  ->
       match Pervasives.(<) _x_218 _y_219 with
       | true  -> value _x_218
       | false  -> value _y_219)
  
let _max_222 _x_223 =
  value
    (fun _y_224  ->
       match Pervasives.(<) _x_223 _y_224 with
       | true  -> value _y_224
       | false  -> value _x_223)
  
let rec _gcd_227 _m_228 =
  value
    (fun _n_229  ->
       match _n_229 with
       | 0 -> value _m_228
       | _ ->
           (_gcd_227 _n_229) >>
             ((fun _g_230  ->
                 (_mod_18 _m_228) >>
                   (fun _gen_bind_232  ->
                      (_gen_bind_232 _n_229) >>
                        (fun _gen_bind_231  -> _g_230 _gen_bind_231)))))
  
let rec _lcm_233 _m_234 =
  value
    (fun _n_235  ->
       (_gcd_227 _m_234) >>
         (fun _gen_bind_237  ->
            (_gen_bind_237 _n_235) >>
              (fun _d_236  ->
                 (_var_31 (Pervasives.( * ) _m_234 _n_235)) >>
                   (fun _gen_bind_238  -> _gen_bind_238 _d_236))))
  
let _odd_241 _x_242 =
  (_mod_18 _x_242) >>
    (fun _gen_bind_245  ->
       (_gen_bind_245 2) >>
         (fun _gen_bind_244  -> value (Pervasives.(=) _gen_bind_244 1)))
  
let _even_246 _x_247 =
  (_mod_18 _x_247) >>
    (fun _gen_bind_250  ->
       (_gen_bind_250 2) >>
         (fun _gen_bind_249  -> value (Pervasives.(=) _gen_bind_249 0)))
  
let _id_251 _x_252 = value _x_252 
let _compose_253 _f_254 =
  value
    (fun _g_255  ->
       value
         (fun _x_256  ->
            (_g_255 _x_256) >> (fun _gen_bind_257  -> _f_254 _gen_bind_257)))
  
let _fst_258 (_x_259,_) = value _x_259 
let _snd_260 (_,_y_261) = value _y_261 
let _print_262 _v_263 =
  (_to_string_40 _v_263) >>
    (fun _s_264  ->
       call Effect_Print _s_264 (fun _result_73  -> value _result_73))
  
let _print_string_265 _str_266 =
  call Effect_Print _str_266 (fun _result_76  -> value _result_76) 
let _print_endline_267 _v_268 =
  (_to_string_40 _v_268) >>
    (fun _s_269  ->
       call Effect_Print _s_269
         (fun __call_result_83  ->
            let _ = __call_result_83  in
            call Effect_Print "\n" (fun _result_79  -> value _result_79)))
  
type (_,_) effect +=
  | Effect_Lookup: (unit,int) effect 
type (_,_) effect +=
  | Effect_Update: (int,unit) effect 
let _state_270 _r_271 =
  value
    (fun _x_272  ->
       value
         {
           value_clause = (fun _y_280  -> value (fun _  -> value _y_280));
           finally_clause = (fun _f_279  -> _f_279 _x_272);
           effect_clauses = fun (type a) -> fun (type b) ->
             fun (x : (a,b) effect)  ->
               (match x with
                | Effect_Lookup  ->
                    (fun (() : unit)  ->
                       fun (_k_276 : int -> _ computation)  ->
                         value
                           (fun _s_277  ->
                              (_k_276 _s_277) >>
                                (fun _gen_bind_278  -> _gen_bind_278 _s_277)))
                | Effect_Update  ->
                    (fun (_s'_273 : int)  ->
                       fun (_k_274 : unit -> _ computation)  ->
                         value
                           (fun _  ->
                              (_k_274 ()) >>
                                (fun _gen_bind_275  -> _gen_bind_275 _s'_273)))
                | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : 
               a -> (b -> _ computation) -> _ computation)
         })
  
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _loop_281 _n_282 =
  match Pervasives.(<) _n_282 0 with
  | true  ->
      call Effect_Fail ()
        (fun __call_result_88  -> _absurd_5 __call_result_88)
  | false  ->
      (match Pervasives.(=) _n_282 0 with
       | true  -> value 0
       | false  ->
           (_loop_281 (Pervasives.(-) _n_282 1)) >>
             ((fun _gen_bind_289  -> value (Pervasives.(+) _gen_bind_289 1))))
  
let rec _loop_acc_292 _n_293 =
  value
    (fun _acc_294  ->
       match Pervasives.(<) _n_293 0 with
       | true  ->
           call Effect_Fail ()
             (fun __call_result_101  -> _absurd_5 __call_result_101)
       | false  ->
           (match Pervasives.(=) _n_293 0 with
            | true  -> value _acc_294
            | false  ->
                (_loop_acc_292 (Pervasives.(-) _n_293 1)) >>
                  ((fun _gen_bind_300  ->
                      _gen_bind_300 (Pervasives.(+) _acc_294 1)))))
  
