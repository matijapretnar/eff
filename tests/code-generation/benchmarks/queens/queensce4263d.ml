(*
=== GENERATED FROM queens.eff ===
=== BEGIN SOURCE ===

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available number_of_queens x qs =
  let rec loop possible y =
    if y < 1 then
      possible
    else if forall (no_attack (x, y)) qs then
      loop (y :: possible) (y - 1)
    else
      loop possible (y - 1)
  in
  loop [] number_of_queens

(******************************************************************************)

effect Decide : unit -> bool
effect Fail : unit -> empty

let rec choose = function
  | [] -> absurd (#Fail ())
  | x::xs -> if #Decide () then x else choose xs

let backtrack = handler
  | #Decide _ k ->
      handle k true with
      | #Fail _ _ -> k false

let choose_all = handler
  | val x -> [x]
  | #Decide _ k -> k true @ k false
  | #Fail _ _ -> []

(******************************************************************************)

let queens number_of_queens =
  let rec place x qs =
    if x > number_of_queens then qs else
      let y = choose (available number_of_queens x qs) in
      place (x + 1) ((x, y) :: qs)
  in
  place 1 []

let queens_one number_of_queens =
  with backtrack handle queens number_of_queens

(* let queens_all number_of_queens = *)
  (* with choose_all handle queens number_of_queens *)

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
let _no_attack_279 (_x_280,_y_281) =
  value
    (fun (_x'_282,_y'_283)  ->
       (_var_67 _x_280) >>
         (fun _gen_bind_285  ->
            (_gen_bind_285 _x'_282) >>
              (fun _gen_bind_284  ->
                 match _gen_bind_284 with
                 | true  ->
                     (_var_67 _y_281) >>
                       ((fun _gen_bind_287  ->
                           (_gen_bind_287 _y'_283) >>
                             (fun _gen_bind_286  ->
                                match _gen_bind_286 with
                                | true  ->
                                    (_abs_211 (Pervasives.(-) _x_280 _x'_282))
                                      >>
                                      ((fun _gen_bind_289  ->
                                          (_var_67 _gen_bind_289) >>
                                            (fun _gen_bind_288  ->
                                               (_abs_211
                                                  (Pervasives.(-) _y_281
                                                     _y'_283))
                                                 >>
                                                 (fun _gen_bind_292  ->
                                                    _gen_bind_288
                                                      _gen_bind_292))))
                                | false  -> value false)))
                 | false  -> value false)))
  
let _available_295 _number_of_queens_296 =
  value
    (fun _x_297  ->
       value
         (fun _qs_298  ->
            let rec _loop_299 _possible_300 =
              value
                (fun _y_301  ->
                   match Pervasives.(<) _y_301 1 with
                   | true  -> value _possible_300
                   | false  ->
                       (_no_attack_279 (_x_297, _y_301)) >>
                         ((fun _gen_bind_306  ->
                             (_forall_128 _gen_bind_306) >>
                               (fun _gen_bind_305  ->
                                  (_gen_bind_305 _qs_298) >>
                                    (fun _gen_bind_304  ->
                                       match _gen_bind_304 with
                                       | true  ->
                                           (_loop_299 (_y_301 ::
                                              _possible_300))
                                             >>
                                             ((fun _gen_bind_307  ->
                                                 _gen_bind_307
                                                   (Pervasives.(-) _y_301 1)))
                                       | false  ->
                                           (_loop_299 _possible_300) >>
                                             ((fun _gen_bind_310  ->
                                                 _gen_bind_310
                                                   (Pervasives.(-) _y_301 1))))))))
               in
            (_loop_299 []) >>
              (fun _gen_bind_313  -> _gen_bind_313 _number_of_queens_296)))
  
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _choose_314 _gen_let_rec_function_315 =
  match _gen_let_rec_function_315 with
  | [] -> call Effect_Fail () (fun _result_78  -> _absurd_5 _result_78)
  | _x_317::_xs_318 ->
      call Effect_Decide ()
        (fun _result_81  ->
           match _result_81 with
           | true  -> value _x_317
           | false  -> _choose_314 _xs_318)
  
let _backtrack_320 =
  {
    value_clause = (fun _gen_id_par_325  -> value _gen_id_par_325);
    finally_clause = (fun _gen_id_par_324  -> value _gen_id_par_324);
    effect_clauses = fun (type a) -> fun (type b) ->
      fun (x : (a,b) effect)  ->
        (match x with
         | Effect_Decide  ->
             (fun (_ : unit)  ->
                fun (_k_321 : bool -> _ computation)  ->
                  handle
                    {
                      value_clause =
                        (fun _gen_id_par_323  -> value _gen_id_par_323);
                      finally_clause =
                        (fun _gen_id_par_322  -> value _gen_id_par_322);
                      effect_clauses = fun (type a) -> fun (type b) ->
                        fun (x : (a,b) effect)  ->
                          (match x with
                           | Effect_Fail  ->
                               (fun (_ : unit)  ->
                                  fun (_ : unit -> _ computation)  ->
                                    _k_321 false)
                           | eff' ->
                               (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                          a -> (b -> _ computation) -> _ computation)
                    } (_k_321 true))
         | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                   (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
  } 
let _choose_all_326 =
  {
    value_clause = (fun _x_332  -> value [_x_332]);
    finally_clause = (fun _gen_id_par_331  -> value _gen_id_par_331);
    effect_clauses = fun (type a) -> fun (type b) ->
      fun (x : (a,b) effect)  ->
        (match x with
         | Effect_Decide  ->
             (fun (_ : unit)  ->
                fun (_k_327 : bool -> _ computation)  ->
                  (_k_327 true) >>
                    (fun _gen_bind_329  ->
                       (_var_187 _gen_bind_329) >>
                         (fun _gen_bind_328  ->
                            (_k_327 false) >>
                              (fun _gen_bind_330  ->
                                 _gen_bind_328 _gen_bind_330))))
         | Effect_Fail  ->
             (fun (_ : unit)  -> fun (_ : unit -> _ computation)  -> value [])
         | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                   (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
  } 
let _queens_333 _number_of_queens_334 =
  let rec _place_335 _x_336 =
    value
      (fun _qs_337  ->
         (_var_52 _x_336) >>
           (fun _gen_bind_339  ->
              (_gen_bind_339 _number_of_queens_334) >>
                (fun _gen_bind_338  ->
                   match _gen_bind_338 with
                   | true  -> value _qs_337
                   | false  ->
                       (_available_295 _number_of_queens_334) >>
                         ((fun _gen_bind_343  ->
                             (_gen_bind_343 _x_336) >>
                               (fun _gen_bind_342  ->
                                  (_gen_bind_342 _qs_337) >>
                                    (fun _gen_bind_341  ->
                                       (_choose_314 _gen_bind_341) >>
                                         (fun _y_340  ->
                                            (_place_335
                                               (Pervasives.(+) _x_336 1))
                                              >>
                                              (fun _gen_bind_344  ->
                                                 _gen_bind_344
                                                   ((_x_336, _y_340) ::
                                                   _qs_337))))))))))
     in
  (_place_335 1) >> (fun _gen_bind_347  -> _gen_bind_347 []) 
let _queens_one_348 _number_of_queens_349 =
  handle
    {
      value_clause = (fun _gen_id_par_85  -> value _gen_id_par_85);
      finally_clause = (fun _gen_id_par_84  -> value _gen_id_par_84);
      effect_clauses = fun (type a) -> fun (type b) ->
        fun (x : (a,b) effect)  ->
          (match x with
           | Effect_Decide  ->
               (fun (_ : unit)  ->
                  fun (_k_86 : bool -> _ computation)  ->
                    handle
                      {
                        value_clause =
                          (fun _gen_id_par_88  -> value _gen_id_par_88);
                        finally_clause =
                          (fun _gen_id_par_87  -> value _gen_id_par_87);
                        effect_clauses = fun (type a) -> fun (type b) ->
                          fun (x : (a,b) effect)  ->
                            (match x with
                             | Effect_Fail  ->
                                 (fun (_ : unit)  ->
                                    fun (_ : unit -> _ computation)  ->
                                      _k_86 false)
                             | eff' ->
                                 (fun arg  -> fun k  -> Call (eff', arg, k)) : 
                            a -> (b -> _ computation) -> _ computation)
                      } (_k_86 true))
           | eff' -> (fun arg  -> fun k  -> Call (eff', arg, k)) : a ->
                                                                    (b ->
                                                                    _
                                                                    computation)
                                                                    ->
                                                                    _
                                                                    computation)
    }
    (let rec _place_335 _x_336 =
       value
         (fun _qs_337  ->
            (_var_52 _x_336) >>
              (fun _gen_bind_339  ->
                 (_gen_bind_339 _number_of_queens_349) >>
                   (fun _gen_bind_338  ->
                      match _gen_bind_338 with
                      | true  -> value _qs_337
                      | false  ->
                          (_available_295 _number_of_queens_349) >>
                            ((fun _gen_bind_343  ->
                                (_gen_bind_343 _x_336) >>
                                  (fun _gen_bind_342  ->
                                     (_gen_bind_342 _qs_337) >>
                                       (fun _gen_bind_341  ->
                                          (_choose_314 _gen_bind_341) >>
                                            (fun _y_340  ->
                                               (_place_335
                                                  (Pervasives.(+) _x_336 1))
                                                 >>
                                                 (fun _gen_bind_344  ->
                                                    _gen_bind_344
                                                      ((_x_336, _y_340) ::
                                                      _qs_337))))))))))
        in
     (_place_335 1) >> (fun _gen_bind_347  -> _gen_bind_347 []))
  
