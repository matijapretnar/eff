(*
=== GENERATED FROM queens.eff ===
=== BEGIN SOURCE ===

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec not_attacked x' = function
  | [] -> true
  | x :: xs -> if no_attack x' x then not_attacked x' xs else false

let available (number_of_queens, x, qs) =
  let rec loop (possible, y) =
    if y < 1 then
      possible
    else if not_attacked (x, y) qs then
      loop ((y :: possible), (y - 1))
    else
      loop (possible, (y - 1))
  in
  loop ([], number_of_queens)

(******************************************************************************)

effect Decide : unit -> bool
effect Fail : unit -> empty

let rec choose = function
  | [] -> (match (#Fail ()) with)
  | x::xs -> if #Decide () then x else choose xs

let backtrack = handler
  | val y -> (fun _ -> y)
  | #Decide _ k -> (fun kf -> k true (fun () -> k false kf) )  
  | #Fail _ _ -> (fun kf -> kf ())

 let choose_all = handler
  | val x -> [x]
  | #Decide _ k -> k true @ k false
  | #Fail _ _ -> []

(******************************************************************************)

let queens number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then qs else
      let y = choose (available (number_of_queens, x, qs)) in
      place ((x + 1), ((x, y) :: qs))
  in
  place (1, [])

let queens_one number_of_queens =
  (with backtrack handle queens number_of_queens) (fun () -> (absurd (#Fail ())))

let queens_all number_of_queens =
  with choose_all handle queens number_of_queens

=== END SOURCE ===
*)

type ('eff_arg,'eff_res) effect = ..
type 'a computation =
  | Value: 'a -> 'a computation 
  | Call: ('eff_arg,'eff_res) effect* 'eff_arg* ('eff_res -> 'a computation)
  -> 'a computation 
type ('eff_arg,'eff_res,'b) effect_clauses =
  ('eff_arg,'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b
type ('a,'b) handler_clauses =
  {
  value_clause: 'a -> 'b ;
  effect_clauses: 'eff_arg 'eff_res . ('eff_arg,'eff_res,'b) effect_clauses }
let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> (k y) >> f))) 
let rec handler (h : ('a,'b) handler_clauses) =
  (let rec handler =
     function
     | Value x -> h.value_clause x
     | Call (eff,arg,k) ->
         let clause = h.effect_clauses eff  in
         clause arg (fun y  -> handler (k y))
      in
   handler : 'a computation -> 'b)
  
let value (x : 'a) = (Value x : 'a computation) 
let call (eff : ('a,'b) effect) (arg : 'a) (cont : 'b -> 'c computation) =
  (Call (eff, arg, cont) : 'c computation) 
let rec lift (f : 'a -> 'b) =
  (function
   | Value x -> Value (f x)
   | Call (eff,arg,k) -> Call (eff, arg, ((fun y  -> lift f (k y)))) : 
  'a computation -> 'b computation) 
let effect eff arg = call eff arg value 
let run =
  function | Value x -> x | Call (eff,_,_) -> failwith "Uncaught effect" 
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
  pow 
let string_length _ = assert false 
let to_string _ = assert false 
let lift_unary f x = value (f x) 
let lift_binary f x = value (fun y  -> value (f x y)) 
let _var_1 = (=) 
let _var_2 = (<) 
let _var_3 = (>) 
let _var_4 = (<>) 
let _var_5 = (<=) 
let _var_6 = (>=) 
let _var_7 = (!=) 
type (_,_) effect +=
  | Effect_Print: (string,unit) effect 
type (_,_) effect +=
  | Effect_Read: (unit,string) effect 
type (_,_) effect +=
  | Effect_Raise: (unit,unit) effect 
let _absurd_8 _void_9 = match _void_9 with | _ -> assert false 
type (_,_) effect +=
  | Effect_DivisionByZero: (unit,unit) effect 
type (_,_) effect +=
  | Effect_InvalidArgument: (string,unit) effect 
type (_,_) effect +=
  | Effect_Failure: (string,unit) effect 
let _failwith_10 _msg_11 =
  call Effect_Failure _msg_11 (fun _result_3  -> value (_absurd_8 _result_3)) 
type (_,_) effect +=
  | Effect_AssertionFault: (unit,unit) effect 
let _var_13 = (~-) 
let _var_14 = (+) 
let _var_15 = ( * ) 
let _var_16 = (-) 
let _mod_17 = (mod) 
let _mod_18 _m_19 _n_20 =
  match _n_20 with
  | 0 ->
      call Effect_DivisionByZero ()
        (fun _result_6  -> value (_absurd_8 _result_6))
  | _n_22 -> value (_m_19 mod _n_22) 
let _var_24 = (~-.) 
let _var_25 = (+.) 
let _var_26 = ( *. ) 
let _var_27 = (-.) 
let _var_28 = (/.) 
let _var_29 = (/) 
let _var_30 = ( ** ) 
let _var_31 _m_32 _n_33 =
  match _n_33 with
  | 0 ->
      call Effect_DivisionByZero ()
        (fun _result_9  -> value (_absurd_8 _result_9))
  | _n_35 -> value (_m_32 / _n_35) 
let _float_of_int_37 = float_of_int 
let _var_38 = (^) 
let _string_length_39 = string_length 
let _to_string_40 = to_string 
type 't9 option =
  | None 
  | Some of 't9 
let rec _assoc_41 _x_42 _gen_function_43 =
  match _gen_function_43 with
  | [] -> None
  | (_y_44,_z_45)::_lst_46 ->
      (match _x_42 = _y_44 with
       | true  -> Some _z_45
       | false  -> _assoc_41 _x_42 _lst_46)
  
let _not_50 _x_51 = match _x_51 with | true  -> false | false  -> true 
let rec _range_52 _m_53 _n_54 =
  match _m_53 > _n_54 with
  | true  -> []
  | false  -> _m_53 :: (_range_52 (_m_53 + 1) _n_54) 
let rec _map_62 _f_63 _gen_function_64 =
  match _gen_function_64 with
  | [] -> value []
  | _x_65::_xs_66 ->
      (_f_63 _x_65) >>
        ((fun _y_67  ->
            (_map_62 _f_63 _xs_66) >>
              (fun _ys_68  -> value (_y_67 :: _ys_68))))
  
let _ignore_70 _ = () 
let _take_71 _f_72 _k_73 = _map_62 _f_72 (_range_52 0 _k_73) 
let rec _fold_left_77 _f_78 _a_79 _gen_function_80 =
  match _gen_function_80 with
  | [] -> value _a_79
  | _y_81::_ys_82 ->
      (_f_78 _a_79) >>
        ((fun _gen_bind_84  ->
            _fold_left_77 _f_78 (_gen_bind_84 _y_81) _ys_82))
  
let rec _fold_right_87 _f_88 _xs_89 _a_90 =
  match _xs_89 with
  | [] -> value _a_90
  | _x_91::_xs_92 ->
      (_fold_right_87 _f_88 _xs_92 _a_90) >>
        ((fun _a_93  ->
            (_f_88 _x_91) >>
              (fun _gen_bind_96  -> value (_gen_bind_96 _a_93))))
  
let rec _iter_97 _f_98 _gen_function_99 =
  match _gen_function_99 with
  | [] -> value ()
  | _x_100::_xs_101 -> (_f_98 _x_100) >> ((fun _  -> _iter_97 _f_98 _xs_101)) 
let rec _forall_103 _p_104 _gen_function_105 =
  match _gen_function_105 with
  | [] -> value true
  | _x_106::_xs_107 ->
      (_p_104 _x_106) >>
        ((fun _gen_bind_108  ->
            match _gen_bind_108 with
            | true  -> _forall_103 _p_104 _xs_107
            | false  -> value false))
  
let rec _exists_110 _p_111 _gen_function_112 =
  match _gen_function_112 with
  | [] -> value false
  | _x_113::_xs_114 ->
      (_p_111 _x_113) >>
        ((fun _gen_bind_115  ->
            match _gen_bind_115 with
            | true  -> value true
            | false  -> _exists_110 _p_111 _xs_114))
  
let _mem_117 _x_118 =
  _exists_110
    (fun _x_201  -> value ((fun _x'_119  -> _x_118 = _x'_119) _x_201))
  
let rec _filter_121 _p_122 _gen_function_123 =
  match _gen_function_123 with
  | [] -> value []
  | _x_124::_xs_125 ->
      (_p_122 _x_124) >>
        ((fun _gen_bind_126  ->
            match _gen_bind_126 with
            | true  ->
                (_filter_121 _p_122 _xs_125) >>
                  ((fun _gen_bind_127  -> value (_x_124 :: _gen_bind_127)))
            | false  -> _filter_121 _p_122 _xs_125))
  
let rec _zip_130 _xs_131 _ys_132 =
  match (_xs_131, _ys_132) with
  | ([],[]) -> value []
  | (_x_133::_xs_134,_y_135::_ys_136) ->
      (_zip_130 _xs_134 _ys_136) >>
        ((fun _gen_bind_137  -> value ((_x_133, _y_135) :: _gen_bind_137)))
  | (_,_) ->
      call Effect_InvalidArgument "zip: length mismatch"
        (fun _result_12  -> value (_absurd_8 _result_12))
  
let _reverse_140 _lst_141 =
  let rec _reverse_acc_142 _acc_143 _gen_function_144 =
    match _gen_function_144 with
    | [] -> _acc_143
    | _x_145::_xs_146 -> _reverse_acc_142 (_x_145 :: _acc_143) _xs_146  in
  _reverse_acc_142 [] _lst_141 
let rec _var_149 _xs_150 _ys_151 =
  match _xs_150 with
  | [] -> _ys_151
  | _x_152::_xs_153 -> _x_152 :: (_var_149 _xs_153 _ys_151) 
let rec _length_156 _gen_let_rec_function_157 =
  match _gen_let_rec_function_157 with
  | [] -> 0
  | _x_158::_xs_159 -> (_length_156 _xs_159) + 1 
let _head_162 _gen_function_163 =
  match _gen_function_163 with
  | [] ->
      call Effect_InvalidArgument "head: empty list"
        (fun _result_15  -> value (_absurd_8 _result_15))
  | _x_165::_ -> value _x_165 
let _tail_166 _gen_function_167 =
  match _gen_function_167 with
  | [] ->
      call Effect_InvalidArgument "tail: empty list"
        (fun _result_18  -> value (_absurd_8 _result_18))
  | _x_169::_xs_170 -> value _xs_170 
let _hd_171 = _head_162 
let _tl_172 = _tail_166 
let _abs_173 _x_174 =
  match _x_174 < 0 with | true  -> - _x_174 | false  -> _x_174 
let _min_177 _x_178 _y_179 =
  match _x_178 < _y_179 with | true  -> _x_178 | false  -> _y_179 
let _max_182 _x_183 _y_184 =
  match _x_183 < _y_184 with | true  -> _y_184 | false  -> _x_183 
let _odd_187 _x_188 =
  (_mod_18 _x_188 2) >> (fun _gen_bind_190  -> value (_gen_bind_190 = 1)) 
let _even_192 _x_193 =
  (_mod_18 _x_193 2) >> (fun _gen_bind_195  -> value (_gen_bind_195 = 0)) 
let _id_197 _x_198 = _x_198 
let _compose_199 _f_200 _g_201 _x_202 =
  (_g_201 _x_202) >> (fun _gen_bind_203  -> _f_200 _gen_bind_203) 
let _fst_204 (_x_205,_) = _x_205 
let _snd_206 (_,_y_207) = _y_207 
let _print_208 _v_209 =
  call Effect_Print (_to_string_40 _v_209)
    (fun _result_20  -> value _result_20)
  
let _print_string_211 _str_212 =
  call Effect_Print _str_212 (fun _result_22  -> value _result_22) 
let _print_endline_213 _v_214 =
  call Effect_Print (_to_string_40 _v_214)
    (fun _result_27  ->
       call Effect_Print "\n" (fun _result_24  -> value _result_24))
  
type (_,_) effect +=
  | Effect_Lookup: (unit,int) effect 
type (_,_) effect +=
  | Effect_Update: (int,unit) effect 
;;"End of pervasives"
let _no_attack_216 (_x_217,_y_218) (_x'_219,_y'_220) =
  match _x_217 <> _x'_219 with
  | true  ->
      (match _y_218 <> _y'_220 with
       | true  ->
           (_abs_173 (_x_217 - _x'_219)) <> (_abs_173 (_y_218 - _y'_220))
       | false  -> false)
  | false  -> false 
let rec _not_attacked_232 _x'_233 _gen_function_234 =
  match _gen_function_234 with
  | [] -> true
  | _x_235::_xs_236 ->
      (match _no_attack_216 _x'_233 _x_235 with
       | true  -> _not_attacked_232 _x'_233 _xs_236
       | false  -> false)
  
let _available_240 (_number_of_queens_241,_x_242,_qs_243) =
  let rec _loop_244 (_possible_245,_y_246) =
    match _y_246 < 1 with
    | true  -> _possible_245
    | false  ->
        (match _not_attacked_232 (_x_242, _y_246) _qs_243 with
         | true  -> _loop_244 ((_y_246 :: _possible_245), (_y_246 - 1))
         | false  -> _loop_244 (_possible_245, (_y_246 - 1)))
     in
  _loop_244 ([], _number_of_queens_241) 
type (_,_) effect +=
  | Effect_Decide: (unit,bool) effect 
type (_,_) effect +=
  | Effect_Fail: (unit,unit) effect 
let rec _choose_255 _gen_let_rec_function_256 =
  match _gen_let_rec_function_256 with
  | [] ->
      call Effect_Fail ()
        (fun _result_30  -> value (match _result_30 with | _ -> assert false))
  | _x_258::_xs_259 ->
      call Effect_Decide ()
        (fun _result_33  ->
           match _result_33 with
           | true  -> value _x_258
           | false  -> _choose_255 _xs_259)

let _queens_274 _number_of_queens_275 =
  let rec _place_276 (_x_277,_qs_278) =
    match _x_277 > _number_of_queens_275 with
    | true  -> value _qs_278
    | false  ->
        (_choose_255
           (_available_240 (_number_of_queens_275, _x_277, _qs_278)))
          >>
          ((fun _y_281  ->
              _place_276 ((_x_277 + 1), ((_x_277, _y_281) :: _qs_278))))
     in
  _place_276 (1, []) 
let _queens_one_285 _number_of_queens_286 =
  (fun _x_204  ->
     value
       ((
         let rec _newvar_49 (_x_46,_qs_45) =
           match _x_46 > _number_of_queens_286 with
           | true  -> (fun _  -> _qs_45)
           | false  ->
               let rec _newvar_75 _gen_let_rec_function_256 =
                 match _gen_let_rec_function_256 with
                 | [] -> (fun _kf_95  -> _kf_95 ())
                 | _x_258::_xs_259 ->
                     (fun _kf_122  ->
                        (fun _x_205  ->
                           value
                             (_newvar_49
                                ((_x_46 + 1), ((_x_46, _x_258) :: _qs_45))
                                _x_205))
                          (fun _x_206  ->
                             run
                               ((fun ()  ->
                                   (fun _x_207  ->
                                      value (_newvar_75 _xs_259 _x_207))
                                     (fun _x_208  -> (_kf_122 _x_208)))
                                  _x_206)))
                  in
               (fun x -> run (_newvar_75
                                (_available_240 (_number_of_queens_286, _x_46, _qs_45)) x))
            in
         _newvar_49 (1, [])) _x_204))
    (fun _x_209  ->
       run
         ((fun ()  ->
             call Effect_Fail ()
               (fun _result_36  -> value (_absurd_8 _result_36))) _x_209))
  
let _queens_all_289 _number_of_queens_290 =
  let rec _newvar_136 (_x_133,_qs_132) =
    match _x_133 > _number_of_queens_290 with
    | true  -> [_qs_132]
    | false  ->
        let rec _newvar_158 _gen_let_rec_function_256 =
          match _gen_let_rec_function_256 with
          | [] -> []
          | _x_258::_xs_259 ->
              _var_149
                (_newvar_136 ((_x_133 + 1), ((_x_133, _x_258) :: _qs_132)))
                (_newvar_158 _xs_259)
           in
        _newvar_158 (_available_240 (_number_of_queens_290, _x_133, _qs_132))
     in
  _newvar_136 (1, []) 
