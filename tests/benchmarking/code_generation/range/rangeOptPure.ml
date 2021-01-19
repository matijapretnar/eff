type ('eff_arg, 'eff_res) effect = ..

type 'a computation =
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
      -> 'a computation

type ('eff_arg, 'eff_res, 'b) effect_clauses =
  ('eff_arg, 'eff_res) effect -> 'eff_arg -> ('eff_res -> 'b) -> 'b

type ('a, 'b) handler_clauses = {
  value_clause : 'a -> 'b;
  effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res, 'b) effect_clauses;
}

let rec ( >> ) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> k y >> f)

let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler = function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff in
        clause arg (fun y -> handler (k y))
  in
  handler

let value (x : 'a) : 'a computation = Value x

let call (eff : ('a, 'b) effect) (arg : 'a) (cont : 'b -> 'c computation) :
    'c computation =
  Call (eff, arg, cont)

let rec lift (f : 'a -> 'b) : 'a computation -> 'b computation = function
  | Value x -> Value (f x)
  | Call (eff, arg, k) -> Call (eff, arg, fun y -> lift f (k y))

let effect eff arg = call eff arg value

let run = function
  | Value x -> x
  | Call (eff, _, _) -> failwith "Uncaught effect"

let ( ** ) =
  let rec pow a =
    Pervasives.(
      function
      | 0 -> 1
      | 1 -> a
      | n ->
          let b = pow a (n / 2) in
          b * b * if n mod 2 = 0 then 1 else a)
  in
  pow

let string_length _ = assert false

let to_string _ = assert false

let lift_unary f x = value (f x)

let lift_binary f x = value (fun y -> value (f x y))

let _var_1 (* = *) = ( = )

let _var_2 (* < *) = ( < )

let _var_3 (* > *) = ( > )

let _var_4 (* <> *) = ( <> )

let _var_5 (* <= *) = ( <= )

let _var_6 (* >= *) = ( >= )

let _var_7 (* != *) = ( != )

type (_, _) effect += Effect_Print : (string, unit) effect

type (_, _) effect += Effect_Read : (unit, string) effect

type (_, _) effect += Effect_Raise : (unit, unit) effect

let _absurd_8 _void_9 = match _void_9 with _ -> assert false

type (_, _) effect += Effect_DivisionByZero : (unit, unit) effect

type (_, _) effect += Effect_InvalidArgument : (string, unit) effect

type (_, _) effect += Effect_Failure : (string, unit) effect

let _failwith_10 _msg_11 =
  call Effect_Failure _msg_11 (fun _result_3 -> value (_absurd_8 _result_3))

type (_, _) effect += Effect_AssertionFault : (unit, unit) effect

let _var_13 (* ~- *) = ( ~- )

let _var_14 (* + *) = ( + )

let _var_15 (* * *) = ( * )

let _var_16 (* - *) = ( - )

let _mod_17 = ( mod )

let _mod_18 _m_19 _n_20 =
  match _n_20 with
  | 0 ->
      call Effect_DivisionByZero () (fun _result_6 ->
          value (_absurd_8 _result_6))
  | _n_22 -> value (_m_19 mod _n_22)

let _var_24 (* ~-. *) = ( ~-. )

let _var_25 (* +. *) = ( +. )

let _var_26 (* *. *) = ( *. )

let _var_27 (* -. *) = ( -. )

let _var_28 (* /. *) = ( /. )

let _var_29 (* / *) = ( / )

let _var_30 (* ** *) = ( ** )

let _var_31 (* / *) _m_32 _n_33 =
  match _n_33 with
  | 0 ->
      call Effect_DivisionByZero () (fun _result_9 ->
          value (_absurd_8 _result_9))
  | _n_35 -> value (_m_32 / _n_35)

let _float_of_int_37 = float_of_int

let _var_38 (* ^ *) = ( ^ )

let _string_length_39 = string_length

let _to_string_40 = to_string

type 't9 option = None | Some of 't9

let rec _assoc_41 _x_42 _gen_function_43 =
  match _gen_function_43 with
  | [] -> None
  | (_y_44, _z_45) :: _lst_46 ->
      if _x_42 = _y_44 then Some _z_45 else _assoc_41 _x_42 _lst_46

let _not_50 _x_51 = if _x_51 then false else true

let rec _range_52 _m_53 _n_54 =
  if _m_53 > _n_54 then [] else _m_53 :: _range_52 (_m_53 + 1) _n_54

let rec _map_62 _f_63 _gen_function_64 =
  match _gen_function_64 with
  | [] -> value []
  | _x_65 :: _xs_66 ->
      _f_63 _x_65 >> fun _y_67 ->
      _map_62 _f_63 _xs_66 >> fun _ys_68 -> value (_y_67 :: _ys_68)

let _ignore_70 _ = ()

let _take_71 _f_72 _k_73 = _map_62 _f_72 (_range_52 0 _k_73)

let rec _fold_left_77 _f_78 _a_79 _gen_function_80 =
  match _gen_function_80 with
  | [] -> value _a_79
  | _y_81 :: _ys_82 ->
      _f_78 _a_79 >> fun _gen_bind_84 ->
      _gen_bind_84 _y_81 >> fun _a_83 -> _fold_left_77 _f_78 _a_83 _ys_82

let rec _fold_right_87 _f_88 _xs_89 _a_90 =
  match _xs_89 with
  | [] -> value _a_90
  | _x_91 :: _xs_92 ->
      _fold_right_87 _f_88 _xs_92 _a_90 >> fun _a_93 ->
      _f_88 _x_91 >> fun _gen_bind_96 -> _gen_bind_96 _a_93

let rec _iter_97 _f_98 _gen_function_99 =
  match _gen_function_99 with
  | [] -> value ()
  | _x_100 :: _xs_101 -> _f_98 _x_100 >> fun _ -> _iter_97 _f_98 _xs_101

let rec _forall_103 _p_104 _gen_function_105 =
  match _gen_function_105 with
  | [] -> value true
  | _x_106 :: _xs_107 ->
      _p_104 _x_106 >> fun _gen_bind_108 ->
      if _gen_bind_108 then _forall_103 _p_104 _xs_107 else value false

let rec _exists_110 _p_111 _gen_function_112 =
  match _gen_function_112 with
  | [] -> value false
  | _x_113 :: _xs_114 ->
      _p_111 _x_113 >> fun _gen_bind_115 ->
      if _gen_bind_115 then value true else _exists_110 _p_111 _xs_114

let _mem_117 _x_118 =
  _exists_110 (fun (* both *) _lift_fun_82 ->
      value ((fun _x'_119 -> _x_118 = _x'_119) _lift_fun_82))

let rec _filter_121 _p_122 _gen_function_123 =
  match _gen_function_123 with
  | [] -> value []
  | _x_124 :: _xs_125 ->
      _p_122 _x_124 >> fun _gen_bind_126 ->
      if _gen_bind_126 then
        _filter_121 _p_122 _xs_125 >> fun _gen_bind_127 ->
        value (_x_124 :: _gen_bind_127)
      else _filter_121 _p_122 _xs_125

let rec _zip_130 _xs_131 _ys_132 =
  match (_xs_131, _ys_132) with
  | [], [] -> value []
  | _x_133 :: _xs_134, _y_135 :: _ys_136 ->
      _zip_130 _xs_134 _ys_136 >> fun _gen_bind_137 ->
      value ((_x_133, _y_135) :: _gen_bind_137)
  | _, _ ->
      call Effect_InvalidArgument "zip: length mismatch" (fun _result_12 ->
          value (_absurd_8 _result_12))

let _reverse_140 _lst_141 =
  let rec _reverse_acc_142 _acc_143 _gen_function_144 =
    match _gen_function_144 with
    | [] -> _acc_143
    | _x_145 :: _xs_146 -> _reverse_acc_142 (_x_145 :: _acc_143) _xs_146
  in
  _reverse_acc_142 [] _lst_141

let rec _var_149 (* @ *) _xs_150 _ys_151 =
  match _xs_150 with
  | [] -> _ys_151
  | _x_152 :: _xs_153 -> _x_152 :: _var_149 (* @ *) _xs_153 _ys_151

let rec _length_156 _gen_let_rec_function_157 =
  match _gen_let_rec_function_157 with
  | [] -> 0
  | _x_158 :: _xs_159 -> _length_156 _xs_159 + 1

let _head_162 _gen_function_163 =
  match _gen_function_163 with
  | [] ->
      call Effect_InvalidArgument "head: empty list" (fun _result_15 ->
          value (_absurd_8 _result_15))
  | _x_165 :: _ -> value _x_165

let _tail_166 _gen_function_167 =
  match _gen_function_167 with
  | [] ->
      call Effect_InvalidArgument "tail: empty list" (fun _result_18 ->
          value (_absurd_8 _result_18))
  | _x_169 :: _xs_170 -> value _xs_170

let _hd_171 = _head_162

let _tl_172 = _tail_166

let _abs_173 _x_174 = if _x_174 < 0 then ~-_x_174 else _x_174

let _min_177 _x_178 _y_179 = if _x_178 < _y_179 then _x_178 else _y_179

let _max_182 _x_183 _y_184 = if _x_183 < _y_184 then _y_184 else _x_183

let _odd_187 _x_188 =
  _mod_18 _x_188 2 >> fun _gen_bind_190 -> value (_gen_bind_190 = 1)

let _even_192 _x_193 =
  _mod_18 _x_193 2 >> fun _gen_bind_195 -> value (_gen_bind_195 = 0)

let _id_197 _x_198 = _x_198

let _compose_199 _f_200 _g_201 _x_202 =
  _g_201 _x_202 >> fun _gen_bind_203 -> _f_200 _gen_bind_203

let _fst_204 (_x_205, _) = _x_205

let _snd_206 (_, _y_207) = _y_207

let _print_208 _v_209 =
  call Effect_Print (_to_string_40 _v_209) (fun _result_20 -> value _result_20)

let _print_string_211 _str_212 =
  call Effect_Print _str_212 (fun _result_22 -> value _result_22)

let _print_endline_213 _v_214 =
  call Effect_Print (_to_string_40 _v_214) (fun _result_27 ->
      call Effect_Print "\n" (fun _result_24 -> value _result_24))

type (_, _) effect += Effect_Lookup : (unit, int) effect

type (_, _) effect += Effect_Update : (int, unit) effect

;;
"End of pervasives"

type (_, _) effect += Effect_Fetch : (unit, int) effect

let rec _range_216 _n_217 =
  match _n_217 with
  | 0 -> value []
  | _ ->
      let _n1_218 = _n_217 - 1 in
      call Effect_Fetch () (fun _result_30 ->
          _range_216 _n1_218 >> fun _gen_bind_221 ->
          value (_result_30 :: _gen_bind_221))

let _test_222 _n_223 =
  let rec _range_31 _n_217 =
    match _n_217 with
    | 0 -> []
    | _ ->
        let rec _new_special_var_50 (_n_217, _k_val_49) =
          match _n_217 with
          | 0 -> _k_val_49 []
          | _ ->
              _new_special_var_50
                ( _n_217 - 1,
                  (* both *)
                  fun _lift_fun_83 ->
                    (fun _gen_bind_79 -> _k_val_49 (42 :: _gen_bind_79))
                      _lift_fun_83 )
        in
        _new_special_var_50 (_n_217 - 1, fun _gen_bind_47 -> 42 :: _gen_bind_47)
  in
  _range_31 _n_223
