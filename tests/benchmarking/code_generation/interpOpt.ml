open OcamlHeader

type term =
  | Num of int
  | Add of (term * term)
  | Mul of (term * term)
  | Sub of (term * term)
  | Div of (term * term)

type (_, _) eff_internal_effect += DivByZero : (unit, int) eff_internal_effect

let _addCase_42 =
  Add
    ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
      Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )

let addCase = _addCase_42

let rec _createZeroCase_43 _x_52 =
  match _x_52 with
  | 0 -> Sub (_addCase_42, _addCase_42)
  | _n_54 -> Sub (_createZeroCase_43 (_n_54 - 1), _createZeroCase_43 (_n_54 - 1))

let createZeroCase = _createZeroCase_43

let rec _createCase_61 _x_67 =
  match _x_67 with
  | 1 -> Div (Num 100, _createZeroCase_43 3)
  | _ -> Add (_addCase_42, _createCase_61 (_x_67 - 1))

let createCase = _createCase_61

let _bigTest_73 (_num_74 : int) =
  let rec _interp_75 _x_105 =
    match _x_105 with
    | Num _b_111 -> Value _b_111
    | Add (_l_113, _r_112) ->
        _interp_75 _l_113 >> fun _x_114 ->
        _interp_75 _r_112 >> fun _y_115 -> Value (_x_114 + _y_115)
    | Mul (_l_118, _r_117) ->
        _interp_75 _l_118 >> fun _x_119 ->
        _interp_75 _r_117 >> fun _y_120 -> Value (_x_119 * _y_120)
    | Sub (_l_123, _r_122) ->
        _interp_75 _l_123 >> fun _x_124 ->
        _interp_75 _r_122 >> fun _y_125 -> Value (_x_124 - _y_125)
    | Div (_l_128, _r_127) -> (
        _interp_75 _r_127 >> fun _y_129 ->
        _interp_75 _l_128 >> fun _x_130 ->
        match _y_129 with
        | 0 -> Call (DivByZero, (), fun (_y_131 : int) -> Value _y_131)
        | _ -> Value (_x_130 / _y_129))
  in
  let rec _interp_135 (_x_105, _k_137) =
    match _x_105 with
    | Num _b_111 -> _k_137 _b_111
    | Add (_l_113, _r_112) ->
        _interp_135
          ( _l_113,
            fun (_x_114 : int) ->
              _interp_135
                (_r_112, fun (_y_115 : int) -> _k_137 (_x_114 + _y_115)) )
    | Mul (_l_118, _r_117) ->
        _interp_135
          ( _l_118,
            fun (_x_119 : int) ->
              _interp_135
                (_r_117, fun (_y_120 : int) -> _k_137 (_x_119 * _y_120)) )
    | Sub (_l_123, _r_122) ->
        _interp_135
          ( _l_123,
            fun (_x_124 : int) ->
              _interp_135
                (_r_122, fun (_y_125 : int) -> _k_137 (_x_124 - _y_125)) )
    | Div (_l_128, _r_127) ->
        _interp_135
          ( _r_127,
            fun (_y_129 : int) ->
              _interp_135
                ( _l_128,
                  fun (_x_130 : int) ->
                    match _y_129 with 0 -> ~-1 | _ -> _k_137 (_x_130 / _y_129)
                ) )
  in
  _interp_135 (_createCase_61 _num_74, fun (_id_101 : int) -> _id_101)

let bigTest = _bigTest_73

type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect

let _testState_140 (_n_141 : int) =
  let rec _interp_142 _x_183 =
    match _x_183 with
    | Num _b_195 ->
        Call (Set, _b_195 * _b_195, fun (_y_198 : unit) -> Value _b_195)
    | Add (_l_200, _r_199) ->
        _interp_142 _l_200 >> fun _x_201 ->
        _interp_142 _r_199 >> fun _y_202 -> Value (_x_201 + _y_202)
    | Mul (_l_205, _r_204) ->
        _interp_142 _l_205 >> fun _x_206 ->
        _interp_142 _r_204 >> fun _y_207 -> Value (_x_206 * _y_207)
    | Sub (_l_210, _r_209) ->
        _interp_142 _l_210 >> fun _x_211 ->
        _interp_142 _r_209 >> fun _y_212 -> Value (_x_211 - _y_212)
    | Div (_l_215, _r_214) -> (
        _interp_142 _r_214 >> fun _y_216 ->
        _interp_142 _l_215 >> fun _x_217 ->
        match _y_216 with
        | 0 -> Call (Get, (), fun (_y_218 : int) -> Value _y_218)
        | _ -> Value (_x_217 / _y_216))
  in
  (let rec _interp_225 (_x_183, _k_227) =
     match _x_183 with
     | Num _b_195 -> fun (_ : int) -> _k_227 _b_195 (_b_195 * _b_195)
     | Add (_l_200, _r_199) ->
         _interp_225
           ( _l_200,
             fun (_x_201 : int) ->
               _interp_225
                 (_r_199, fun (_y_202 : int) -> _k_227 (_x_201 + _y_202)) )
     | Mul (_l_205, _r_204) ->
         _interp_225
           ( _l_205,
             fun (_x_206 : int) ->
               _interp_225
                 (_r_204, fun (_y_207 : int) -> _k_227 (_x_206 * _y_207)) )
     | Sub (_l_210, _r_209) ->
         _interp_225
           ( _l_210,
             fun (_x_211 : int) ->
               _interp_225
                 (_r_209, fun (_y_212 : int) -> _k_227 (_x_211 - _y_212)) )
     | Div (_l_215, _r_214) ->
         _interp_225
           ( _r_214,
             fun (_y_216 : int) ->
               _interp_225
                 ( _l_215,
                   fun (_x_217 : int) ->
                     force_unsafe
                       ((handler
                           {
                             value_clause =
                               (fun (_x_226 : int) -> Value (_k_227 _x_226));
                             effect_clauses =
                               (fun (type a b)
                                    (eff : (a, b) eff_internal_effect) :
                                    (a -> (b -> _) -> _) ->
                                 match eff with
                                 | Get ->
                                     fun () _l_184 ->
                                       Value
                                         (fun (_s_169 : int) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_184 _s_169 _s_169)
                                 | Set ->
                                     fun _s_171 _l_185 ->
                                       Value
                                         (fun (_ : int) ->
                                           coer_arrow coer_refl_ty force_unsafe
                                             _l_185 () _s_171)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (match _y_216 with
                          | 0 ->
                              Call (Get, (), fun (_y_218 : int) -> Value _y_218)
                          | _ -> Value (_x_217 / _y_216))) ) )
   in
   _interp_225 (_createCase_61 _n_141, fun (_x_174 : int) (_ : int) -> _x_174))
    _n_141

let testState = _testState_140
