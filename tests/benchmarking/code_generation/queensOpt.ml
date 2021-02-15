open OcamlHeader

type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

type queen = Queen of (int * int)

type rows = RowsEmpty | RowsCons of (int * rows)

type solution = SolutionEmpty | SolutionPlace of (queen * solution)

type solutions = SolutionsNil | SolutionsCons of (solution * solutions)

type optional_solution = None | Some of solution

type void = Void

let _absurd_41 (_void_42 : float) = match _void_42 with _ -> assert false

let absurd = _absurd_41

let rec _op_43 (* @ *) _x_50 (_ys_52 : solutions) =
  match _x_50 with
  | SolutionsNil -> _ys_52
  | SolutionsCons (_x_54, _xs_53) ->
      SolutionsCons (_x_54, _op_43 (* @ *) _xs_53 _ys_52)

let _op_43 (* @ *) = _op_43 (* @ *)

let _op_57 (* > *) (_x_58 : int) (_y_59 : int) = _y_59 < _x_58

let _op_57 (* > *) = _op_57 (* > *)

let _op_61 (* <> *) (_x_62 : int) (_y_63 : int) =
  match _y_63 = _x_62 with true -> false | false -> true

let _op_61 (* <> *) = _op_61 (* <> *)

let _abs_66 (_x_67 : int) =
  match _x_67 < 0 with true -> ~-_x_67 | false -> _x_67

let abs = _abs_66

let _no_attack_70 (Queen (_x_71, _y_72) : queen)
    (Queen (_x'_73, _y'_74) : queen) =
  match _op_61 (* <> *) _x_71 _x'_73 with
  | true -> (
      match _op_61 (* <> *) _y_72 _y'_74 with
      | true ->
          _op_61 (* <> *) (_abs_66 (_x_71 - _x'_73)) (_abs_66 (_y_72 - _y'_74))
      | false -> false)
  | false -> false

let no_attack = _no_attack_70

let rec _not_attacked_86 _x_94 (_qs_96 : solution) =
  match _qs_96 with
  | SolutionEmpty -> true
  | SolutionPlace (_x_98, _xs_97) -> (
      match _no_attack_70 _x_94 _x_98 with
      | true -> _not_attacked_86 _x_94 _xs_97
      | false -> false)

let not_attacked = _not_attacked_86

let _available_102 (_number_of_queens_103 : int) (_x_104 : int)
    (_qs_105 : solution) =
  let rec _loop_106 _x_117 =
    let _possible_107, _y_108 = _x_117 in
    match _y_108 < 1 with
    | true -> _possible_107
    | false -> (
        match _not_attacked_86 (Queen (_x_104, _y_108)) _qs_105 with
        | true -> _loop_106 (RowsCons (_y_108, _possible_107), _y_108 - 1)
        | false -> _loop_106 (_possible_107, _y_108 - 1))
  in
  _loop_106 (RowsEmpty, _number_of_queens_103)

let available = _available_102

let rec _tr_choose_128 _x_138 =
  match _x_138 with
  | RowsEmpty ->
      Call
        ( Fail,
          (),
          fun (_y_146 : empty) -> Value (match _y_146 with _ -> assert false) )
  | RowsCons (_x_148, _xs'_147) ->
      Call
        ( Decide,
          (),
          fun (_y_149 : bool) ->
            match _y_149 with
            | true -> Value _x_148
            | false -> _tr_choose_128 _xs'_147 )

let tr_choose = _tr_choose_128

let _queens_150 (_number_of_queens_151 : int) =
  let rec _tr_place_152 _x_163 =
    let _x_153, _qs_154 = _x_163 in
    match _op_57 (* > *) _x_153 _number_of_queens_151 with
    | true -> Value _qs_154
    | false ->
        _tr_choose_128 (_available_102 _number_of_queens_151 _x_153 _qs_154)
        >> fun _y_157 ->
        _tr_place_152
          (_x_153 + 1, SolutionPlace (Queen (_x_153, _y_157), _qs_154))
  in
  _tr_place_152 (1, SolutionEmpty)

let queens = _queens_150

let _queens_one_option_174 (_number_of_queens_175 : int) =
  let rec _queens_188 _number_of_queens_151 =
    let rec _tr_place_152 _x_163 =
      let _x_153, _qs_154 = _x_163 in
      match _op_57 (* > *) _x_153 _number_of_queens_151 with
      | true -> Value _qs_154
      | false ->
          _tr_choose_128 (_available_102 _number_of_queens_151 _x_153 _qs_154)
          >> fun _y_157 ->
          _tr_place_152
            (_x_153 + 1, SolutionPlace (Queen (_x_153, _y_157), _qs_154))
    in
    let rec _tr_place_199 _x_163 =
      let _x_153, _qs_154 = _x_163 in
      match _op_57 (* > *) _x_153 _number_of_queens_151 with
      | true -> Some _qs_154
      | false ->
          let rec _tr_choose_201 _x_138 =
            match _x_138 with
            | RowsEmpty -> None
            | RowsCons (_x_148, _xs'_147) -> (
                let _l_184 (_y_149 : bool) =
                  match _y_149 with
                  | true ->
                      _tr_place_199
                        ( _x_153 + 1,
                          SolutionPlace (Queen (_x_153, _x_148), _qs_154) )
                  | false -> _tr_choose_201 _xs'_147
                in
                match _l_184 true with
                | Some _x_179 -> Some _x_179
                | None -> _l_184 false)
          in
          _tr_choose_201 (_available_102 _number_of_queens_151 _x_153 _qs_154)
    in
    _tr_place_199 (1, SolutionEmpty)
  in
  _queens_188 _number_of_queens_175

let queens_one_option = _queens_one_option_174

let _queens_all_222 (_number_of_queens_223 : int) =
  let rec _queens_237 _number_of_queens_151 =
    let rec _tr_place_152 _x_163 =
      let _x_153, _qs_154 = _x_163 in
      match _op_57 (* > *) _x_153 _number_of_queens_151 with
      | true -> Value _qs_154
      | false ->
          _tr_choose_128 (_available_102 _number_of_queens_151 _x_153 _qs_154)
          >> fun _y_157 ->
          _tr_place_152
            (_x_153 + 1, SolutionPlace (Queen (_x_153, _y_157), _qs_154))
    in
    let rec _tr_place_248 _x_163 =
      let _x_153, _qs_154 = _x_163 in
      match _op_57 (* > *) _x_153 _number_of_queens_151 with
      | true -> SolutionsCons (_qs_154, SolutionsNil)
      | false ->
          let rec _tr_choose_250 _x_138 =
            match _x_138 with
            | RowsEmpty -> SolutionsNil
            | RowsCons (_x_148, _xs'_147) ->
                let _l_233 (_y_149 : bool) =
                  match _y_149 with
                  | true ->
                      _tr_place_248
                        ( _x_153 + 1,
                          SolutionPlace (Queen (_x_153, _x_148), _qs_154) )
                  | false -> _tr_choose_250 _xs'_147
                in
                _op_43 (* @ *) (_l_233 true) (_l_233 false)
          in
          _tr_choose_250 (_available_102 _number_of_queens_151 _x_153 _qs_154)
    in
    _tr_place_248 (1, SolutionEmpty)
  in
  _queens_237 _number_of_queens_223

let queens_all = _queens_all_222

let _queens_one_cps_272 (_number_of_queens_273 : int) =
  (let rec _queens_338 _number_of_queens_339 =
     let rec _tr_place_340 _x_341 =
       let _x_343, _qs_342 = _x_341 in
       match _op_57 (* > *) _x_343 _number_of_queens_339 with
       | true -> Value _qs_342
       | false ->
           _tr_choose_128 (_available_102 _number_of_queens_339 _x_343 _qs_342)
           >> fun _y_349 ->
           _tr_place_340
             (_x_343 + 1, SolutionPlace (Queen (_x_343, _y_349), _qs_342))
     in
     let rec _tr_place_352 _x_353 =
       let _x_355, _qs_354 = _x_353 in
       match _op_57 (* > *) _x_355 _number_of_queens_339 with
       | true ->
           coer_arrow coer_refl_ty (coer_return coer_refl_ty)
             (fun (_ : unit -> solution computation) -> _qs_354)
       | false ->
           let rec _tr_choose_361 _x_362 =
             match _x_362 with
             | RowsEmpty ->
                 fun (_kf_363 : unit -> solution computation) -> _kf_363 ()
             | RowsCons (_x_365, _xs'_364) ->
                 let _l_366 (_y_370 : bool) =
                   match _y_370 with
                   | true ->
                       _tr_place_352
                         ( _x_355 + 1,
                           SolutionPlace (Queen (_x_355, _x_365), _qs_354) )
                   | false -> _tr_choose_361 _xs'_364
                 in
                 fun (_kf_367 : unit -> solution computation) ->
                   _l_366 true (fun (_ : unit) -> _l_366 false _kf_367)
           in
           _tr_choose_361 (_available_102 _number_of_queens_339 _x_355 _qs_354)
     in
     _tr_place_352 (1, SolutionEmpty)
   in
   _queens_338 _number_of_queens_273) (fun (() : unit) ->
      Call
        ( Fail,
          (),
          fun (_y_337 : empty) -> Value (match _y_337 with _ -> assert false) ))

let queens_one_cps = _queens_one_cps_272
