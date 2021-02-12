open OcamlHeader

type (_, _) effect += Decide : (unit, bool) effect

type (_, _) effect += Fail : (unit, empty) effect

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

let _no_attack_70 (_q1_71 : queen) (_q2_72 : queen) =
  match _q1_71 with
  | Queen (_x_73, _y_74) -> (
      match _q2_72 with
      | Queen (_x'_75, _y'_76) -> (
          match _op_61 (* <> *) _x_73 _x'_75 with
          | true -> (
              match _op_61 (* <> *) _y_74 _y'_76 with
              | true ->
                  _op_61 (* <> *)
                    (_abs_66 (_x_73 - _x'_75))
                    (_abs_66 (_y_74 - _y'_76))
              | false -> false
              | false -> false)))

let no_attack = _no_attack_70

let rec _not_attacked_88 _x_96 (_qs_98 : solution) =
  match _qs_98 with
  | SolutionEmpty -> true
  | SolutionPlace (_x_100, _xs_99) -> (
      match _no_attack_70 _x_96 _x_100 with
      | true -> _not_attacked_88 _x_96 _xs_99
      | false -> false)

let not_attacked = _not_attacked_88

let _available_104 (_number_of_queens_105 : int) (_x_106 : int)
    (_qs_107 : solution) =
  let rec _loop_108 _x_119 =
    let _possible_109, _y_110 = _x_119 in
    match _y_110 < 1 with
    | true -> _possible_109
    | false -> (
        match _not_attacked_88 (Queen (_x_106, _y_110)) _qs_107 with
        | true -> _loop_108 (RowsCons (_y_110, _possible_109), _y_110 - 1)
        | false -> _loop_108 (_possible_109, _y_110 - 1))
  in
  _loop_108 (RowsEmpty, _number_of_queens_105)

let available = _available_104

let rec _tr_choose_130 _x_140 =
  match _x_140 with
  | RowsEmpty ->
      Call
        ( Fail,
          (),
          fun (_y_148 : empty) -> Value (match _y_148 with _ -> assert false) )
  | RowsCons (_x_150, _xs'_149) ->
      Call
        ( Decide,
          (),
          fun (_y_151 : bool) ->
            match _y_151 with
            | true -> Value _x_150
            | false -> _tr_choose_130 _xs'_149 )

let tr_choose = _tr_choose_130

let _queens_152 (_number_of_queens_153 : int) =
  let rec _tr_place_154 _x_165 =
    let _x_155, _qs_156 = _x_165 in
    match _op_57 (* > *) _x_155 _number_of_queens_153 with
    | true -> Value _qs_156
    | false ->
        _tr_choose_130 (_available_104 _number_of_queens_153 _x_155 _qs_156)
        >> fun _y_159 ->
        _tr_place_154
          (_x_155 + 1, SolutionPlace (Queen (_x_155, _y_159), _qs_156))
  in
  _tr_place_154 (1, SolutionEmpty)

let queens = _queens_152

let _queens_one_option_176 (_number_of_queens_177 : int) =
  let rec _queens_190 _number_of_queens_153 =
    let rec _tr_place_154 _x_165 =
      let _x_155, _qs_156 = _x_165 in
      match _op_57 (* > *) _x_155 _number_of_queens_153 with
      | true -> Value _qs_156
      | false ->
          _tr_choose_130 (_available_104 _number_of_queens_153 _x_155 _qs_156)
          >> fun _y_159 ->
          _tr_place_154
            (_x_155 + 1, SolutionPlace (Queen (_x_155, _y_159), _qs_156))
    in
    let rec _tr_place_201 _x_165 =
      let _x_155, _qs_156 = _x_165 in
      match _op_57 (* > *) _x_155 _number_of_queens_153 with
      | true -> Some _qs_156
      | false ->
          let rec _tr_choose_203 _x_140 =
            match _x_140 with
            | RowsEmpty -> None
            | RowsCons (_x_150, _xs'_149) -> (
                let _l_186 (_y_151 : bool) =
                  match _y_151 with
                  | true ->
                      _tr_place_201
                        ( _x_155 + 1,
                          SolutionPlace (Queen (_x_155, _x_150), _qs_156) )
                  | false -> _tr_choose_203 _xs'_149
                in
                match _l_186 true with
                | Some _x_181 -> Some _x_181
                | None -> _l_186 false)
          in
          _tr_choose_203 (_available_104 _number_of_queens_153 _x_155 _qs_156)
    in
    _tr_place_201 (1, SolutionEmpty)
  in
  _queens_190 _number_of_queens_177

let queens_one_option = _queens_one_option_176

let _queens_all_224 (_number_of_queens_225 : int) =
  let rec _queens_239 _number_of_queens_153 =
    let rec _tr_place_154 _x_165 =
      let _x_155, _qs_156 = _x_165 in
      match _op_57 (* > *) _x_155 _number_of_queens_153 with
      | true -> Value _qs_156
      | false ->
          _tr_choose_130 (_available_104 _number_of_queens_153 _x_155 _qs_156)
          >> fun _y_159 ->
          _tr_place_154
            (_x_155 + 1, SolutionPlace (Queen (_x_155, _y_159), _qs_156))
    in
    let rec _tr_place_250 _x_165 =
      let _x_155, _qs_156 = _x_165 in
      match _op_57 (* > *) _x_155 _number_of_queens_153 with
      | true -> SolutionsCons (_qs_156, SolutionsNil)
      | false ->
          let rec _tr_choose_252 _x_140 =
            match _x_140 with
            | RowsEmpty -> SolutionsNil
            | RowsCons (_x_150, _xs'_149) ->
                let _l_235 (_y_151 : bool) =
                  match _y_151 with
                  | true ->
                      _tr_place_250
                        ( _x_155 + 1,
                          SolutionPlace (Queen (_x_155, _x_150), _qs_156) )
                  | false -> _tr_choose_252 _xs'_149
                in
                _op_43 (* @ *) (_l_235 true) (_l_235 false)
          in
          _tr_choose_252 (_available_104 _number_of_queens_153 _x_155 _qs_156)
    in
    _tr_place_250 (1, SolutionEmpty)
  in
  _queens_239 _number_of_queens_225

let queens_all = _queens_all_224

let _queens_one_cps_274 (_number_of_queens_275 : int) =
  (let rec _queens_340 _number_of_queens_341 =
     let rec _tr_place_342 _x_343 =
       let _x_345, _qs_344 = _x_343 in
       match _op_57 (* > *) _x_345 _number_of_queens_341 with
       | true -> Value _qs_344
       | false ->
           _tr_choose_130 (_available_104 _number_of_queens_341 _x_345 _qs_344)
           >> fun _y_351 ->
           _tr_place_342
             (_x_345 + 1, SolutionPlace (Queen (_x_345, _y_351), _qs_344))
     in
     let rec _tr_place_354 _x_355 =
       let _x_357, _qs_356 = _x_355 in
       match _op_57 (* > *) _x_357 _number_of_queens_341 with
       | true ->
           coer_arrow coer_refl_ty (coer_return coer_refl_ty)
             (fun (_ : unit -> solution computation) -> _qs_356)
       | false ->
           let rec _tr_choose_363 _x_364 =
             match _x_364 with
             | RowsEmpty ->
                 fun (_kf_365 : unit -> solution computation) -> _kf_365 ()
             | RowsCons (_x_367, _xs'_366) ->
                 let _l_368 (_y_372 : bool) =
                   match _y_372 with
                   | true ->
                       _tr_place_354
                         ( _x_357 + 1,
                           SolutionPlace (Queen (_x_357, _x_367), _qs_356) )
                   | false -> _tr_choose_363 _xs'_366
                 in
                 fun (_kf_369 : unit -> solution computation) ->
                   _l_368 true (fun (_ : unit) -> _l_368 false _kf_369)
           in
           _tr_choose_363 (_available_104 _number_of_queens_341 _x_357 _qs_356)
     in
     _tr_place_354 (1, SolutionEmpty)
   in
   _queens_340 _number_of_queens_275) (fun (() : unit) ->
      Call
        ( Fail,
          (),
          fun (_y_339 : empty) -> Value (match _y_339 with _ -> assert false) ))

let queens_one_cps = _queens_one_cps_274
