open OcamlHeader

type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

type queen = int * int

type rows = RowsEmpty | RowsCons of (int * rows)

type solution = SolutionEmpty | SolutionPlace of (queen * solution)

type solutions = SolutionsNil | SolutionsCons of (solution * solutions)

type optional_solution = None | Some of solution

type void = Void

let _absurd_45 (_void_46 : float) = match _void_46 with _ -> assert false

let absurd = _absurd_45

let rec _op_47 (* @ *) _x_54 (_ys_56 : solutions) =
  match _x_54 with
  | SolutionsNil -> _ys_56
  | SolutionsCons (_x_58, _xs_57) ->
      SolutionsCons (_x_58, _op_47 (* @ *) _xs_57 _ys_56)

let _op_47 (* @ *) = _op_47 (* @ *)

let _no_attack_61 ((_x_62, _y_63) : int * int) ((_x'_64, _y'_65) : int * int) =
  _x_62 <> _x'_64 && _y_63 <> _y'_65
  && abs (_x_62 - _x'_64) <> abs (_y_63 - _y'_65)

let no_attack = _no_attack_61

let rec _not_attacked_77 _x_85 (_qs_87 : solution) =
  match _qs_87 with
  | SolutionEmpty -> true
  | SolutionPlace (_x_89, _xs_88) ->
      _no_attack_61 _x_85 _x_89 && _not_attacked_77 _x_85 _xs_88

let not_attacked = _not_attacked_77

let _available_93 (_number_of_queens_94 : int) (_x_95 : int) (_qs_96 : solution)
    =
  let rec _loop_97 (_possible_98, _y_99) =
    match _y_99 < 1 with
    | true -> _possible_98
    | false -> (
        match _not_attacked_77 (_x_95, _y_99) _qs_96 with
        | true -> _loop_97 (RowsCons (_y_99, _possible_98), _y_99 - 1)
        | false -> _loop_97 (_possible_98, _y_99 - 1))
  in
  _loop_97 (RowsEmpty, _number_of_queens_94)

let available = _available_93

let rec _tr_choose_119 _x_129 =
  match _x_129 with
  | RowsEmpty ->
      Call
        ( Fail,
          (),
          fun (_y_137 : empty) -> Value (match _y_137 with _ -> assert false) )
  | RowsCons (_x_139, _xs'_138) ->
      Call
        ( Decide,
          (),
          fun (_y_140 : bool) ->
            match _y_140 with
            | true -> Value _x_139
            | false -> _tr_choose_119 _xs'_138 )

let tr_choose = _tr_choose_119

let _queens_141 (_number_of_queens_142 : int) =
  let rec _tr_place_143 (_x_144, _qs_145) =
    match _x_144 > _number_of_queens_142 with
    | true -> Value _qs_145
    | false ->
        _tr_choose_119 (_available_93 _number_of_queens_142 _x_144 _qs_145)
        >> fun _y_148 ->
        _tr_place_143 (_x_144 + 1, SolutionPlace ((_x_144, _y_148), _qs_145))
  in
  _tr_place_143 (1, SolutionEmpty)

let queens = _queens_141

let _queens_one_option_165 (_number_of_queens_166 : int) =
  let rec _queens_179 _number_of_queens_142 =
    let rec _tr_place_143 (_x_144, _qs_145) =
      match _x_144 > _number_of_queens_142 with
      | true -> Value _qs_145
      | false ->
          _tr_choose_119 (_available_93 _number_of_queens_142 _x_144 _qs_145)
          >> fun _y_148 ->
          _tr_place_143 (_x_144 + 1, SolutionPlace ((_x_144, _y_148), _qs_145))
    in
    let rec _tr_place_190 (_x_144, _qs_145) =
      match _x_144 > _number_of_queens_142 with
      | true -> Some _qs_145
      | false ->
          let rec _tr_choose_192 _x_129 =
            match _x_129 with
            | RowsEmpty -> None
            | RowsCons (_x_139, _xs'_138) -> (
                let _l_175 (_y_140 : bool) =
                  match _y_140 with
                  | true ->
                      _tr_place_190
                        (_x_144 + 1, SolutionPlace ((_x_144, _x_139), _qs_145))
                  | false -> _tr_choose_192 _xs'_138
                in
                match _l_175 true with
                | Some _x_170 -> Some _x_170
                | None -> _l_175 false)
          in
          _tr_choose_192 (_available_93 _number_of_queens_142 _x_144 _qs_145)
    in
    _tr_place_190 (1, SolutionEmpty)
  in
  _queens_179 _number_of_queens_166

let queens_one_option = _queens_one_option_165

let _queens_all_213 (_number_of_queens_214 : int) =
  let rec _queens_228 _number_of_queens_142 =
    let rec _tr_place_143 (_x_144, _qs_145) =
      match _x_144 > _number_of_queens_142 with
      | true -> Value _qs_145
      | false ->
          _tr_choose_119 (_available_93 _number_of_queens_142 _x_144 _qs_145)
          >> fun _y_148 ->
          _tr_place_143 (_x_144 + 1, SolutionPlace ((_x_144, _y_148), _qs_145))
    in
    let rec _tr_place_239 (_x_144, _qs_145) =
      match _x_144 > _number_of_queens_142 with
      | true -> SolutionsCons (_qs_145, SolutionsNil)
      | false ->
          let rec _tr_choose_241 _x_129 =
            match _x_129 with
            | RowsEmpty -> SolutionsNil
            | RowsCons (_x_139, _xs'_138) ->
                let _l_224 (_y_140 : bool) =
                  match _y_140 with
                  | true ->
                      _tr_place_239
                        (_x_144 + 1, SolutionPlace ((_x_144, _x_139), _qs_145))
                  | false -> _tr_choose_241 _xs'_138
                in
                _op_47 (* @ *) (_l_224 true) (_l_224 false)
          in
          _tr_choose_241 (_available_93 _number_of_queens_142 _x_144 _qs_145)
    in
    _tr_place_239 (1, SolutionEmpty)
  in
  _queens_228 _number_of_queens_214

let queens_all = _queens_all_213

let _queens_one_cps_263 (_number_of_queens_264 : int) =
  (let rec _queens_329 _number_of_queens_330 =
     let rec _tr_place_331 (_x_334, _qs_333) =
       match _x_334 > _number_of_queens_330 with
       | true -> Value _qs_333
       | false ->
           _tr_choose_119 (_available_93 _number_of_queens_330 _x_334 _qs_333)
           >> fun _y_340 ->
           _tr_place_331 (_x_334 + 1, SolutionPlace ((_x_334, _y_340), _qs_333))
     in
     let rec _tr_place_343 (_x_346, _qs_345) =
       match _x_346 > _number_of_queens_330 with
       | true ->
           coer_arrow coer_refl_ty (coer_return coer_refl_ty)
             (fun (_ : unit -> solution computation) -> _qs_345)
       | false ->
           let rec _tr_choose_352 _x_353 =
             match _x_353 with
             | RowsEmpty ->
                 fun (_kf_354 : unit -> solution computation) -> _kf_354 ()
             | RowsCons (_x_356, _xs'_355) ->
                 let _l_357 (_y_361 : bool) =
                   match _y_361 with
                   | true ->
                       _tr_place_343
                         (_x_346 + 1, SolutionPlace ((_x_346, _x_356), _qs_345))
                   | false -> _tr_choose_352 _xs'_355
                 in
                 fun (_kf_358 : unit -> solution computation) ->
                   _l_357 true (fun (_ : unit) -> _l_357 false _kf_358)
           in
           _tr_choose_352 (_available_93 _number_of_queens_330 _x_346 _qs_345)
     in
     _tr_place_343 (1, SolutionEmpty)
   in
   _queens_329 _number_of_queens_264) (fun (() : unit) ->
      Call
        ( Fail,
          (),
          fun (_y_328 : empty) -> Value (match _y_328 with _ -> assert false) ))

let queens_one_cps = _queens_one_cps_263
