open OcamlHeader

type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

type queen = int * int

type rows = RowsEmpty | RowsCons of (int * rows)

type solution = SolutionEmpty | SolutionPlace of (queen * solution)

type solutions = SolutionsNil | SolutionsCons of (solution * solutions)

type optional_solution = None | Some of solution

type void = Void

let _absurd_42 (_void_43 : float) = match _void_43 with _ -> assert false

let absurd = _absurd_42

let rec _op_44 (* @ *) _x_51 (_ys_53 : solutions) =
  match _x_51 with
  | SolutionsNil -> _ys_53
  | SolutionsCons (_x_55, _xs_54) ->
      SolutionsCons (_x_55, _op_44 (* @ *) _xs_54 _ys_53)

let _op_44 (* @ *) = _op_44 (* @ *)

let _no_attack_58 ((_x_59, _y_60) : int * int) ((_x'_61, _y'_62) : int * int) =
  _x_59 <> _x'_61 && _y_60 <> _y'_62
  && abs (_x_59 - _x'_61) <> abs (_y_60 - _y'_62)

let no_attack = _no_attack_58

let rec _not_attacked_74 _x_82 (_qs_84 : solution) =
  match _qs_84 with
  | SolutionEmpty -> true
  | SolutionPlace (_x_86, _xs_85) ->
      _no_attack_58 _x_82 _x_86 && _not_attacked_74 _x_82 _xs_85

let not_attacked = _not_attacked_74

let _available_90 (_number_of_queens_91 : int) (_x_92 : int) (_qs_93 : solution)
    =
  let rec _loop_94 (_possible_95, _y_96) =
    if _y_96 < 1 then _possible_95
    else if _not_attacked_74 (_x_92, _y_96) _qs_93 then
      _loop_94 (RowsCons (_y_96, _possible_95), _y_96 - 1)
    else _loop_94 (_possible_95, _y_96 - 1)
  in
  _loop_94 (RowsEmpty, _number_of_queens_91)

let available = _available_90

let rec _choose_116 _x_126 =
  match _x_126 with
  | RowsEmpty ->
      Call (Fail, (), fun (_y_133 : empty) -> Value _y_133) >>= fun _b_132 ->
      Value (match _b_132 with _ -> assert false)
  | RowsCons (_x_135, _xs'_134) ->
      Call (Decide, (), fun (_y_137 : bool) -> Value _y_137) >>= fun _b_136 ->
      if _b_136 then Value _x_135 else _choose_116 _xs'_134

let choose = _choose_116

let _queens_138 (_number_of_queens_139 : int) =
  let rec _place_140 (_x_141, _qs_142) =
    if _x_141 > _number_of_queens_139 then Value _qs_142
    else
      _choose_116 (_available_90 _number_of_queens_139 _x_141 _qs_142)
      >>= fun _y_145 ->
      _place_140 (_x_141 + 1, SolutionPlace ((_x_141, _y_145), _qs_142))
  in
  _place_140 (1, SolutionEmpty)

let queens = _queens_138

let _queens_one_option_162 (_number_of_queens_163 : int) =
  let rec _queens_176 _number_of_queens_139 =
    let rec _place_177 (_x_141, _qs_142) =
      if _x_141 > _number_of_queens_139 then Some _qs_142
      else
        let rec _choose_232 _x_233 =
          match _x_233 with
          | RowsEmpty -> None
          | RowsCons (_x_235, _xs'_234) -> (
              let _l_236 (_y_239 : bool) =
                if _y_239 then
                  _place_177
                    (_x_141 + 1, SolutionPlace ((_x_141, _x_235), _qs_142))
                else _choose_232 _xs'_234
              in
              match _l_236 true with
              | Some _x_238 -> Some _x_238
              | None -> _l_236 false)
        in
        _choose_232 (_available_90 _number_of_queens_139 _x_141 _qs_142)
    in
    _place_177 (1, SolutionEmpty)
  in
  _queens_176 _number_of_queens_163

let queens_one_option = _queens_one_option_162

let _queens_all_242 (_number_of_queens_243 : int) =
  let rec _queens_257 _number_of_queens_139 =
    let rec _place_258 (_x_141, _qs_142) =
      if _x_141 > _number_of_queens_139 then
        SolutionsCons (_qs_142, SolutionsNil)
      else
        let rec _choose_314 _x_315 =
          match _x_315 with
          | RowsEmpty -> SolutionsNil
          | RowsCons (_x_317, _xs'_316) ->
              let _l_318 (_y_322 : bool) =
                if _y_322 then
                  _place_258
                    (_x_141 + 1, SolutionPlace ((_x_141, _x_317), _qs_142))
                else _choose_314 _xs'_316
              in
              _op_44 (* @ *) (_l_318 true) (_l_318 false)
        in
        _choose_314 (_available_90 _number_of_queens_139 _x_141 _qs_142)
    in
    _place_258 (1, SolutionEmpty)
  in
  _queens_257 _number_of_queens_243

let queens_all = _queens_all_242

let _queens_one_cps_325 (_number_of_queens_326 : int) =
  let rec _queens_426 _number_of_queens_427 =
    let rec _place_439 (_x_441, _qs_440) =
      if _x_441 > _number_of_queens_427 then
        coer_arrow coer_refl_ty (coer_return coer_refl_ty)
          (fun (_ : unit -> solution computation) -> _qs_440)
      else
        let rec _choose_447 _x_448 (_x_0 : unit -> solution computation) =
          match _x_448 with
          | RowsEmpty -> _x_0 ()
          | RowsCons (_x_451, _xs'_450) ->
              let _l_452 (_y_456 : bool) =
                if _y_456 then
                  _place_439
                    (_x_441 + 1, SolutionPlace ((_x_441, _x_451), _qs_440))
                else _choose_447 _xs'_450
              in
              _l_452 true (fun (_ : unit) -> _l_452 false _x_0)
        in
        _choose_447 (_available_90 _number_of_queens_427 _x_441 _qs_440)
    in
    _place_439 (1, SolutionEmpty)
  in
  _queens_426 _number_of_queens_326 (fun (() : unit) ->
      Call (Fail, (), fun (_y_425 : empty) -> Value _y_425) >>= fun _b_424 ->
      Value (match _b_424 with _ -> assert false))

let queens_one_cps = _queens_one_cps_325
