open OcamlHeader

type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect

type queen = int * int

type rows = RowsEmpty | RowsCons of (int * rows)

type solution = SolutionEmpty | SolutionPlace of (queen * solution)

type solutions = SolutionsNil | SolutionsCons of (solution * solutions)

type optional_solution = None | Some of solution

type void = Void

let _absurd_42 _void_43 = match _void_43 with _ -> assert false

let absurd = _absurd_42

let rec _op_44 (* @ *) _x_51 (_ys_53 : solutions) =
  match _x_51 with
  | SolutionsNil -> Value _ys_53
  | SolutionsCons (_x_55, _xs_54) ->
      Value (_op_44 (* @ *) _xs_54) >>= fun _b_56 ->
      Value (_b_56 _ys_53) >>= fun _b_57 ->
      Value (SolutionsCons (_x_55, force_unsafe _b_57))

let _op_44 (* @ *) = _op_44 (* @ *)

let _no_attack_58 ((_x_59, _y_60) : int * int) ((_x'_61, _y'_62) : int * int) :
    bool computation =
  Value (( <> ) _x_59) >>= fun _b_64 ->
  Value (_b_64 _x'_61) >>= fun _b_63 ->
  Value
    (_b_63
    && force_unsafe
         ( Value (( <> ) _y_60) >>= fun _b_66 ->
           Value (_b_66 _y'_62) >>= fun _b_65 -> Value _b_65 )
    && force_unsafe
         ( Value (( - ) _x_59) >>= fun _b_70 ->
           Value (_b_70 _x'_61) >>= fun _b_69 ->
           Value (abs _b_69) >>= fun _b_68 ->
           Value (( <> ) _b_68) >>= fun _b_67 ->
           Value (( - ) _y_60) >>= fun _b_73 ->
           Value (_b_73 _y'_62) >>= fun _b_72 ->
           Value (abs _b_72) >>= fun _b_71 -> Value (_b_67 _b_71) ))

let no_attack = _no_attack_58

let rec _not_attacked_74 _x_82 (_qs_84 : solution) : bool computation =
  match _qs_84 with
  | SolutionEmpty -> Value true
  | SolutionPlace (_x_86, _xs_85) ->
      Value (_no_attack_58 _x_82) >>= fun _b_87 ->
      Value (_b_87 _x_86) >>= fun _b_88 ->
      Value
        (force_unsafe _b_88
        && force_unsafe
             (Value (_not_attacked_74 _x_82) >>= fun _b_89 -> _b_89 _xs_85))

let not_attacked = _not_attacked_74

let _available_90 (_number_of_queens_91 : int) (_x_92 : int) (_qs_93 : solution)
    : rows computation =
  let rec _loop_94 (_possible_95, _y_96) =
    Value (( < ) _y_96) >>= fun _b_98 ->
    Value (_b_98 1) >>= fun _b_97 ->
    if _b_97 then Value _possible_95
    else
      Value (_not_attacked_74 (_x_92, _y_96)) >>= fun _b_100 ->
      Value (_b_100 _qs_93) >>= fun _b_99 ->
      if force_unsafe _b_99 then
        Value (( - ) _y_96) >>= fun _b_102 ->
        Value (_b_102 1) >>= fun _b_101 ->
        _loop_94 (RowsCons (_y_96, _possible_95), _b_101)
      else
        Value (( - ) _y_96) >>= fun _b_104 ->
        Value (_b_104 1) >>= fun _b_103 -> _loop_94 (_possible_95, _b_103)
  in
  _loop_94 (RowsEmpty, _number_of_queens_91)

let available = _available_90

let rec _choose_116 _x_126 =
  match _x_126 with
  | RowsEmpty ->
      Call
        ( Fail,
          (),
          fun (_y_134 : empty) -> Value (match _y_134 with _ -> assert false) )
  | RowsCons (_x_136, _xs'_135) ->
      Call
        ( Decide,
          (),
          fun (_y_137 : bool) ->
            if _y_137 then Value _x_136 else _choose_116 _xs'_135 )

let choose = _choose_116

let _queens_138 (_number_of_queens_139 : int) =
  let rec _place_140 (_x_141, _qs_142) =
    Value (( > ) _x_141) >>= fun _b_144 ->
    Value (_b_144 _number_of_queens_139) >>= fun _b_143 ->
    if _b_143 then Value _qs_142
    else
      Value (_available_90 _number_of_queens_139) >>= fun _b_148 ->
      Value (_b_148 _x_141) >>= fun _b_147 ->
      Value (_b_147 _qs_142) >>= fun _b_146 ->
      _choose_116 (force_unsafe _b_146) >>= fun _y_145 ->
      Value (( + ) _x_141) >>= fun _b_150 ->
      Value (_b_150 1) >>= fun _b_149 ->
      _place_140 (_b_149, SolutionPlace ((_x_141, _y_145), _qs_142))
  in
  _place_140 (1, SolutionEmpty)

let queens = _queens_138

let _queens_one_option_162 (_number_of_queens_163 : int) =
  let rec _queens_176 _number_of_queens_139 =
    let rec _place_177 (_x_141, _qs_142) =
      Value (( > ) _x_141) >>= fun _x_238 ->
      Value (_x_238 _number_of_queens_139) >>= fun _x_257 ->
      if _x_257 then Value (Some _qs_142)
      else
        Value (_available_90 _number_of_queens_139) >>= fun _x_258 ->
        Value (_x_258 _x_141) >>= fun _x_259 ->
        Value (_x_259 _qs_142) >>= fun _x_260 ->
        let rec _choose_261 (_x_262 : rows) =
          match _x_262 with
          | RowsEmpty -> Value None
          | RowsCons (_x_264, _xs'_263) -> (
              let _l_265 (_y_268 : bool) : optional_solution computation =
                if _y_268 then
                  Value (( + ) _x_141) >>= fun _x_269 ->
                  Value (_x_269 1) >>= fun _x_270 ->
                  _place_177 (_x_270, SolutionPlace ((_x_141, _x_264), _qs_142))
                else _choose_261 _xs'_263
              in

              _l_265 true >>= fun _b_266 ->
              match _b_266 with
              | Some _x_267 -> Value (Some _x_267)
              | None -> _l_265 false)
        in
        _choose_261 (force_unsafe _x_260)
    in
    _place_177 (1, SolutionEmpty)
  in
  _queens_176 _number_of_queens_163

let queens_one_option = _queens_one_option_162

let _queens_all_271 (_number_of_queens_272 : int) : solutions computation =
  let rec _queens_286 _number_of_queens_139 =
    let rec _place_287 (_x_141, _qs_142) =
      Value (( > ) _x_141) >>= fun _x_351 ->
      Value (_x_351 _number_of_queens_139) >>= fun _x_371 ->
      if _x_371 then Value (SolutionsCons (_qs_142, SolutionsNil))
      else
        Value (_available_90 _number_of_queens_139) >>= fun _x_372 ->
        Value (_x_372 _x_141) >>= fun _x_373 ->
        Value (_x_373 _qs_142) >>= fun _x_374 ->
        let rec _choose_375 _x_376 =
          match _x_376 with
          | RowsEmpty -> Value SolutionsNil
          | RowsCons (_x_378, _xs'_377) ->
              let _l_379 (_y_383 : bool) =
                if _y_383 then
                  Value (( + ) _x_141) >>= fun _x_384 ->
                  Value (_x_384 1) >>= fun _x_385 ->
                  _place_287 (_x_385, SolutionPlace ((_x_141, _x_378), _qs_142))
                else _choose_375 _xs'_377
              in
              Value (_l_379 true) >>= fun _b_380 ->
              Value (_op_44 (* @ *) (force_unsafe _b_380)) >>= fun _b_381 ->
              Value (_l_379 false) >>= fun _b_382 ->
              _b_381 (force_unsafe _b_382)
        in
        _choose_375 (force_unsafe _x_374)
    in
    _place_287 (1, SolutionEmpty)
  in
  _queens_286 _number_of_queens_272

let queens_all = _queens_all_271

let _queens_one_cps_386 (_number_of_queens_387 : int) =
  Value
    (let rec _queens_521 _number_of_queens_522 =
       let rec _place_534 (_x_536, _qs_535) =
         Value (( > ) _x_536) >>= fun _x_537 ->
         Value (_x_537 _number_of_queens_522) >>= fun _x_538 ->
         if _x_538 then
           (* coer_arrow coer_refl_ty (coer_return coer_refl_ty) *)
             (fun (_ : unit -> solution computation) -> _qs_535)
         else
           Value (_available_90 _number_of_queens_522) >>= fun _x_539 ->
           Value (_x_539 _x_536) >>= fun _x_540 ->
           Value (_x_540 _qs_535) >>= fun _x_541 ->
           let rec _choose_542 _x_543 =
             match _x_543 with
             | RowsEmpty ->
                 fun (_kf_544 : unit -> solution computation) -> _kf_544 ()
             | RowsCons (_x_546, _xs'_545) ->
                 let _l_547 (_y_551 : bool) =
                   if _y_551 then
                     Value (( + ) _x_536) >>= fun _x_552 ->
                     Value (_x_552 1) >>= fun _x_553 ->
                     _place_534
                       (_x_553, SolutionPlace ((_x_536, _x_546), _qs_535))
                   else Value (_choose_542 _xs'_545)
                 in
                 fun (_kf_548 : unit -> solution computation) ->
                   Value (_l_547 true) >>= fun _b_549 ->
                   _b_549 (fun (_ : unit) ->
                       Value (_l_547 false) >>= fun _b_550 -> _b_550 _kf_548)
           in
           _choose_542 _x_541
       in
       _place_534 (1, SolutionEmpty)
     in
     _queens_521 _number_of_queens_387)
  >>= fun _b_519 ->
  (force_unsafe _b_519) (fun (() : unit) ->
      Call
        ( Fail,
          (),
          fun (_y_520 : empty) -> Value (match _y_520 with _ -> assert false) ))

let queens_one_cps x = force_unsafe (_queens_one_cps_386 x)
