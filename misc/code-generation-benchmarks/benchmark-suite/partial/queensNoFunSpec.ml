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
    if _x_141 > _number_of_queens_139 then Value _qs_142
    else
      _choose_116 (_available_90 _number_of_queens_139 _x_141 _qs_142)
      >>= fun _y_145 ->
      _place_140 (_x_141 + 1, SolutionPlace ((_x_141, _y_145), _qs_142))
  in
  _place_140 (1, SolutionEmpty)

let queens = _queens_138

let _queens_one_option_162 (_number_of_queens_163 : int) =
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x_169 : solution) -> Value (Some _x_169));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun _ _l_172 ->
                    Value
                      (match
                         coer_arrow coer_refl_ty force_unsafe _l_172 true
                       with
                      | Some _x_167 -> Some _x_167
                      | None ->
                          coer_arrow coer_refl_ty force_unsafe _l_172 false)
              | Fail -> fun _ _l_173 -> Value None
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_queens_138 _number_of_queens_163))

let queens_one_option = _queens_one_option_162

let _queens_all_257 (_number_of_queens_258 : int) =
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_265 : solution) ->
              Value (SolutionsCons (_x_265, SolutionsNil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun _ _l_268 ->
                    Value
                      (_op_44 (* @ *)
                         (coer_arrow coer_refl_ty force_unsafe _l_268 true)
                         (coer_arrow coer_refl_ty force_unsafe _l_268 false))
              | Fail -> fun _ _l_269 -> Value SolutionsNil
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_queens_138 _number_of_queens_258))

let queens_all = _queens_all_257

let _queens_one_cps_362 (_number_of_queens_363 : int) =
  force_unsafe
    ((handler
        {
          value_clause =
            (fun (_x_491 : solution) ->
              Value
                (coer_arrow coer_refl_ty (coer_return coer_refl_ty)
                   (fun (_ : unit -> solution computation) -> _x_491)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun _ _l_492 ->
                    Value
                      (fun (_kf_493 : unit -> solution computation) ->
                        coer_arrow coer_refl_ty force_unsafe _l_492 true
                          (fun (_ : unit) ->
                            coer_arrow coer_refl_ty force_unsafe _l_492 false
                              _kf_493))
              | Fail ->
                  fun _ _l_496 ->
                    Value
                      (fun (_kf_497 : unit -> solution computation) ->
                        _kf_497 ())
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_queens_138 _number_of_queens_363))
    (fun (() : unit) ->
      Call
        ( Fail,
          (),
          fun (_y_490 : empty) -> Value (match _y_490 with _ -> assert false) ))

let queens_one_cps = _queens_one_cps_362
